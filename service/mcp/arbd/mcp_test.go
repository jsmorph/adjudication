package mcp

import (
	"bytes"
	"context"
	"encoding/json"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"
)

func TestInitializeRejectsMixedPrincipals(t *testing.T) {
	server := testMCPServer()
	req := httptest.NewRequest(http.MethodPost, "/mcp?case_id=case-1&role_id=plaintiff&member_id=C1", bytes.NewReader(initializeRequest(t)))
	rec := httptest.NewRecorder()
	server.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d, want %d", rec.Code, http.StatusOK)
	}
	var got rpcResponse
	if err := json.NewDecoder(rec.Body).Decode(&got); err != nil {
		t.Fatalf("decode response: %v", err)
	}
	if got.Error == nil {
		t.Fatalf("expected initialize error")
	}
}

func TestUnifiedToolNamesForLawyerAndCouncil(t *testing.T) {
	for _, tc := range []struct {
		name  string
		query string
		want  string
	}{
		{name: "lawyer", query: "case_id=case-1&role_id=plaintiff", want: "submit_decision"},
		{name: "council", query: "case_id=case-1&member_id=C1", want: "submit_council_answer"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			server := testMCPServer()
			sessionID := initializeSession(t, server, tc.query)
			req := httptest.NewRequest(http.MethodPost, "/mcp", bytes.NewReader(rpcRequest(t, "tools/list", map[string]any{})))
			req.Header.Set("Mcp-Session-Id", sessionID)
			rec := httptest.NewRecorder()
			server.ServeHTTP(rec, req)
			if rec.Code != http.StatusOK {
				t.Fatalf("status = %d, want %d", rec.Code, http.StatusOK)
			}
			var got struct {
				Result map[string][]map[string]any `json:"result"`
			}
			if err := json.NewDecoder(rec.Body).Decode(&got); err != nil {
				t.Fatalf("decode response: %v", err)
			}
			if !hasTool(got.Result["tools"], "wait_for_opportunity") {
				t.Fatalf("missing wait_for_opportunity: %#v", got.Result["tools"])
			}
			if !hasTool(got.Result["tools"], "get_current_opportunity") {
				t.Fatalf("missing get_current_opportunity: %#v", got.Result["tools"])
			}
			if !hasTool(got.Result["tools"], tc.want) {
				t.Fatalf("missing %s: %#v", tc.want, got.Result["tools"])
			}
		})
	}
}

func TestMCPProcessRejectsInvalidStartup(t *testing.T) {
	err := Run(context.Background(), Options{ListenAddr: freeListenAddr(t)})
	if err == nil || !strings.Contains(err.Error(), "caseapi-base is required") {
		t.Fatalf("missing required-base error: %v", err)
	}

	err = Run(context.Background(), Options{ListenAddr: freeListenAddr(t), CaseAPIBase: "://bad"})
	if err == nil || !strings.Contains(err.Error(), "invalid caseapi-base") {
		t.Fatalf("missing invalid-base error: %v", err)
	}
}

func TestMCPProcessHealthAuthOriginAndSessions(t *testing.T) {
	fake := newFakeAARServer(t, "service-token")
	defer fake.Close()
	proc := startMCPServer(t, Options{
		ListenAddr:     freeListenAddr(t),
		CaseAPIBase:    fake.URL,
		BearerToken:    "mcp-token",
		APIBearerToken: "service-token",
		AllowedOrigins: []string{"https://client.example"},
		SessionTTL:     time.Hour,
	})

	resp := httpGet(t, proc.baseURL+"/health", nil)
	if resp.status != http.StatusNoContent {
		t.Fatalf("/health status = %d, want %d", resp.status, http.StatusNoContent)
	}

	resp = httpPostJSON(t, proc.baseURL+"/mcp?case_id=case-1&role_id=plaintiff", "", "", initializeRequest(t))
	if resp.status != http.StatusUnauthorized {
		t.Fatalf("unauthorized initialize status = %d, want %d", resp.status, http.StatusUnauthorized)
	}

	resp = httpPostJSON(t, proc.baseURL+"/mcp?case_id=case-1&role_id=plaintiff", "mcp-token", "https://bad.example", initializeRequest(t))
	if resp.status != http.StatusForbidden {
		t.Fatalf("bad-origin initialize status = %d, want %d", resp.status, http.StatusForbidden)
	}

	resp = httpGet(t, proc.baseURL+"/mcp", map[string]string{"Authorization": "Bearer mcp-token"})
	if resp.status != http.StatusMethodNotAllowed {
		t.Fatalf("GET /mcp status = %d, want %d", resp.status, http.StatusMethodNotAllowed)
	}

	resp = httpPostJSON(t, proc.baseURL+"/mcp", "mcp-token", "", rpcRequest(t, "tools/list", map[string]any{}))
	if resp.status != http.StatusBadRequest {
		t.Fatalf("tools/list without session status = %d, want %d", resp.status, http.StatusBadRequest)
	}
	got := decodeRPC(t, resp.body)
	if got.Error == nil || got.Error.Code != -32600 {
		t.Fatalf("tools/list without session error = %#v, want -32600", got.Error)
	}

	sessionID := initializeHTTPSession(t, proc.baseURL, "case_id=case-1&role_id=plaintiff", "mcp-token", "https://client.example")
	req, err := http.NewRequest(http.MethodDelete, proc.baseURL+"/mcp", nil)
	if err != nil {
		t.Fatalf("build DELETE: %v", err)
	}
	req.Header.Set("Authorization", "Bearer mcp-token")
	req.Header.Set("Mcp-Session-Id", sessionID)
	delResp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("DELETE session: %v", err)
	}
	_ = delResp.Body.Close()
	if delResp.StatusCode != http.StatusNoContent {
		t.Fatalf("DELETE session status = %d, want %d", delResp.StatusCode, http.StatusNoContent)
	}

	resp = postRPC(t, proc.baseURL, "mcp-token", "", sessionID, "tools/list", map[string]any{})
	if resp.status != http.StatusNotFound {
		t.Fatalf("tools/list after delete status = %d, want %d", resp.status, http.StatusNotFound)
	}
}

func TestMCPProcessLawyerAndObserverAPI(t *testing.T) {
	fake := newFakeAARServer(t, "service-token")
	defer fake.Close()
	proc := startMCPServer(t, Options{
		ListenAddr:     freeListenAddr(t),
		CaseAPIBase:    fake.URL,
		BearerToken:    "mcp-token",
		APIBearerToken: "service-token",
		SessionTTL:     time.Hour,
	})

	plaintiffSession := initializeHTTPSession(t, proc.baseURL, "case_id=case-1&role_id=plaintiff", "mcp-token", "")
	tools := listHTTPTools(t, proc.baseURL, "mcp-token", plaintiffSession)
	for _, name := range []string{"wait_for_opportunity", "get_current_opportunity", "case_status", "get_case_result", "send_work_notes", "submit_evidence", "submit_decision"} {
		if !hasTool(tools, name) {
			t.Fatalf("plaintiff tools missing %s: %#v", name, tools)
		}
	}
	if hasTool(tools, "submit_council_answer") {
		t.Fatalf("plaintiff tools include council answer: %#v", tools)
	}

	tool := callHTTPTool(t, proc.baseURL, "mcp-token", plaintiffSession, waitToolName, map[string]any{"timeout_ms": 5})
	structured := structuredContent(t, tool)
	if structured["state"] != "ready" {
		t.Fatalf("wait state = %#v, want ready; result %#v", structured["state"], structured)
	}
	if structured["after_opportunity_id"] != "opp-plaintiff" {
		t.Fatalf("after_opportunity_id = %#v, want opp-plaintiff", structured["after_opportunity_id"])
	}
	if structured["after_version"] != json.Number("7") {
		t.Fatalf("after_version = %#v, want 7", structured["after_version"])
	}

	tool = callHTTPTool(t, proc.baseURL, "mcp-token", plaintiffSession, "submit_decision", map[string]any{
		"kind":           "tool",
		"tool_name":      "submit_argument",
		"case_id":        "spoofed-case",
		"role_id":        "defendant",
		"opportunity_id": "spoofed-opportunity",
		"payload":        map[string]any{"text": "argument"},
	})
	structured = structuredContent(t, tool)
	if structured["ok"] != true {
		t.Fatalf("submit_decision ok = %#v; result %#v", structured["ok"], structured)
	}
	req := fake.lastToolRequest(t, "submit_decision")
	if req.Body["case_id"] != "case-1" || req.Body["role_id"] != "plaintiff" || req.Body["opportunity_id"] != "opp-plaintiff" {
		t.Fatalf("forwarded lawyer body = %#v", req.Body)
	}
	if req.Authorization != "Bearer service-token" {
		t.Fatalf("forwarded authorization = %q", req.Authorization)
	}
	logs := waitForProcessLog(t, proc, "tool=submit_decision")
	for _, want := range []string{"mcp_session_created", "lawyerapi_wait", "lawyerapi_do", "tool=submit_decision", "http_status=200 ok=true"} {
		if !strings.Contains(logs, want) {
			t.Fatalf("stderr missing %q:\n%s", want, logs)
		}
	}
	for _, forbidden := range []string{"mcp-token", "service-token", "argument"} {
		if strings.Contains(logs, forbidden) {
			t.Fatalf("stderr contains %q:\n%s", forbidden, logs)
		}
	}

	observerSession := initializeHTTPSession(t, proc.baseURL, "case_id=case-1&role_id=observer", "mcp-token", "")
	tools = listHTTPTools(t, proc.baseURL, "mcp-token", observerSession)
	if !hasTool(tools, "case_status") || !hasTool(tools, "get_case_result") || !hasTool(tools, "get_turn") {
		t.Fatalf("observer tools missing read tools: %#v", tools)
	}
	if hasTool(tools, "submit_decision") || hasTool(tools, "submit_evidence") || hasTool(tools, "send_work_notes") {
		t.Fatalf("observer tools include mutating lawyer tools: %#v", tools)
	}

	tool = callHTTPTool(t, proc.baseURL, "mcp-token", observerSession, "case_status", map[string]any{})
	structured = structuredContent(t, tool)
	if structured["role_id"] != "observer" || structured["status"] != "ready" {
		t.Fatalf("observer case_status = %#v", structured)
	}
	tool = callHTTPTool(t, proc.baseURL, "mcp-token", observerSession, "get_case_result", map[string]any{})
	structured = structuredContent(t, tool)
	if structured["status"] != "pending" {
		t.Fatalf("observer get_case_result status = %#v, want pending", structured["status"])
	}
	tool = callHTTPTool(t, proc.baseURL, "mcp-token", observerSession, "get_turn", map[string]any{})
	structured = structuredContent(t, tool)
	if structured["ok"] != true {
		t.Fatalf("observer get_turn ok = %#v; result %#v", structured["ok"], structured)
	}
	req = fake.lastToolRequest(t, "get_turn")
	if _, ok := req.Body["opportunity_id"]; ok {
		t.Fatalf("observer request included opportunity_id: %#v", req.Body)
	}
}

func TestMCPProcessCouncilAPIAndErrorResults(t *testing.T) {
	fake := newFakeAARServer(t, "service-token")
	defer fake.Close()
	proc := startMCPServer(t, Options{
		ListenAddr:     freeListenAddr(t),
		CaseAPIBase:    fake.URL,
		BearerToken:    "mcp-token",
		APIBearerToken: "service-token",
		SessionTTL:     time.Hour,
	})

	sessionID := initializeHTTPSession(t, proc.baseURL, "case_id=case-1&member_id=C1", "mcp-token", "")
	tools := listHTTPTools(t, proc.baseURL, "mcp-token", sessionID)
	if !hasTool(tools, "submit_council_answer") || !hasTool(tools, "read_evidence_range") {
		t.Fatalf("council tools missing expected tools: %#v", tools)
	}
	if hasTool(tools, "submit_decision") || hasTool(tools, "submit_evidence") {
		t.Fatalf("council tools include lawyer tools: %#v", tools)
	}

	tool := callHTTPTool(t, proc.baseURL, "mcp-token", sessionID, waitToolName, map[string]any{"timeout_ms": 5})
	structured := structuredContent(t, tool)
	if structured["state"] != "ready" || structured["after_opportunity_id"] != "opp-C1" {
		t.Fatalf("council wait result = %#v", structured)
	}

	tool = callHTTPTool(t, proc.baseURL, "mcp-token", sessionID, "submit_council_answer", map[string]any{
		"answer":    72,
		"rationale": "rationale",
		"member_id": "spoofed-member",
	})
	structured = structuredContent(t, tool)
	if structured["ok"] != true {
		t.Fatalf("submit_council_answer ok = %#v; result %#v", structured["ok"], structured)
	}
	req := fake.lastToolRequest(t, "submit_council_answer")
	if req.Body["case_id"] != "case-1" || req.Body["member_id"] != "C1" || req.Body["opportunity_id"] != "opp-C1" {
		t.Fatalf("forwarded council body = %#v", req.Body)
	}

	tool = callHTTPTool(t, proc.baseURL, "mcp-token", sessionID, "force_ok_false", map[string]any{})
	structured = structuredContent(t, tool)
	if structured["ok"] != false {
		t.Fatalf("ok:false structured content = %#v", structured)
	}
	if tool["isError"] != true {
		t.Fatalf("ok:false isError = %#v, want true", tool["isError"])
	}

	tool = callHTTPTool(t, proc.baseURL, "mcp-token", sessionID, "force_non_2xx", map[string]any{})
	structured = structuredContent(t, tool)
	if structured["ok"] != false || structured["http_status"] != json.Number("409") {
		t.Fatalf("non-2xx structured content = %#v", structured)
	}
	if tool["isError"] != true {
		t.Fatalf("non-2xx isError = %#v, want true", tool["isError"])
	}
}

func TestToolResultTextIncludesNestedResult(t *testing.T) {
	text := toolResultText(map[string]any{
		"ok":        true,
		"case_id":   "case-1",
		"member_id": "C1",
		"result": map[string]any{
			"evidence": []any{
				map[string]any{
					"evidence_id": "ev_123",
					"title":       "record.txt",
				},
			},
		},
		"turn": map[string]any{
			"opportunity_id":     "deliberation:1:C1",
			"remaining_ms":       json.Number("60000"),
			"attempts_remaining": json.Number("3"),
		},
	})
	for _, want := range []string{"ok: true", "case_id: case-1", "json:", `"evidence_id":"ev_123"`} {
		if !strings.Contains(text, want) {
			t.Fatalf("tool result text missing %q:\n%s", want, text)
		}
	}
}

func TestMCPProcessWaitStateNormalization(t *testing.T) {
	fake := newFakeAARServer(t, "service-token")
	defer fake.Close()
	proc := startMCPServer(t, Options{
		ListenAddr:     freeListenAddr(t),
		CaseAPIBase:    fake.URL,
		BearerToken:    "mcp-token",
		APIBearerToken: "service-token",
		SessionTTL:     time.Hour,
	})

	for _, tc := range []struct {
		caseID    string
		wantState string
	}{
		{caseID: "case-waiting", wantState: "waiting"},
		{caseID: "case-done", wantState: "done"},
		{caseID: "case-failed", wantState: "failed"},
		{caseID: "case-error", wantState: "error"},
	} {
		t.Run(tc.caseID, func(t *testing.T) {
			sessionID := initializeHTTPSession(t, proc.baseURL, "case_id="+tc.caseID+"&role_id=plaintiff", "mcp-token", "")
			tool := callHTTPTool(t, proc.baseURL, "mcp-token", sessionID, waitToolName, map[string]any{"timeout_ms": 5})
			structured := structuredContent(t, tool)
			if structured["state"] != tc.wantState {
				t.Fatalf("state = %#v, want %s; result %#v", structured["state"], tc.wantState, structured)
			}
			if structured["after_version"] != json.Number("7") {
				t.Fatalf("after_version = %#v, want 7; result %#v", structured["after_version"], structured)
			}
		})
	}
}

func TestIdleSessionExpiry(t *testing.T) {
	server := testMCPServer()
	server.sessionTTL = time.Minute
	old := &mcpSession{ID: "old", CaseID: "case-1", AssignmentType: "lawyer", RoleID: "plaintiff", LastSeen: time.Now().Add(-2 * time.Minute)}
	current := &mcpSession{ID: "current", CaseID: "case-1", AssignmentType: "lawyer", RoleID: "defendant", LastSeen: time.Now()}
	server.sessions[old.ID] = old
	server.sessions[current.ID] = current

	n := server.expireIdleSessions(time.Now())
	if n != 1 {
		t.Fatalf("expired sessions = %d, want 1", n)
	}
	if _, ok := server.sessions[old.ID]; ok {
		t.Fatalf("old session remained after expiry")
	}
	if _, ok := server.sessions[current.ID]; !ok {
		t.Fatalf("current session was removed")
	}
}

func testMCPServer() *mcpServer {
	return &mcpServer{
		caseAPIBase: "http://127.0.0.1:1",
		sessions:    map[string]*mcpSession{},
	}
}

func initializeSession(t *testing.T, server *mcpServer, query string) string {
	t.Helper()
	req := httptest.NewRequest(http.MethodPost, "/mcp?"+query, bytes.NewReader(initializeRequest(t)))
	rec := httptest.NewRecorder()
	server.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d, want %d", rec.Code, http.StatusOK)
	}
	sessionID := rec.Header().Get("Mcp-Session-Id")
	if sessionID == "" {
		t.Fatalf("missing session id")
	}
	return sessionID
}

func initializeRequest(t *testing.T) []byte {
	t.Helper()
	return rpcRequest(t, "initialize", map[string]any{
		"protocolVersion": mcpProtocolVersion,
		"capabilities":    map[string]any{},
		"clientInfo":      map[string]any{"name": "test", "version": "0"},
	})
}

func rpcRequest(t *testing.T, method string, params map[string]any) []byte {
	t.Helper()
	raw, err := json.Marshal(map[string]any{
		"jsonrpc": "2.0",
		"id":      1,
		"method":  method,
		"params":  params,
	})
	if err != nil {
		t.Fatalf("marshal request: %v", err)
	}
	return raw
}

func hasTool(tools []map[string]any, name string) bool {
	for _, tool := range tools {
		if tool["name"] == name {
			return true
		}
	}
	return false
}

type mcpProcess struct {
	baseURL string
	cancel  context.CancelFunc
	done    chan error
	log     *safeBuffer
}

func startMCPServer(t *testing.T, opts Options) *mcpProcess {
	t.Helper()
	if strings.TrimSpace(opts.ListenAddr) == "" {
		opts.ListenAddr = freeListenAddr(t)
	}
	ctx, cancel := context.WithCancel(context.Background())
	log := &safeBuffer{}
	opts.Log = log
	proc := &mcpProcess{
		baseURL: "http://" + opts.ListenAddr,
		cancel:  cancel,
		done:    make(chan error, 1),
		log:     log,
	}
	go func() {
		proc.done <- Run(ctx, opts)
	}()
	waitForHealth(t, proc)
	t.Cleanup(func() {
		proc.cancel()
		select {
		case err := <-proc.done:
			if err != nil {
				t.Fatalf("mcp server returned after cancellation: %v\nlog:\n%s", err, proc.log.String())
			}
		case <-time.After(5 * time.Second):
			t.Fatalf("mcp server did not exit after cancellation; log:\n%s", proc.log.String())
		}
	})
	return proc
}

type safeBuffer struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (b *safeBuffer) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.Write(p)
}

func (b *safeBuffer) String() string {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.String()
}

func waitForHealth(t *testing.T, proc *mcpProcess) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		select {
		case err := <-proc.done:
			t.Fatalf("mcp server exited before health check: %v\nlog:\n%s", err, proc.log.String())
		default:
		}
		resp, err := http.Get(proc.baseURL + "/health")
		if err == nil {
			_ = resp.Body.Close()
			if resp.StatusCode == http.StatusNoContent {
				return
			}
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatalf("mcp server did not become healthy; log:\n%s", proc.log.String())
}

func waitForProcessLog(t *testing.T, proc *mcpProcess, text string) string {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		logs := proc.log.String()
		if strings.Contains(logs, text) {
			return logs
		}
		select {
		case err := <-proc.done:
			t.Fatalf("mcp server exited while waiting for log %q: %v\nlog:\n%s", text, err, logs)
		default:
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatalf("log missing %q:\n%s", text, proc.log.String())
	return ""
}

type httpResponse struct {
	status int
	header http.Header
	body   []byte
}

func httpGet(t *testing.T, rawURL string, headers map[string]string) httpResponse {
	t.Helper()
	req, err := http.NewRequest(http.MethodGet, rawURL, nil)
	if err != nil {
		t.Fatalf("build GET %s: %v", rawURL, err)
	}
	for key, value := range headers {
		req.Header.Set(key, value)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("GET %s: %v", rawURL, err)
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read GET %s: %v", rawURL, err)
	}
	return httpResponse{status: resp.StatusCode, header: resp.Header.Clone(), body: body}
}

func httpPostJSON(t *testing.T, rawURL string, token string, origin string, body []byte) httpResponse {
	t.Helper()
	req, err := http.NewRequest(http.MethodPost, rawURL, bytes.NewReader(body))
	if err != nil {
		t.Fatalf("build POST %s: %v", rawURL, err)
	}
	req.Header.Set("Content-Type", "application/json")
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	if origin != "" {
		req.Header.Set("Origin", origin)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("POST %s: %v", rawURL, err)
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read POST %s: %v", rawURL, err)
	}
	return httpResponse{status: resp.StatusCode, header: resp.Header.Clone(), body: raw}
}

func postRPC(t *testing.T, baseURL string, token string, origin string, sessionID string, method string, params map[string]any) httpResponse {
	t.Helper()
	body := rpcRequest(t, method, params)
	req, err := http.NewRequest(http.MethodPost, baseURL+"/mcp", bytes.NewReader(body))
	if err != nil {
		t.Fatalf("build RPC %s: %v", method, err)
	}
	req.Header.Set("Content-Type", "application/json")
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	if origin != "" {
		req.Header.Set("Origin", origin)
	}
	if sessionID != "" {
		req.Header.Set("Mcp-Session-Id", sessionID)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("RPC %s: %v", method, err)
	}
	defer resp.Body.Close()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read RPC %s: %v", method, err)
	}
	return httpResponse{status: resp.StatusCode, header: resp.Header.Clone(), body: raw}
}

func initializeHTTPSession(t *testing.T, baseURL string, query string, token string, origin string) string {
	t.Helper()
	resp := httpPostJSON(t, baseURL+"/mcp?"+query, token, origin, initializeRequest(t))
	if resp.status != http.StatusOK {
		t.Fatalf("initialize status = %d, want %d; body:\n%s", resp.status, http.StatusOK, string(resp.body))
	}
	sessionID := resp.header.Get("Mcp-Session-Id")
	if sessionID == "" {
		t.Fatalf("initialize missing Mcp-Session-Id; body:\n%s", string(resp.body))
	}
	got := decodeRPC(t, resp.body)
	if got.Error != nil {
		t.Fatalf("initialize error = %#v", got.Error)
	}
	result := resultMap(t, got)
	if result["protocolVersion"] != mcpProtocolVersion {
		t.Fatalf("protocolVersion = %#v, want %s", result["protocolVersion"], mcpProtocolVersion)
	}
	return sessionID
}

func listHTTPTools(t *testing.T, baseURL string, token string, sessionID string) []map[string]any {
	t.Helper()
	resp := postRPC(t, baseURL, token, "", sessionID, "tools/list", map[string]any{})
	if resp.status != http.StatusOK {
		t.Fatalf("tools/list status = %d, want %d; body:\n%s", resp.status, http.StatusOK, string(resp.body))
	}
	got := decodeRPC(t, resp.body)
	if got.Error != nil {
		t.Fatalf("tools/list error = %#v", got.Error)
	}
	result := resultMap(t, got)
	rawTools, ok := result["tools"].([]any)
	if !ok {
		t.Fatalf("tools result = %#v", result)
	}
	tools := make([]map[string]any, 0, len(rawTools))
	for _, raw := range rawTools {
		tool, ok := raw.(map[string]any)
		if !ok {
			t.Fatalf("tool entry = %#v", raw)
		}
		tools = append(tools, tool)
	}
	return tools
}

func callHTTPTool(t *testing.T, baseURL string, token string, sessionID string, name string, arguments map[string]any) map[string]any {
	t.Helper()
	resp := postRPC(t, baseURL, token, "", sessionID, "tools/call", map[string]any{
		"name":      name,
		"arguments": arguments,
	})
	if resp.status != http.StatusOK {
		t.Fatalf("tools/call %s status = %d, want %d; body:\n%s", name, resp.status, http.StatusOK, string(resp.body))
	}
	got := decodeRPC(t, resp.body)
	if got.Error != nil {
		t.Fatalf("tools/call %s error = %#v", name, got.Error)
	}
	return resultMap(t, got)
}

func decodeRPC(t *testing.T, raw []byte) rpcResponse {
	t.Helper()
	var got rpcResponse
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	if err := dec.Decode(&got); err != nil {
		t.Fatalf("decode RPC response %q: %v", string(raw), err)
	}
	return got
}

func resultMap(t *testing.T, got rpcResponse) map[string]any {
	t.Helper()
	result, ok := got.Result.(map[string]any)
	if !ok {
		t.Fatalf("RPC result = %#v", got.Result)
	}
	return result
}

func structuredContent(t *testing.T, toolResult map[string]any) map[string]any {
	t.Helper()
	structured, ok := toolResult["structuredContent"].(map[string]any)
	if !ok {
		t.Fatalf("tool result missing structuredContent: %#v", toolResult)
	}
	return structured
}

func freeListenAddr(t *testing.T) string {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("allocate listen address: %v", err)
	}
	addr := ln.Addr().String()
	if err := ln.Close(); err != nil {
		t.Fatalf("close listen socket: %v", err)
	}
	return addr
}

type fakeAARServer struct {
	*httptest.Server
	t          *testing.T
	apiToken   string
	mu         sync.Mutex
	toolCalls  []fakeAARToolRequest
	pathCounts map[string]int
}

type fakeAARToolRequest struct {
	Path          string
	Authorization string
	Body          map[string]any
}

func newFakeAARServer(t *testing.T, apiToken string) *fakeAARServer {
	t.Helper()
	fake := &fakeAARServer{t: t, apiToken: apiToken, pathCounts: map[string]int{}}
	fake.Server = httptest.NewServer(http.HandlerFunc(fake.handle))
	return fake
}

func (f *fakeAARServer) handle(w http.ResponseWriter, r *http.Request) {
	f.mu.Lock()
	f.pathCounts[r.URL.Path]++
	f.mu.Unlock()
	if f.apiToken != "" && r.Header.Get("Authorization") != "Bearer "+f.apiToken {
		writeFakeJSON(w, http.StatusUnauthorized, map[string]any{"ok": false, "error": map[string]any{"code": "unauthorized", "message": "unauthorized"}})
		return
	}
	switch {
	case strings.HasSuffix(r.URL.Path, "/get") && r.Method == http.MethodGet:
		f.handleGet(w, r)
	case strings.HasSuffix(r.URL.Path, "/wait") && r.Method == http.MethodGet:
		f.handleWait(w, r)
	case strings.HasSuffix(r.URL.Path, "/status") && r.Method == http.MethodGet:
		writeFakeJSON(w, http.StatusOK, map[string]any{"ok": true, "status": "ready", "case_id": r.URL.Query().Get("case_id"), "role_id": r.URL.Query().Get("role_id")})
	case strings.HasSuffix(r.URL.Path, "/result") && r.Method == http.MethodGet:
		writeFakeJSON(w, http.StatusOK, map[string]any{"ok": true, "status": "pending", "case_id": r.URL.Query().Get("case_id")})
	case strings.HasSuffix(r.URL.Path, "/do") && r.Method == http.MethodPost:
		f.handleDo(w, r)
	default:
		writeFakeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "error": map[string]any{"code": "not_found", "message": r.URL.Path}})
	}
}

func (f *fakeAARServer) handleGet(w http.ResponseWriter, r *http.Request) {
	query := r.URL.Query()
	caseID := query.Get("case_id")
	if memberID := query.Get("member_id"); memberID != "" {
		writeFakeJSON(w, http.StatusOK, readyResponse(caseID, "council", memberID, "opp-"+memberID))
		return
	}
	roleID := query.Get("role_id")
	writeFakeJSON(w, http.StatusOK, readyResponse(caseID, roleID, "", "opp-"+roleID))
}

func (f *fakeAARServer) handleWait(w http.ResponseWriter, r *http.Request) {
	query := r.URL.Query()
	caseID := query.Get("case_id")
	switch caseID {
	case "case-waiting":
		writeFakeJSON(w, http.StatusOK, map[string]any{"ok": true, "status": "waiting", "case_id": caseID, "wait": map[string]any{"version": 7, "reason": "timeout"}})
		return
	case "case-done":
		writeFakeJSON(w, http.StatusOK, map[string]any{"ok": true, "status": "done", "case_id": caseID, "wait": map[string]any{"version": 7, "reason": "done"}})
		return
	case "case-failed":
		writeFakeJSON(w, http.StatusOK, map[string]any{"ok": true, "status": "failed", "case_id": caseID, "wait": map[string]any{"version": 7, "reason": "failed"}})
		return
	case "case-error":
		writeFakeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "status": "waiting", "case_id": caseID, "wait": map[string]any{"version": 7, "reason": "upstream_error"}, "error": map[string]any{"code": "upstream_error", "message": "upstream error"}})
		return
	}
	if memberID := query.Get("member_id"); memberID != "" {
		resp := readyResponse(caseID, "council", memberID, "opp-"+memberID)
		resp["wait"] = map[string]any{"version": 7, "reason": "state_changed"}
		writeFakeJSON(w, http.StatusOK, resp)
		return
	}
	roleID := query.Get("role_id")
	resp := readyResponse(caseID, roleID, "", "opp-"+roleID)
	resp["wait"] = map[string]any{"version": 7, "reason": "state_changed"}
	writeFakeJSON(w, http.StatusOK, resp)
}

func (f *fakeAARServer) handleDo(w http.ResponseWriter, r *http.Request) {
	var body map[string]any
	dec := json.NewDecoder(r.Body)
	dec.UseNumber()
	if err := dec.Decode(&body); err != nil {
		writeFakeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": map[string]any{"code": "bad_json", "message": err.Error()}})
		return
	}
	req := fakeAARToolRequest{Path: r.URL.Path, Authorization: r.Header.Get("Authorization"), Body: body}
	f.mu.Lock()
	f.toolCalls = append(f.toolCalls, req)
	f.mu.Unlock()
	if body["tool"] == "force_non_2xx" {
		writeFakeJSON(w, http.StatusConflict, map[string]any{"error": map[string]any{"code": "forced_conflict", "message": "forced conflict"}})
		return
	}
	if body["tool"] == "force_ok_false" {
		writeFakeJSON(w, http.StatusOK, map[string]any{"ok": false, "error": map[string]any{"code": "forced_rejection", "message": "forced rejection"}})
		return
	}
	writeFakeJSON(w, http.StatusOK, map[string]any{"ok": true, "status": "accepted", "tool": body["tool"], "case_id": body["case_id"], "role_id": body["role_id"], "member_id": body["member_id"]})
}

func (f *fakeAARServer) lastToolRequest(t *testing.T, tool string) fakeAARToolRequest {
	t.Helper()
	f.mu.Lock()
	defer f.mu.Unlock()
	for i := len(f.toolCalls) - 1; i >= 0; i-- {
		if f.toolCalls[i].Body["tool"] == tool {
			return f.toolCalls[i]
		}
	}
	t.Fatalf("missing forwarded tool request %s; requests: %#v", tool, f.toolCalls)
	return fakeAARToolRequest{}
}

func readyResponse(caseID string, roleID string, memberID string, opportunityID string) map[string]any {
	turn := map[string]any{
		"phase":              "arguments",
		"opportunity_id":     opportunityID,
		"remaining_ms":       60000,
		"attempts_remaining": 3,
	}
	if memberID != "" {
		turn["member_id"] = memberID
	} else {
		turn["role_id"] = roleID
	}
	return map[string]any{
		"ok":        true,
		"status":    "ready",
		"case_id":   caseID,
		"role_id":   roleID,
		"member_id": memberID,
		"prompt":    "test prompt",
		"turn":      turn,
		"limits":    map[string]any{"max_attempts": 3},
		"tools":     []any{},
	}
}

func writeFakeJSON(w http.ResponseWriter, status int, value map[string]any) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(value)
}
