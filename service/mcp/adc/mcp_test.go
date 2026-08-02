package mcp

import (
	"bytes"
	"encoding/json"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func TestInitializeToolsAndRoleAPIForwarding(t *testing.T) {
	var forwarded map[string]any
	fakeCaseAPI := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("Authorization") != "Bearer service-token" {
			t.Fatalf("authorization = %q", r.Header.Get("Authorization"))
		}
		switch r.URL.Path {
		case "/roleapi/v1/get", "/roleapi/v1/wait_for_opportunity":
			writeTestJSON(w, map[string]any{
				"ok":      true,
				"status":  "active",
				"case_id": "case-1",
				"opportunity": map[string]any{
					"opportunity_id":      "opp-1",
					"phase":               "deliberation",
					"kind":                "juror_vote",
					"remaining_time_ms":   1000,
					"attempts_remaining":  3,
					"allowed_legal_tools": []string{"record_verdict"},
				},
			})
		case "/roleapi/v1/do":
			if err := json.NewDecoder(r.Body).Decode(&forwarded); err != nil {
				t.Fatalf("decode forwarded request: %v", err)
			}
			writeTestJSON(w, map[string]any{"ok": true, "status": "active", "case_id": forwarded["case_id"]})
		default:
			t.Fatalf("unexpected path %s", r.URL.Path)
		}
	}))
	defer fakeCaseAPI.Close()

	server := testServer(fakeCaseAPI.URL)
	sessionID := initializeTestSession(t, server, "case_id=case-1&role_id=juror&principal_id=J1")
	tools := listTestTools(t, server, sessionID)
	for _, name := range []string{"wait_for_opportunity", "get_current_opportunity", "get_case_result", "send_work_notes", "submit_decision", "get_juror_context"} {
		if !hasTool(tools, name) {
			t.Fatalf("missing tool %s: %#v", name, tools)
		}
	}

	wait := callTestTool(t, server, sessionID, "wait_for_opportunity", map[string]any{"timeout_ms": 5})
	waitContent := structuredContent(t, wait)
	if waitContent["state"] != "ready" || waitContent["after_opportunity_id"] != "opp-1" {
		t.Fatalf("wait content = %#v", waitContent)
	}

	result := callTestTool(t, server, sessionID, "submit_decision", map[string]any{
		"kind":      "tool",
		"tool_name": "record_verdict",
		"payload":   map[string]any{"verdict": "liable"},
		"case_id":   "spoofed-case",
		"role_id":   "plaintiff",
	})
	resultContent := structuredContent(t, result)
	if resultContent["ok"] != true {
		t.Fatalf("submit result = %#v", resultContent)
	}
	if forwarded["case_id"] != "case-1" || forwarded["role_id"] != "juror" || forwarded["principal_id"] != "J1" || forwarded["opportunity_id"] != "opp-1" {
		t.Fatalf("forwarded body = %#v", forwarded)
	}
	if forwarded["tool"] != "submit_decision" {
		t.Fatalf("forwarded tool = %#v", forwarded["tool"])
	}
}

func TestObserverToolsAreReadOnly(t *testing.T) {
	server := testServer("http://127.0.0.1:1")
	sessionID := initializeTestSession(t, server, "case_id=case-1&role_id=observer")
	tools := listTestTools(t, server, sessionID)
	for _, name := range []string{"wait_for_opportunity", "case_status", "get_case_result"} {
		if !hasTool(tools, name) {
			t.Fatalf("missing observer tool %s: %#v", name, tools)
		}
	}
	for _, name := range []string{"send_work_notes", "submit_decision", "read_case_file_bytes"} {
		if hasTool(tools, name) {
			t.Fatalf("observer received mutating or role-specific tool %s: %#v", name, tools)
		}
	}
}

func TestObserverCannotCallUnlistedTool(t *testing.T) {
	caseAPICalls := 0
	fakeCaseAPI := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		caseAPICalls++
		writeTestJSON(w, map[string]any{"ok": true})
	}))
	defer fakeCaseAPI.Close()

	server := testServer(fakeCaseAPI.URL)
	sessionID := initializeTestSession(t, server, "case_id=case-1&role_id=observer")
	result := callTestTool(t, server, sessionID, "submit_decision", map[string]any{
		"kind":   "pass",
		"reason": "observer should not be able to act",
	})
	content := structuredContent(t, result)
	if content["ok"] != false || content["status"] != "forbidden" {
		t.Fatalf("observer unlisted tool content = %#v", content)
	}
	if isError, _ := result["isError"].(bool); !isError {
		t.Fatalf("observer unlisted tool result isError = %#v", result["isError"])
	}
	if caseAPICalls != 0 {
		t.Fatalf("observer unlisted tool reached Role API %d times", caseAPICalls)
	}
}

func TestInitializeRejectsWrongPrincipalUse(t *testing.T) {
	server := testServer("http://127.0.0.1:1")
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/mcp?case_id=case-1&role_id=plaintiff&principal_id=J1", bytes.NewReader(testRPCRequest(t, "initialize", map[string]any{})))
	server.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("status = %d, want %d", rec.Code, http.StatusOK)
	}
	resp := decodeTestRPC(t, rec.Body)
	if resp.Error == nil || !strings.Contains(resp.Error.Message, "principal_id is only allowed") {
		t.Fatalf("error = %#v", resp.Error)
	}
}

func testServer(caseAPIBase string) *server {
	return &server{
		caseAPIBase:    caseAPIBase,
		bearerToken:    "",
		apiBearerToken: "service-token",
		client:         &http.Client{Timeout: time.Second},
		log:            io.Discard,
		sessionTTL:     time.Hour,
		sessions:       map[string]*session{},
	}
}

func initializeTestSession(t *testing.T, server *server, query string) string {
	t.Helper()
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/mcp?"+query, bytes.NewReader(testRPCRequest(t, "initialize", map[string]any{})))
	server.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("initialize status = %d", rec.Code)
	}
	resp := decodeTestRPC(t, rec.Body)
	if resp.Error != nil {
		t.Fatalf("initialize error = %#v", resp.Error)
	}
	sessionID := rec.Header().Get("Mcp-Session-Id")
	if sessionID == "" {
		t.Fatalf("missing Mcp-Session-Id")
	}
	return sessionID
}

func listTestTools(t *testing.T, server *server, sessionID string) []map[string]any {
	t.Helper()
	resp := rpcPost(t, server, sessionID, "tools/list", map[string]any{})
	result, ok := resp.Result.(map[string]any)
	if !ok {
		t.Fatalf("result = %#v", resp.Result)
	}
	rawTools, ok := result["tools"].([]any)
	if !ok {
		t.Fatalf("tools = %#v", result["tools"])
	}
	tools := make([]map[string]any, 0, len(rawTools))
	for _, raw := range rawTools {
		tool, ok := raw.(map[string]any)
		if !ok {
			t.Fatalf("tool = %#v", raw)
		}
		tools = append(tools, tool)
	}
	return tools
}

func callTestTool(t *testing.T, server *server, sessionID string, name string, args map[string]any) map[string]any {
	t.Helper()
	resp := rpcPost(t, server, sessionID, "tools/call", map[string]any{"name": name, "arguments": args})
	if resp.Error != nil {
		t.Fatalf("tool error = %#v", resp.Error)
	}
	result, ok := resp.Result.(map[string]any)
	if !ok {
		t.Fatalf("tool result = %#v", resp.Result)
	}
	return result
}

func rpcPost(t *testing.T, server *server, sessionID string, method string, params map[string]any) rpcResponse {
	t.Helper()
	rec := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodPost, "/mcp", bytes.NewReader(testRPCRequest(t, method, params)))
	req.Header.Set("Mcp-Session-Id", sessionID)
	server.ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("%s status = %d; body=%s", method, rec.Code, rec.Body.String())
	}
	return decodeTestRPC(t, rec.Body)
}

func testRPCRequest(t *testing.T, method string, params map[string]any) []byte {
	t.Helper()
	raw, err := json.Marshal(map[string]any{"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
	if err != nil {
		t.Fatalf("marshal request: %v", err)
	}
	return raw
}

func decodeTestRPC(t *testing.T, r io.Reader) rpcResponse {
	t.Helper()
	var resp rpcResponse
	dec := json.NewDecoder(r)
	dec.UseNumber()
	if err := dec.Decode(&resp); err != nil {
		t.Fatalf("decode rpc response: %v", err)
	}
	return resp
}

func structuredContent(t *testing.T, result map[string]any) map[string]any {
	t.Helper()
	content, ok := result["structuredContent"].(map[string]any)
	if !ok {
		t.Fatalf("structuredContent = %#v", result["structuredContent"])
	}
	return content
}

func hasTool(tools []map[string]any, name string) bool {
	for _, tool := range tools {
		if tool["name"] == name {
			return true
		}
	}
	return false
}

func writeTestJSON(w http.ResponseWriter, value map[string]any) {
	w.Header().Set("Content-Type", "application/json")
	_ = json.NewEncoder(w).Encode(value)
}
