package compat

import (
	"bytes"
	"context"
	"encoding/json"
	"io"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

type mcpServiceProcess struct {
	*testProcess
	baseURL string
	token   string
}

func TestBlackBoxMCPThroughService(t *testing.T) {
	fx := newBlackBoxFixture(t)
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()

	svc := fx.startService(ctx, t)
	defer svc.kill(t)

	mcp := fx.startMCP(ctx, t, svc)
	defer mcp.kill(t)

	caseID := "bb-mcp-service"
	outDir := svc.outputDir("mcp-service-case")
	caseFile := filepath.Join(fx.dir, "case", "source.txt")
	mustWriteFile(t, caseFile, "Initial case-packet source text for MCP evidence reading.\n")
	createCase(ctx, t, svc.baseURL, map[string]any{
		"case_id":                 caseID,
		"run_id":                  "run-" + caseID,
		"complaint_path":          fx.complaintPath,
		"case_files":              []string{caseFile},
		"out_dir":                 outDir,
		"policy_path":             fx.policyPath,
		"council_pool_path":       fx.councilPoolPath,
		"common_root":             fx.commonRoot,
		"engine_path":             fx.enginePath,
		"council_backend":         "councilapi",
		"invalid_attempt_limit":   2,
		"lawyer_timeout_seconds":  30,
		"council_timeout_seconds": 30,
	})

	plaintiff := mcpInitialize(ctx, t, mcp, "case_id="+url.QueryEscape(caseID)+"&role_id=plaintiff")
	defendant := mcpInitialize(ctx, t, mcp, "case_id="+url.QueryEscape(caseID)+"&role_id=defendant")
	observer := mcpInitialize(ctx, t, mcp, "case_id="+url.QueryEscape(caseID)+"&role_id=observer")

	plaintiffTools := mcpListTools(ctx, t, mcp, plaintiff)
	for _, name := range []string{"wait_for_opportunity", "get_current_opportunity", "send_work_notes", "list_evidence", "read_evidence_range", "submit_decision"} {
		if !mcpHasTool(plaintiffTools, name) {
			t.Fatalf("plaintiff MCP tools missing %s: %#v", name, plaintiffTools)
		}
	}

	observerTools := mcpListTools(ctx, t, mcp, observer)
	if !mcpHasTool(observerTools, "get_turn") || !mcpHasTool(observerTools, "get_case_result") {
		t.Fatalf("observer MCP tools missing read tools: %#v", observerTools)
	}
	if mcpHasTool(observerTools, "submit_decision") || mcpHasTool(observerTools, "submit_council_answer") {
		t.Fatalf("observer MCP tools include mutating tools: %#v", observerTools)
	}
	rejected := mcpCall(ctx, t, mcp, observer, "submit_decision", map[string]any{"kind": "pass"})
	if rejected["isError"] != true || boolAt(mcpStructured(t, rejected), "ok") {
		t.Fatalf("observer mutating call was not rejected: %#v", rejected)
	}

	mcpWaitReady(ctx, t, mcp, plaintiff)
	mcpCallOK(ctx, t, mcp, plaintiff, "send_work_notes", map[string]any{"notes": "MCP plaintiff work notes before opening."})
	evidenceID := firstEvidenceID(t, mcpCallOK(ctx, t, mcp, plaintiff, "list_evidence", map[string]any{}))
	mcpCallOK(ctx, t, mcp, plaintiff, "read_evidence_range", map[string]any{"evidence_id": evidenceID, "offset": 0, "length": 24})

	mcpSubmitDecision(ctx, t, mcp, plaintiff, "record_opening_statement", map[string]any{"text": "Plaintiff opening through MCP."})
	mcpSubmitDecision(ctx, t, mcp, defendant, "record_opening_statement", map[string]any{"text": "Defendant opening through MCP."})
	mcpSubmitDecision(ctx, t, mcp, plaintiff, "submit_argument", map[string]any{"text": "Plaintiff argument through MCP.", "offered_evidence": []any{}, "technical_reports": []any{}})
	mcpSubmitDecision(ctx, t, mcp, defendant, "submit_argument", map[string]any{"text": "Defendant argument through MCP.", "offered_evidence": []any{}, "technical_reports": []any{}})
	mcpSubmitPass(ctx, t, mcp, plaintiff)
	mcpSubmitPass(ctx, t, mcp, defendant)
	mcpSubmitDecision(ctx, t, mcp, plaintiff, "deliver_closing_statement", map[string]any{"text": "Plaintiff closing through MCP."})
	mcpSubmitDecision(ctx, t, mcp, defendant, "deliver_closing_statement", map[string]any{"text": "Defendant closing through MCP."})

	c1 := mcpInitialize(ctx, t, mcp, "case_id="+url.QueryEscape(caseID)+"&member_id=C1")
	c2 := mcpInitialize(ctx, t, mcp, "case_id="+url.QueryEscape(caseID)+"&member_id=C2")
	c3 := mcpInitialize(ctx, t, mcp, "case_id="+url.QueryEscape(caseID)+"&member_id=C3")
	councilTools := mcpListTools(ctx, t, mcp, c1)
	if !mcpHasTool(councilTools, "submit_council_answer") || mcpHasTool(councilTools, "submit_decision") {
		t.Fatalf("council MCP tools wrong: %#v", councilTools)
	}
	mcpWaitReady(ctx, t, mcp, c1)
	mcpCallOK(ctx, t, mcp, c1, "list_evidence", map[string]any{})
	mcpCallOK(ctx, t, mcp, c1, "read_evidence_range", map[string]any{"evidence_id": evidenceID, "offset": 0, "length": 24})
	mcpCallOK(ctx, t, mcp, c1, "submit_council_answer", map[string]any{"answer": 72, "rationale": "The record supports the question."})
	mcpWaitReady(ctx, t, mcp, c2)
	mcpCallOK(ctx, t, mcp, c2, "submit_council_answer", map[string]any{"answer": 72, "rationale": "The record supports the question."})
	mcpWaitReady(ctx, t, mcp, c3)
	mcpCallOK(ctx, t, mcp, c3, "submit_council_answer", map[string]any{"answer": 72, "rationale": "The record supports the question."})

	result := pollResultStatus(ctx, t, svc.baseURL, caseID, "done")
	answers := mapAny(mapAny(result["result"])["answers"])
	if intValue(answers["C1"]) != 72 || intValue(answers["C2"]) != 72 || intValue(answers["C3"]) != 72 {
		t.Fatalf("answers = %#v, want all council answers", answers)
	}

	finalByMCP := mcpStructured(t, mcpCall(ctx, t, mcp, observer, "get_case_result", map[string]any{}))
	assertString(t, finalByMCP, "status", "done")
	finalAnswers := mapAny(mapAny(finalByMCP["result"])["answers"])
	if intValue(finalAnswers["C1"]) != 72 || intValue(finalAnswers["C2"]) != 72 || intValue(finalAnswers["C3"]) != 72 {
		t.Fatalf("final answers = %#v, want all council answers", finalAnswers)
	}

	record := pollCaseRecordStatus(ctx, t, svc.baseURL, caseID, "completed")
	assertServiceRecord(t, record, "completed", "ok")
	run := readJSONFile(t, filepath.Join(outDir, "run.json"))
	assertString(t, run, "status", "ok")
	caseObj := mapAny(mapAny(run["final_state"])["case"])
	if len(listOfMaps(caseObj["council_answers"])) < 2 {
		t.Fatalf("final_state council_answers = %#v, want at least two answers", caseObj["council_answers"])
	}
	workNotes := readTextFile(t, filepath.Join(outDir, "work-notes.ndjson"))
	if !strings.Contains(workNotes, "MCP plaintiff work notes before opening.") {
		t.Fatalf("work notes missing MCP note:\n%s", workNotes)
	}
	assertEventTypes(t, filepath.Join(outDir, "events.ndjson"), "evidence_read", "council_answer")
}

func (fx *blackBoxFixture) startMCP(ctx context.Context, t *testing.T, svc *serviceProcess) *mcpServiceProcess {
	t.Helper()
	listen := freeListenAddr(t)
	token := "mcp-test-token"
	cmd := exec.CommandContext(ctx, fx.mcpBin,
		"--listen", listen,
		"--caseapi-base", svc.baseURL,
		"--bearer-token", token,
	)
	cmd.Dir = fx.arbRoot
	stdoutLog, stderrLog := fx.processLogPaths()
	proc := startTestProcess(cmd, stdoutLog, stderrLog)
	mcp := &mcpServiceProcess{testProcess: proc, baseURL: "http://" + listen, token: token}
	waitMCPHealth(ctx, t, mcp)
	return mcp
}

func waitMCPHealth(ctx context.Context, t *testing.T, mcp *mcpServiceProcess) {
	t.Helper()
	ticker := time.NewTicker(20 * time.Millisecond)
	defer ticker.Stop()
	for {
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, mcp.baseURL+"/health", nil)
		if err != nil {
			t.Fatalf("build MCP health request: %v", err)
		}
		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			if err := resp.Body.Close(); err != nil {
				t.Fatalf("close MCP health response: %v", err)
			}
			if resp.StatusCode == http.StatusNoContent {
				return
			}
		}
		select {
		case err := <-mcp.done:
			t.Fatalf("aard mcp exited before health check: %v\nstderr:\n%s\nstdout:\n%s", err, mcp.stderrString(), mcp.stdoutString())
		case <-ctx.Done():
			t.Fatalf("timeout waiting for aard mcp health\nstderr:\n%s\nstdout:\n%s", mcp.stderrString(), mcp.stdoutString())
		case <-ticker.C:
		}
	}
}

func mcpInitialize(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, query string) string {
	t.Helper()
	resp := mcpPost(ctx, t, mcp, "/mcp?"+query, mcpRequest(t, "initialize", map[string]any{
		"protocolVersion": "2025-06-18",
		"capabilities":    map[string]any{},
		"clientInfo":      map[string]any{"name": "blackbox", "version": "0"},
	}), "")
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("MCP initialize HTTP %d: %s", resp.StatusCode, string(resp.Body))
	}
	sessionID := resp.Header.Get("Mcp-Session-Id")
	if sessionID == "" {
		t.Fatalf("MCP initialize missing Mcp-Session-Id: %s", string(resp.Body))
	}
	mcpDecodeRPC(t, resp.Body)
	return sessionID
}

func mcpListTools(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string) []map[string]any {
	t.Helper()
	result := mcpRPC(ctx, t, mcp, sessionID, "tools/list", map[string]any{})
	rawTools, ok := result["tools"].([]any)
	if !ok {
		t.Fatalf("MCP tools/list result = %#v", result)
	}
	tools := make([]map[string]any, 0, len(rawTools))
	for _, raw := range rawTools {
		tools = append(tools, mapAny(raw))
	}
	return tools
}

func mcpSubmitDecision(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string, toolName string, payload map[string]any) {
	t.Helper()
	mcpWaitReady(ctx, t, mcp, sessionID)
	mcpCallOK(ctx, t, mcp, sessionID, "submit_decision", map[string]any{
		"kind":      "tool",
		"tool_name": toolName,
		"payload":   payload,
	})
}

func mcpSubmitPass(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string) {
	t.Helper()
	mcpWaitReady(ctx, t, mcp, sessionID)
	mcpCallOK(ctx, t, mcp, sessionID, "submit_decision", map[string]any{"kind": "pass"})
}

func mcpWaitReady(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string) map[string]any {
	t.Helper()
	for {
		result := mcpCall(ctx, t, mcp, sessionID, "wait_for_opportunity", map[string]any{"timeout_ms": 5000})
		structured := mcpStructured(t, result)
		switch mapString(structured["state"]) {
		case "ready":
			return structured
		case "waiting":
		case "done", "failed", "error":
			t.Fatalf("MCP wait state = %q, want ready: %#v", mapString(structured["state"]), structured)
		default:
			t.Fatalf("MCP wait result missing state: %#v", structured)
		}
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for MCP assignment to become ready")
		default:
		}
	}
}

func mcpCallOK(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string, name string, arguments map[string]any) map[string]any {
	t.Helper()
	result := mcpCall(ctx, t, mcp, sessionID, name, arguments)
	structured := mcpStructured(t, result)
	if result["isError"] == true || structured["ok"] != true {
		t.Fatalf("MCP tool %s failed: result=%#v structured=%#v", name, result, structured)
	}
	if nested := mapAny(structured["result"]); len(nested) > 0 {
		return nested
	}
	return structured
}

func mcpCall(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string, name string, arguments map[string]any) map[string]any {
	t.Helper()
	return mcpRPC(ctx, t, mcp, sessionID, "tools/call", map[string]any{"name": name, "arguments": arguments})
}

func mcpRPC(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, sessionID string, method string, params map[string]any) map[string]any {
	t.Helper()
	resp := mcpPost(ctx, t, mcp, "/mcp", mcpRequest(t, method, params), sessionID)
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("MCP %s HTTP %d: %s", method, resp.StatusCode, string(resp.Body))
	}
	decoded := mcpDecodeRPC(t, resp.Body)
	if decoded.Error != nil {
		t.Fatalf("MCP %s JSON-RPC error = %#v", method, decoded.Error)
	}
	return mapAny(decoded.Result)
}

type mcpHTTPResponse struct {
	StatusCode int
	Header     http.Header
	Body       []byte
}

func mcpPost(ctx context.Context, t *testing.T, mcp *mcpServiceProcess, path string, body []byte, sessionID string) mcpHTTPResponse {
	t.Helper()
	endpoint := mcp.baseURL + path
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, endpoint, bytes.NewReader(body))
	if err != nil {
		t.Fatalf("build MCP POST request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+mcp.token)
	if sessionID != "" {
		req.Header.Set("Mcp-Session-Id", sessionID)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("POST %s: %v", endpoint, err)
	}
	defer func() {
		if err := resp.Body.Close(); err != nil {
			t.Errorf("close MCP response body: %v", err)
		}
	}()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read MCP response: %v", err)
	}
	logHTTPExchange(t, http.MethodPost, endpoint, body, resp.StatusCode, raw)
	return mcpHTTPResponse{StatusCode: resp.StatusCode, Header: resp.Header.Clone(), Body: raw}
}

type mcpRPCResponse struct {
	JSONRPC string       `json:"jsonrpc"`
	ID      any          `json:"id,omitempty"`
	Result  any          `json:"result,omitempty"`
	Error   *mcpRPCError `json:"error,omitempty"`
}

type mcpRPCError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

func mcpRequest(t *testing.T, method string, params map[string]any) []byte {
	t.Helper()
	raw, err := json.Marshal(map[string]any{"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
	if err != nil {
		t.Fatalf("marshal MCP request: %v", err)
	}
	return raw
}

func mcpDecodeRPC(t *testing.T, raw []byte) mcpRPCResponse {
	t.Helper()
	var out mcpRPCResponse
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	if err := dec.Decode(&out); err != nil {
		t.Fatalf("decode MCP response %q: %v", string(raw), err)
	}
	if out.JSONRPC != "2.0" {
		t.Fatalf("MCP response jsonrpc = %q, want 2.0: %#v", out.JSONRPC, out)
	}
	return out
}

func mcpStructured(t *testing.T, toolResult map[string]any) map[string]any {
	t.Helper()
	structured := mapAny(toolResult["structuredContent"])
	if len(structured) == 0 {
		t.Fatalf("MCP tool result missing structuredContent: %#v", toolResult)
	}
	return structured
}

func mcpHasTool(tools []map[string]any, name string) bool {
	for _, tool := range tools {
		if mapString(tool["name"]) == name {
			return true
		}
	}
	return false
}

func firstEvidenceID(t *testing.T, listResult map[string]any) string {
	t.Helper()
	evidence := listOfMaps(listResult["evidence"])
	if len(evidence) == 0 {
		t.Fatalf("evidence list is empty: %#v", listResult)
	}
	id := mapString(evidence[0]["evidence_id"])
	if id == "" {
		t.Fatalf("first evidence item missing evidence_id: %#v", evidence[0])
	}
	return id
}

func readTextFile(t *testing.T, path string) string {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	return string(raw)
}
