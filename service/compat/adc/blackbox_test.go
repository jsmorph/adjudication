package compat

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

var serviceBinDir = flag.String("service-bin-dir", "", "Directory containing service executables")
var carveBinDir = flag.String("carve-bin-dir", "", "Directory containing carve executables")
var carveRoot = flag.String("carve-root", "", "Carve checkout root")

func TestADCClerkMCPCompatibility(t *testing.T) {
	fx := newADCFixture(t)
	ctx, cancel := context.WithTimeout(context.Background(), 120*time.Second)
	defer cancel()

	service := fx.startService(ctx, t)
	defer service.stop(t)
	mcp := fx.startMCP(ctx, t, service.baseURL)
	defer mcp.stop(t)

	caseID := "adc-clerk-mcp"
	outDir := filepath.Join(fx.outputRoot, caseID)
	created := postADCJSON(ctx, t, service.baseURL+"/clerk/v1/cases", map[string]any{
		"mode":                    "direct",
		"case_id":                 caseID,
		"run_id":                  "run-" + caseID,
		"scenario_path":           fx.scenarioPath,
		"out_dir":                 outDir,
		"external_roles":          []string{"plaintiff", "defendant"},
		"roleapi_timeout_seconds": 30,
		"timeout_seconds":         30,
		"invalid_attempt_limit":   2,
	})
	if created["ok"] != true {
		t.Fatalf("create Clerk case: %#v", created)
	}

	plaintiff := initializeADCMCP(ctx, t, mcp, caseID, "plaintiff")
	defendant := initializeADCMCP(ctx, t, mcp, caseID, "defendant")
	observer := initializeADCMCP(ctx, t, mcp, caseID, "observer")

	partyTools := listADCMCPTools(ctx, t, mcp, plaintiff)
	for _, name := range []string{"wait_for_opportunity", "get_case", "send_work_notes", "submit_decision"} {
		if !hasADCMCPTool(partyTools, name) {
			t.Fatalf("plaintiff MCP tools missing %s: %#v", name, partyTools)
		}
	}
	observerTools := listADCMCPTools(ctx, t, mcp, observer)
	if !hasADCMCPTool(observerTools, "get_case_result") || hasADCMCPTool(observerTools, "submit_decision") {
		t.Fatalf("observer MCP tools are wrong: %#v", observerTools)
	}
	rejected := callADCMCP(ctx, t, mcp, observer, "submit_decision", map[string]any{"kind": "pass"})
	if rejected["isError"] != true || adcMap(rejected["structuredContent"])["ok"] != false {
		t.Fatalf("observer mutation was not rejected: %#v", rejected)
	}

	waitADCReady(ctx, t, mcp, plaintiff, "filed", "file_complaint")
	callADCMCPOK(ctx, t, mcp, plaintiff, "send_work_notes", map[string]any{
		"notes": "Plaintiff reviewed the current case before filing through MCP.",
	})
	caseView := callADCMCPOK(ctx, t, mcp, plaintiff, "get_case", map[string]any{})
	if len(adcMap(caseView["result"])) == 0 {
		t.Fatalf("get_case returned no result: %#v", caseView)
	}
	submitADCDecision(ctx, t, mcp, plaintiff, "filed", "file_complaint", map[string]any{
		"summary": "Plaintiff alleges a civil claim and requests judgment.",
	})
	submitADCDecision(ctx, t, mcp, defendant, "filed", "file_answer", map[string]any{
		"summary": "Defendant denies liability and requests judgment.",
	})

	submitADCDecision(ctx, t, mcp, plaintiff, "plaintiff_evidence", "rest_case", map[string]any{})
	submitADCDecision(ctx, t, mcp, defendant, "defense_evidence", "rest_case", map[string]any{})
	submitADCDecision(ctx, t, mcp, plaintiff, "plaintiff_rebuttal_evidence", "rest_case", map[string]any{})
	submitADCDecision(ctx, t, mcp, defendant, "defense_surrebuttal_evidence", "rest_case", map[string]any{})

	submitADCDecision(ctx, t, mcp, plaintiff, "charge_conference", "propose_jury_instruction", map[string]any{
		"party":          "plaintiff",
		"instruction_id": "PI-1",
		"text":           "Plaintiff bears the burden of proof.",
	})
	submitADCDecision(ctx, t, mcp, defendant, "charge_conference", "propose_jury_instruction", map[string]any{
		"party":          "defendant",
		"instruction_id": "DI-1",
		"text":           "Judgment follows if plaintiff does not carry the burden.",
	})
	submitADCDecision(ctx, t, mcp, plaintiff, "closings", "deliver_closing_argument", map[string]any{
		"party":    "plaintiff",
		"argument": "The record supports judgment for plaintiff.",
	})
	submitADCDecision(ctx, t, mcp, defendant, "closings", "deliver_closing_argument", map[string]any{
		"party":    "defendant",
		"argument": "The record does not support plaintiff's claim.",
	})
	submitADCPass(ctx, t, mcp, plaintiff, "closings")

	result := pollADCStatus(ctx, t, service.baseURL+"/clerk/v1/cases/"+url.PathEscape(caseID)+"/result", "done")
	finalResult := adcMap(result["result"])
	assertADCFinalState(t, finalResult)

	mcpResult := callADCMCPOK(ctx, t, mcp, observer, "get_case_result", map[string]any{})
	if adcString(mcpResult["status"]) != "done" {
		t.Fatalf("observer result status = %q, want done: %#v", adcString(mcpResult["status"]), mcpResult)
	}
	assertADCFinalState(t, adcMap(mcpResult["result"]))

	recordResponse := pollADCCaseRecord(ctx, t, service.baseURL+"/clerk/v1/cases/"+url.PathEscape(caseID), "completed")
	record := adcMap(recordResponse["case"])
	if adcInt(record["exit_code"]) != 0 {
		t.Fatalf("service exit_code = %d, want 0: %#v", adcInt(record["exit_code"]), record)
	}
	if adcString(adcMap(record["summary"])["scenario"]) != "adc_clerk_mcp_compatibility" {
		t.Fatalf("service summary is wrong: %#v", record["summary"])
	}

	artifacts := getADCJSON(ctx, t, service.baseURL+"/clerk/v1/cases/"+url.PathEscape(caseID)+"/artifacts")
	for _, name := range []string{"run.json", "state.json", "certificate.json", "events.ndjson", "work-notes.ndjson"} {
		if !hasADCArtifact(artifacts["artifacts"], name) {
			t.Fatalf("Clerk artifact list missing %s: %#v", name, artifacts)
		}
	}

	run := readADCJSONFile(t, filepath.Join(outDir, "run.json"))
	assertADCFinalState(t, run)
	state := readADCJSONFile(t, filepath.Join(outDir, "state.json"))
	if adcString(adcMap(state["case"])["status"]) != "judgment_entered" {
		t.Fatalf("state case status = %#v", adcMap(state["case"])["status"])
	}
	workNotes, err := os.ReadFile(filepath.Join(outDir, "work-notes.ndjson"))
	if err != nil {
		t.Fatalf("read work notes: %v", err)
	}
	if !bytes.Contains(workNotes, []byte("Plaintiff reviewed the current case before filing through MCP.")) {
		t.Fatalf("work notes lack MCP note: %s", workNotes)
	}
	assertADCActions(t, filepath.Join(outDir, "events.ndjson"), "file_complaint", "file_answer", "file_bench_opinion", "enter_judgment")

	verify := exec.CommandContext(ctx, fx.adcBin, "verify-certificate", "--dir", outDir, "--engine", fx.enginePath)
	verify.Dir = fx.adcRoot
	verified, err := verify.CombinedOutput()
	if err != nil {
		t.Fatalf("verify ADC certificate: %v\n%s", err, verified)
	}
	if fx.judgeCalls.Load() != 1 || fx.summaryCalls.Load() != 1 {
		t.Fatalf("fake provider calls: judge=%d summary=%d, want one each", fx.judgeCalls.Load(), fx.summaryCalls.Load())
	}
}

type adcFixture struct {
	dir          string
	adcRoot      string
	adcBin       string
	serviceBin   string
	mcpBin       string
	enginePath   string
	scenarioPath string
	outputRoot   string
	provider     *httptest.Server
	judgeCalls   atomic.Int64
	summaryCalls atomic.Int64
}

func newADCFixture(t *testing.T) *adcFixture {
	t.Helper()
	serviceBins := strings.TrimSpace(*serviceBinDir)
	carveBins := strings.TrimSpace(*carveBinDir)
	carveCheckout := strings.TrimSpace(*carveRoot)
	if serviceBins == "" || carveBins == "" || carveCheckout == "" {
		t.Skip("-service-bin-dir, -carve-bin-dir, and -carve-root are required")
	}
	carveCheckout, err := filepath.Abs(carveCheckout)
	if err != nil {
		t.Fatalf("resolve carve root: %v", err)
	}
	dir, err := os.MkdirTemp("", "adc-clerk-mcp-")
	if err != nil {
		t.Fatalf("create compatibility directory: %v", err)
	}
	t.Logf("ADC compatibility directory: %s", dir)
	fx := &adcFixture{
		dir:          dir,
		adcRoot:      filepath.Join(carveCheckout, "adc"),
		adcBin:       filepath.Join(carveBins, "adc"),
		serviceBin:   filepath.Join(serviceBins, "adc-service"),
		mcpBin:       filepath.Join(serviceBins, "adc-mcp"),
		enginePath:   filepath.Join(carveCheckout, "adc", "engine", ".lake", "build", "bin", "adcengine"),
		scenarioPath: filepath.Join(dir, "scenario.json"),
		outputRoot:   filepath.Join(dir, "service-output"),
	}
	for _, path := range []string{fx.adcBin, fx.serviceBin, fx.mcpBin, fx.enginePath} {
		info, err := os.Stat(path)
		if err != nil {
			t.Fatalf("stat compatibility executable %s: %v", path, err)
		}
		if info.IsDir() {
			t.Fatalf("compatibility executable is a directory: %s", path)
		}
	}
	if err := os.MkdirAll(fx.outputRoot, 0o755); err != nil {
		t.Fatalf("create service output root: %v", err)
	}
	writeADCJSONFile(t, fx.scenarioPath, adcCompatibilityScenario())
	fx.provider = newADCProvider(t, &fx.judgeCalls, &fx.summaryCalls)
	t.Cleanup(func() {
		fx.provider.Close()
		if t.Failed() {
			t.Logf("retained ADC compatibility directory: %s", dir)
			return
		}
		if err := os.RemoveAll(dir); err != nil {
			t.Errorf("remove compatibility directory %s: %v", dir, err)
		}
	})
	return fx
}

func adcCompatibilityScenario() map[string]any {
	return map[string]any{
		"name":       "adc_clerk_mcp_compatibility",
		"court_name": "United States District",
		"model":      "blackbox-judge",
		"initial_cases": []map[string]any{{
			"case_id": "adc-clerk-mcp", "caption": "Plaintiff v. Defendant", "judge": "Test Judge", "filed_on": "2026-08-05",
		}},
		"claims": []map[string]any{{
			"claim_id": "claim-1", "label": "Civil claim", "legal_theory": "civil_claim",
			"standard_of_proof": "preponderance_of_the_evidence", "burden_holder": "plaintiff",
			"elements": []string{"duty", "breach", "causation", "damages"}, "defenses": []string{},
			"damages_question": "What damages, if any, are proven?",
		}},
		"roles": []map[string]any{
			{"name": "plaintiff", "instructions": "Act for plaintiff.", "allowed_actions": []string{"file_complaint", "rest_case", "propose_jury_instruction", "deliver_closing_argument"}},
			{"name": "defendant", "instructions": "Act for defendant.", "allowed_actions": []string{"file_answer", "rest_case", "propose_jury_instruction", "deliver_closing_argument"}},
			{"name": "clerk", "instructions": "Perform deterministic clerk actions.", "allowed_actions": []string{"set_last_pleading_served_on"}},
			{"name": "judge", "model": "blackbox-judge", "instructions": "Decide the case.", "allowed_actions": []string{"resolve_trial_mode", "transition_case", "advance_trial_phase", "file_bench_opinion", "enter_judgment"}},
		},
		"loop_policy": map[string]any{
			"type": "autopilot_trial", "max_steps_per_turn": 2, "max_turns": 40,
			"stop_on_case_status": "judgment_entered", "stop_case_index": 0,
		},
		"assertions": []map[string]any{
			{"type": "trial_mode", "case_index": 0, "equals": "bench"},
			{"type": "case_status", "case_index": 0, "equals": "judgment_entered"},
			{"type": "decision_trace_contains_action", "case_index": 0, "action": "file_bench_opinion"},
			{"type": "decision_trace_contains_action", "case_index": 0, "action": "enter_judgment"},
		},
	}
}

func newADCProvider(t *testing.T, judgeCalls *atomic.Int64, summaryCalls *atomic.Int64) *httptest.Server {
	t.Helper()
	return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost || r.URL.Path != "/v1/responses" {
			http.NotFound(w, r)
			return
		}
		defer r.Body.Close()
		var request map[string]any
		if err := json.NewDecoder(r.Body).Decode(&request); err != nil {
			t.Errorf("decode judge request: %v", err)
			http.Error(w, "bad request", http.StatusBadRequest)
			return
		}
		tools := adcList(request["tools"])
		if len(tools) == 0 {
			summaryCalls.Add(1)
			writeADCProviderResponse(t, w, []map[string]any{{
				"id": "msg_adc_summary", "type": "message", "status": "completed", "role": "assistant",
				"content": []map[string]any{{
					"type":        "output_text",
					"text":        `{"plaintiff_summary":"Plaintiff requested judgment based on the pleaded civil claim. [Closing argument - plaintiff]","defendant_summary":"Defendant denied liability and argued that plaintiff did not carry the burden. [Closing argument - defendant]"}`,
					"annotations": []any{},
				}},
			}})
			return
		}
		found := false
		for _, raw := range tools {
			if adcString(adcMap(raw)["name"]) == "file_bench_opinion" {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("judge request lacks file_bench_opinion: %#v", request["tools"])
		}
		judgeCalls.Add(1)
		writeADCProviderResponse(t, w, []map[string]any{{
			"id": "fc_adc_judge", "type": "function_call", "status": "completed",
			"call_id": "call_adc_judge", "name": "file_bench_opinion",
			"arguments": `{"text":"After considering the pleadings and trial record, the court finds that plaintiff did not prove the claim by a preponderance of the evidence. Judgment shall be entered on the bench verdict."}`,
		}})
	}))
}

func writeADCProviderResponse(t *testing.T, w http.ResponseWriter, output []map[string]any) {
	t.Helper()
	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(map[string]any{
		"id": "resp_adc_compatibility", "object": "response", "created_at": time.Now().Unix(),
		"status": "completed", "model": "blackbox-judge", "output": output,
		"usage": map[string]any{"input_tokens": 1, "output_tokens": 1, "total_tokens": 2},
	}); err != nil {
		t.Errorf("write provider response: %v", err)
	}
}

type adcProcess struct {
	cmd    *exec.Cmd
	stdout adcLockedBuffer
	stderr adcLockedBuffer
	done   chan struct{}
	mu     sync.Mutex
	err    error
}

func startADCProcess(t *testing.T, cmd *exec.Cmd) *adcProcess {
	t.Helper()
	p := &adcProcess{cmd: cmd, done: make(chan struct{})}
	cmd.Stdout = &p.stdout
	cmd.Stderr = &p.stderr
	if err := cmd.Start(); err != nil {
		t.Fatalf("start %s: %v", cmd.Path, err)
	}
	go func() {
		err := cmd.Wait()
		p.mu.Lock()
		p.err = err
		p.mu.Unlock()
		close(p.done)
	}()
	return p
}

func (p *adcProcess) stop(t *testing.T) {
	t.Helper()
	select {
	case <-p.done:
		return
	default:
	}
	if p.cmd.Process != nil {
		if err := p.cmd.Process.Kill(); err != nil && !errors.Is(err, os.ErrProcessDone) {
			t.Errorf("kill %s: %v", p.cmd.Path, err)
		}
	}
	select {
	case <-p.done:
	case <-time.After(3 * time.Second):
		t.Errorf("timeout stopping %s", p.cmd.Path)
	}
}

func (p *adcProcess) failureText() string {
	p.mu.Lock()
	err := p.err
	p.mu.Unlock()
	return fmt.Sprintf("error: %v\nstderr:\n%s\nstdout:\n%s", err, p.stderr.String(), p.stdout.String())
}

type adcLockedBuffer struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (b *adcLockedBuffer) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.Write(p)
}

func (b *adcLockedBuffer) String() string {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.String()
}

type adcServiceProcess struct {
	*adcProcess
	baseURL string
}

func (fx *adcFixture) startService(ctx context.Context, t *testing.T) *adcServiceProcess {
	t.Helper()
	listen := freeADCListenAddr(t)
	cmd := exec.CommandContext(ctx, fx.serviceBin,
		"--listen", listen,
		"--output-root", fx.outputRoot,
		"--adc-bin", fx.adcBin,
		"--adc-working-dir", fx.adcRoot,
		"--engine", fx.enginePath,
		"--case-startup-timeout", "20s",
	)
	cmd.Dir = fx.dir
	cmd.Env = adcMergedEnv(map[string]string{
		"OPENAI_API_KEY":  "compatibility-key",
		"OPENAI_BASE_URL": fx.provider.URL + "/v1",
	})
	process := startADCProcess(t, cmd)
	service := &adcServiceProcess{adcProcess: process, baseURL: "http://" + listen}
	waitADCHTTP(ctx, t, process, service.baseURL+"/api/v1/cases", http.StatusOK)
	return service
}

type adcMCPProcess struct {
	*adcProcess
	baseURL string
	token   string
}

func (fx *adcFixture) startMCP(ctx context.Context, t *testing.T, caseAPIBase string) *adcMCPProcess {
	t.Helper()
	listen := freeADCListenAddr(t)
	token := "adc-mcp-compatibility-token"
	cmd := exec.CommandContext(ctx, fx.mcpBin,
		"--listen", listen,
		"--caseapi-base", caseAPIBase,
		"--bearer-token", token,
		"--disable-session-expiry",
	)
	cmd.Dir = fx.dir
	process := startADCProcess(t, cmd)
	mcp := &adcMCPProcess{adcProcess: process, baseURL: "http://" + listen, token: token}
	waitADCHTTP(ctx, t, process, mcp.baseURL+"/health", http.StatusNoContent)
	return mcp
}

func waitADCHTTP(ctx context.Context, t *testing.T, process *adcProcess, endpoint string, want int) {
	t.Helper()
	ticker := time.NewTicker(20 * time.Millisecond)
	defer ticker.Stop()
	for {
		req, err := http.NewRequestWithContext(ctx, http.MethodGet, endpoint, nil)
		if err != nil {
			t.Fatalf("build health request: %v", err)
		}
		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			closeErr := resp.Body.Close()
			if closeErr != nil {
				t.Fatalf("close health response: %v", closeErr)
			}
			if resp.StatusCode == want {
				return
			}
			t.Fatalf("%s returned HTTP %d, want %d", endpoint, resp.StatusCode, want)
		}
		select {
		case <-process.done:
			t.Fatalf("process exited before health response from %s\n%s", endpoint, process.failureText())
		case <-ctx.Done():
			t.Fatalf("timeout waiting for %s\n%s", endpoint, process.failureText())
		case <-ticker.C:
		}
	}
}

func initializeADCMCP(ctx context.Context, t *testing.T, mcp *adcMCPProcess, caseID string, role string) string {
	t.Helper()
	query := "?case_id=" + url.QueryEscape(caseID) + "&role_id=" + url.QueryEscape(role)
	response := postADCMCP(ctx, t, mcp, query, "", adcRPCRequest(t, "initialize", map[string]any{
		"protocolVersion": "2025-06-18",
		"capabilities":    map[string]any{},
		"clientInfo":      map[string]any{"name": "adc-compatibility", "version": "0"},
	}))
	if response.status != http.StatusOK {
		t.Fatalf("initialize MCP HTTP %d: %s", response.status, response.body)
	}
	sessionID := response.header.Get("Mcp-Session-Id")
	if sessionID == "" {
		t.Fatalf("initialize MCP lacks session ID: %s", response.body)
	}
	decodeADCRPC(t, response.body)
	return sessionID
}

func listADCMCPTools(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string) []any {
	t.Helper()
	result := adcMCPRPC(ctx, t, mcp, sessionID, "tools/list", map[string]any{})
	return adcList(result["tools"])
}

func hasADCMCPTool(tools []any, name string) bool {
	for _, raw := range tools {
		if adcString(adcMap(raw)["name"]) == name {
			return true
		}
	}
	return false
}

func waitADCReady(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string, phase string, tool string) map[string]any {
	t.Helper()
	for {
		structured := adcMap(callADCMCP(ctx, t, mcp, sessionID, "wait_for_opportunity", map[string]any{"timeout_ms": 5000})["structuredContent"])
		switch adcString(structured["state"]) {
		case "ready":
			opportunity := adcMap(structured["opportunity"])
			if adcString(opportunity["phase"]) != phase {
				t.Fatalf("opportunity phase = %q, want %q: %#v", adcString(opportunity["phase"]), phase, opportunity)
			}
			if tool != "" && !adcContainsString(opportunity["allowed_legal_tools"], tool) {
				t.Fatalf("opportunity lacks %s: %#v", tool, opportunity)
			}
			return opportunity
		case "waiting":
		case "done", "failed", "error":
			t.Fatalf("MCP wait state = %q, want ready: %#v", adcString(structured["state"]), structured)
		default:
			t.Fatalf("MCP wait lacks state: %#v", structured)
		}
		if ctx.Err() != nil {
			t.Fatalf("timeout waiting for MCP opportunity: %v", ctx.Err())
		}
	}
}

func submitADCDecision(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string, phase string, tool string, payload map[string]any) {
	t.Helper()
	waitADCReady(ctx, t, mcp, sessionID, phase, tool)
	callADCMCPOK(ctx, t, mcp, sessionID, "submit_decision", map[string]any{
		"kind": "tool", "tool_name": tool, "payload": payload,
	})
}

func submitADCPass(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string, phase string) {
	t.Helper()
	opportunity := waitADCReady(ctx, t, mcp, sessionID, phase, "deliver_closing_argument")
	if opportunity["may_pass"] != true {
		t.Fatalf("closing rebuttal opportunity does not allow pass: %#v", opportunity)
	}
	callADCMCPOK(ctx, t, mcp, sessionID, "submit_decision", map[string]any{
		"kind": "pass", "reason": "Plaintiff waives closing rebuttal.",
	})
}

func callADCMCPOK(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string, name string, arguments map[string]any) map[string]any {
	t.Helper()
	result := callADCMCP(ctx, t, mcp, sessionID, name, arguments)
	structured := adcMap(result["structuredContent"])
	if result["isError"] == true || structured["ok"] != true {
		t.Fatalf("MCP tool %s failed: result=%#v structured=%#v", name, result, structured)
	}
	return structured
}

func callADCMCP(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string, name string, arguments map[string]any) map[string]any {
	t.Helper()
	return adcMCPRPC(ctx, t, mcp, sessionID, "tools/call", map[string]any{"name": name, "arguments": arguments})
}

func adcMCPRPC(ctx context.Context, t *testing.T, mcp *adcMCPProcess, sessionID string, method string, params map[string]any) map[string]any {
	t.Helper()
	response := postADCMCP(ctx, t, mcp, "", sessionID, adcRPCRequest(t, method, params))
	if response.status != http.StatusOK {
		t.Fatalf("MCP %s HTTP %d: %s", method, response.status, response.body)
	}
	rpc := decodeADCRPC(t, response.body)
	if rpc.Error != nil {
		t.Fatalf("MCP %s error: %#v", method, rpc.Error)
	}
	return adcMap(rpc.Result)
}

type adcMCPHTTPResponse struct {
	status int
	header http.Header
	body   []byte
}

func postADCMCP(ctx context.Context, t *testing.T, mcp *adcMCPProcess, query string, sessionID string, body []byte) adcMCPHTTPResponse {
	t.Helper()
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, mcp.baseURL+"/mcp"+query, bytes.NewReader(body))
	if err != nil {
		t.Fatalf("build MCP request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+mcp.token)
	if sessionID != "" {
		req.Header.Set("Mcp-Session-Id", sessionID)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("MCP POST: %v", err)
	}
	defer func() {
		if err := resp.Body.Close(); err != nil {
			t.Errorf("close MCP response: %v", err)
		}
	}()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read MCP response: %v", err)
	}
	return adcMCPHTTPResponse{status: resp.StatusCode, header: resp.Header.Clone(), body: raw}
}

type adcRPCResponse struct {
	JSONRPC string       `json:"jsonrpc"`
	Result  any          `json:"result"`
	Error   *adcRPCError `json:"error"`
}

type adcRPCError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

func adcRPCRequest(t *testing.T, method string, params map[string]any) []byte {
	t.Helper()
	raw, err := json.Marshal(map[string]any{"jsonrpc": "2.0", "id": 1, "method": method, "params": params})
	if err != nil {
		t.Fatalf("marshal MCP request: %v", err)
	}
	return raw
}

func decodeADCRPC(t *testing.T, raw []byte) adcRPCResponse {
	t.Helper()
	var response adcRPCResponse
	decoder := json.NewDecoder(bytes.NewReader(raw))
	decoder.UseNumber()
	if err := decoder.Decode(&response); err != nil {
		t.Fatalf("decode MCP response %q: %v", raw, err)
	}
	if response.JSONRPC != "2.0" {
		t.Fatalf("MCP jsonrpc = %q, want 2.0: %#v", response.JSONRPC, response)
	}
	return response
}

func pollADCStatus(ctx context.Context, t *testing.T, endpoint string, want string) map[string]any {
	t.Helper()
	for {
		response := getADCJSON(ctx, t, endpoint)
		status := adcString(response["status"])
		if status == want {
			return response
		}
		if status == "failed" {
			t.Fatalf("case reached failed status while waiting for %s: %#v", want, response)
		}
		if ctx.Err() != nil {
			t.Fatalf("timeout waiting for status %s: last response=%#v", want, response)
		}
		time.Sleep(50 * time.Millisecond)
	}
}

func pollADCCaseRecord(ctx context.Context, t *testing.T, endpoint string, want string) map[string]any {
	t.Helper()
	for {
		response := getADCJSON(ctx, t, endpoint)
		status := adcString(adcMap(response["case"])["status"])
		if status == want {
			return response
		}
		if status == "failed" {
			t.Fatalf("service case reached failed status while waiting for %s: %#v", want, response)
		}
		if ctx.Err() != nil {
			t.Fatalf("timeout waiting for case status %s: last response=%#v", want, response)
		}
		time.Sleep(50 * time.Millisecond)
	}
}

func postADCJSON(ctx context.Context, t *testing.T, endpoint string, body map[string]any) map[string]any {
	t.Helper()
	raw, err := json.Marshal(body)
	if err != nil {
		t.Fatalf("marshal POST body: %v", err)
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, endpoint, bytes.NewReader(raw))
	if err != nil {
		t.Fatalf("build POST request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	return doADCJSON(t, req)
}

func getADCJSON(ctx context.Context, t *testing.T, endpoint string) map[string]any {
	t.Helper()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, endpoint, nil)
	if err != nil {
		t.Fatalf("build GET request: %v", err)
	}
	return doADCJSON(t, req)
}

func doADCJSON(t *testing.T, req *http.Request) map[string]any {
	t.Helper()
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("%s %s: %v", req.Method, req.URL, err)
	}
	defer func() {
		if err := resp.Body.Close(); err != nil {
			t.Errorf("close HTTP response: %v", err)
		}
	}()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read %s response: %v", req.URL, err)
	}
	var response map[string]any
	decoder := json.NewDecoder(bytes.NewReader(raw))
	decoder.UseNumber()
	if err := decoder.Decode(&response); err != nil {
		t.Fatalf("decode %s HTTP %d: %v\n%s", req.URL, resp.StatusCode, err, raw)
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		t.Fatalf("%s returned HTTP %d: %#v", req.URL, resp.StatusCode, response)
	}
	return response
}

func assertADCFinalState(t *testing.T, result map[string]any) {
	t.Helper()
	if adcString(result["scenario"]) != "adc_clerk_mcp_compatibility" {
		t.Fatalf("scenario = %q, want compatibility scenario: %#v", adcString(result["scenario"]), result)
	}
	caseState := adcMap(adcMap(result["final_state"])["case"])
	if adcString(caseState["status"]) != "judgment_entered" || adcString(caseState["trial_mode"]) != "bench" {
		t.Fatalf("final case state is wrong: %#v", caseState)
	}
	for _, assertion := range adcList(result["assertions"]) {
		if adcMap(assertion)["passed"] != true {
			t.Fatalf("scenario assertion failed: %#v", assertion)
		}
	}
}

func assertADCActions(t *testing.T, path string, wanted ...string) {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read events: %v", err)
	}
	found := map[string]bool{}
	for _, line := range strings.Split(strings.TrimSpace(string(raw)), "\n") {
		if strings.TrimSpace(line) == "" {
			continue
		}
		var event map[string]any
		if err := json.Unmarshal([]byte(line), &event); err != nil {
			t.Fatalf("parse event %q: %v", line, err)
		}
		found[adcString(event["action"])] = true
	}
	for _, action := range wanted {
		if !found[action] {
			t.Fatalf("events lack action %s: found=%v", action, found)
		}
	}
}

func hasADCArtifact(value any, name string) bool {
	for _, raw := range adcList(value) {
		if adcString(adcMap(raw)["name"]) == name {
			return true
		}
	}
	return false
}

func readADCJSONFile(t *testing.T, path string) map[string]any {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var value map[string]any
	if err := json.Unmarshal(raw, &value); err != nil {
		t.Fatalf("parse %s: %v", path, err)
	}
	return value
}

func writeADCJSONFile(t *testing.T, path string, value any) {
	t.Helper()
	raw, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		t.Fatalf("marshal %s: %v", path, err)
	}
	if err := os.WriteFile(path, append(raw, '\n'), 0o644); err != nil {
		t.Fatalf("write %s: %v", path, err)
	}
}

func freeADCListenAddr(t *testing.T) string {
	t.Helper()
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("allocate listen address: %v", err)
	}
	address := listener.Addr().String()
	if err := listener.Close(); err != nil {
		t.Fatalf("close listen address: %v", err)
	}
	return address
}

func adcMergedEnv(overrides map[string]string) []string {
	env := os.Environ()
	for key, value := range overrides {
		prefix := key + "="
		replaced := false
		for i, existing := range env {
			if strings.HasPrefix(existing, prefix) {
				env[i] = prefix + value
				replaced = true
				break
			}
		}
		if !replaced {
			env = append(env, prefix+value)
		}
	}
	return env
}

func adcMap(value any) map[string]any {
	result, _ := value.(map[string]any)
	if result == nil {
		return map[string]any{}
	}
	return result
}

func adcList(value any) []any {
	result, _ := value.([]any)
	return result
}

func adcString(value any) string {
	text, _ := value.(string)
	return strings.TrimSpace(text)
}

func adcInt(value any) int {
	switch typed := value.(type) {
	case json.Number:
		integer, _ := typed.Int64()
		return int(integer)
	case float64:
		return int(typed)
	case int:
		return typed
	default:
		return 0
	}
}

func adcContainsString(value any, wanted string) bool {
	for _, raw := range adcList(value) {
		if adcString(raw) == wanted {
			return true
		}
	}
	return false
}
