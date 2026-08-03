package localrun

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"flag"
	"net"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"adjudication/service/modelrequest"
)

var pairedCoreBinDir = flag.String("carve-bin-dir", "", "Directory containing paired carve executables")
var pairedCoreRoot = flag.String("carve-root", "", "Paired carve checkout root")

func TestRenderInstructionsUsesTemplateData(t *testing.T) {
	path := filepath.Join(t.TempDir(), "lawyer.md.tmpl")
	if err := os.WriteFile(path, []byte("case={{.CaseID}} role={{.RoleID}} server={{.MCPServer}} url={{.MCPURL}}\n"), 0o644); err != nil {
		t.Fatalf("write template: %v", err)
	}
	got, err := renderInstructions(path, instructionData{
		CaseID:    "case-1",
		RoleID:    "plaintiff",
		MCPServer: "aard-case-1-plaintiff",
		MCPURL:    "http://example/mcp",
	})
	if err != nil {
		t.Fatalf("render instructions: %v", err)
	}
	for _, want := range []string{"case=case-1", "role=plaintiff", "server=aard-case-1-plaintiff", "url=http://example/mcp"} {
		if !strings.Contains(got, want) {
			t.Fatalf("rendered instructions missing %q: %s", want, got)
		}
	}
}

func TestRenderInstructionsRejectsMissingTemplateKey(t *testing.T) {
	path := filepath.Join(t.TempDir(), "bad.md.tmpl")
	if err := os.WriteFile(path, []byte("{{.Missing}}\n"), 0o644); err != nil {
		t.Fatalf("write template: %v", err)
	}
	_, err := renderInstructions(path, instructionData{CaseID: "case-1"})
	if err == nil {
		t.Fatalf("expected missing key error")
	}
}

func TestCoreCaseArgsUseProcessInterface(t *testing.T) {
	args := coreCaseArgs(Options{
		ComplaintPath:              "/case/complaint.md",
		CaseFiles:                  []string{"/case/source-1", "/case/source-2"},
		OutputDir:                  "/out",
		PolicyPath:                 "/case/policy.json",
		CouncilSize:                3,
		JudgmentStandard:           "score from 0 through 100",
		AttorneyInstructionsPath:   "/case/attorney.md",
		PromptDir:                  "/case/prompts",
		AttorneyCommonPromptPath:   "/case/common.md",
		AttorneyArgumentPromptPath: "/case/arguments.md",
		AttorneyRebuttalPromptPath: "/case/rebuttals.md",
		CommonRoot:                 "/common",
		CouncilPoolPath:            "/case/pool.jsonl",
		CouncilTimeoutSeconds:      90,
		LawyerTimeoutSeconds:       60,
		MaxResponseBytes:           4096,
		InvalidAttemptLimit:        2,
		EnginePath:                 "/bin/aardengine",
		RunID:                      "run-1",
		CaseID:                     "case-1",
	}, "127.0.0.1:9001")
	joined := strings.Join(args, "\x00")
	for _, want := range []string{
		"case", "--complaint\x00/case/complaint.md", "--file\x00/case/source-1",
		"--file\x00/case/source-2", "--out-dir\x00/out", "--case-id\x00case-1",
		"--run-id\x00run-1", "--caseapi-addr\x00127.0.0.1:9001",
		"--council-backend\x00councilapi", "--policy\x00/case/policy.json",
		"--judgment-standard\x00score from 0 through 100", "--engine\x00/bin/aardengine",
	} {
		if !strings.Contains(joined, want) {
			t.Fatalf("core args lack %q: %#v", want, args)
		}
	}
}

func TestStartCoreCaseReadsFreshResult(t *testing.T) {
	dir := t.TempDir()
	logDir := filepath.Join(dir, "logs")
	if err := os.MkdirAll(logDir, 0o755); err != nil {
		t.Fatalf("mkdir logs: %v", err)
	}
	core := filepath.Join(dir, "aard-core")
	script := `#!/bin/sh
set -eu
out_dir=
case_id=
run_id=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out-dir) out_dir=$2; shift 2 ;;
    --case-id) case_id=$2; shift 2 ;;
    --run-id) run_id=$2; shift 2 ;;
    *) shift ;;
  esac
done
printf '{"case_id":"%s","run_id":"%s","status":"ok","answers":{"C1":72},"extra":"preserved"}\n' "$case_id" "$run_id" > "$out_dir/run.json"
printf '{"status":"ok","answers":{"C1":72}}\n'
`
	if err := os.WriteFile(core, []byte(script), 0o755); err != nil {
		t.Fatalf("write fake core: %v", err)
	}
	done, err := startCoreCase(context.Background(), Options{
		CoreCommand:   core,
		ComplaintPath: filepath.Join(dir, "complaint.md"),
		OutputDir:     dir,
		CaseID:        "case-1",
		RunID:         "run-1",
	}, "127.0.0.1:9001", logDir)
	if err != nil {
		t.Fatalf("start core case: %v", err)
	}
	outcome := <-done
	if outcome.err != nil {
		t.Fatalf("core outcome: %v", outcome.err)
	}
	if outcome.result.Status != "ok" || outcome.result.Answers["C1"] != 72 {
		t.Fatalf("result = %#v", outcome.result)
	}
	raw, err := json.Marshal(outcome.result)
	if err != nil {
		t.Fatalf("marshal result: %v", err)
	}
	if !strings.Contains(string(raw), `"extra":"preserved"`) {
		t.Fatalf("marshaled result lost core fields: %s", raw)
	}
}

func TestStartCoreCaseRejectsStaleResult(t *testing.T) {
	dir := t.TempDir()
	logDir := filepath.Join(dir, "logs")
	if err := os.MkdirAll(logDir, 0o755); err != nil {
		t.Fatalf("mkdir logs: %v", err)
	}
	if err := os.WriteFile(filepath.Join(dir, "run.json"), []byte(`{"status":"stale"}`+"\n"), 0o644); err != nil {
		t.Fatalf("write stale result: %v", err)
	}
	core := filepath.Join(dir, "aard-core")
	if err := os.WriteFile(core, []byte("#!/bin/sh\nexit 0\n"), 0o755); err != nil {
		t.Fatalf("write fake core: %v", err)
	}
	done, err := startCoreCase(context.Background(), Options{
		CoreCommand:   core,
		ComplaintPath: filepath.Join(dir, "complaint.md"),
		OutputDir:     dir,
		CaseID:        "case-1",
	}, "127.0.0.1:9001", logDir)
	if err != nil {
		t.Fatalf("start core case: %v", err)
	}
	outcome := <-done
	if outcome.err == nil || !strings.Contains(outcome.err.Error(), "did not replace existing result") {
		t.Fatalf("outcome error = %v", outcome.err)
	}
}

func TestPairedCoreCaseAPI(t *testing.T) {
	binDir := strings.TrimSpace(*pairedCoreBinDir)
	carveRoot := strings.TrimSpace(*pairedCoreRoot)
	if binDir == "" || carveRoot == "" {
		t.Skip("-carve-bin-dir and -carve-root are not set")
	}
	coreCommand := filepath.Join(binDir, "aard")
	enginePath := filepath.Join(carveRoot, "arbd", "engine", ".lake", "build", "bin", "aardengine")
	for _, path := range []string{coreCommand, enginePath} {
		if _, err := os.Stat(path); err != nil {
			t.Fatalf("stat paired core path %s: %v", path, err)
		}
	}
	dir := t.TempDir()
	logDir := filepath.Join(dir, "logs")
	if err := os.MkdirAll(logDir, 0o755); err != nil {
		t.Fatalf("mkdir logs: %v", err)
	}
	complaintPath := filepath.Join(dir, "complaint.md")
	if err := os.WriteFile(complaintPath, []byte("# Question\n\nHow strongly does the record support the claim?\n"), 0o644); err != nil {
		t.Fatalf("write complaint: %v", err)
	}
	provider := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost || r.URL.Path != "/v1/responses" {
			http.NotFound(w, r)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		if err := json.NewEncoder(w).Encode(map[string]any{
			"id": "paired-response", "object": "response", "status": "completed",
			"model": "paired-council",
			"output": []map[string]any{{
				"id": "paired-message", "type": "message", "status": "completed", "role": "assistant",
				"content": []map[string]any{{"type": "output_text", "text": "ready", "annotations": []any{}}},
			}},
			"usage": map[string]any{"input_tokens": 1, "output_tokens": 1, "total_tokens": 2},
		}); err != nil {
			t.Errorf("write paired provider response: %v", err)
		}
	}))
	defer provider.Close()
	t.Setenv("OPENAI_API_KEY", "paired-key")
	t.Setenv("OPENAI_BASE_URL", provider.URL+"/v1")
	policyPath := filepath.Join(dir, "policy.json")
	if err := writeJSONFile(policyPath, map[string]any{
		"council_size":      1,
		"judgment_standard": "Answer with one integer from 0 through 100.",
	}); err != nil {
		t.Fatalf("write policy: %v", err)
	}
	poolDir := filepath.Join(dir, "pool")
	if err := os.MkdirAll(poolDir, 0o755); err != nil {
		t.Fatalf("mkdir pool: %v", err)
	}
	if err := os.WriteFile(filepath.Join(poolDir, "c1.txt"), []byte("Paired council persona.\n"), 0o644); err != nil {
		t.Fatalf("write persona: %v", err)
	}
	poolPath := filepath.Join(poolDir, "pool.jsonl")
	if err := os.WriteFile(poolPath, []byte(`{"endpoint":"openai","model":"paired-council","persona":"c1.txt"}`+"\n"), 0o644); err != nil {
		t.Fatalf("write pool: %v", err)
	}
	caseAPIAddr, err := resolveListenAddr("127.0.0.1:0", "127.0.0.1")
	if err != nil {
		t.Fatalf("resolve case API address: %v", err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	done, err := startCoreCase(ctx, Options{
		CoreCommand:           coreCommand,
		CoreWorkingDir:        filepath.Join(carveRoot, "arbd"),
		ComplaintPath:         complaintPath,
		OutputDir:             dir,
		PolicyPath:            policyPath,
		CommonRoot:            filepath.Join(carveRoot, "common"),
		CouncilPoolPath:       poolPath,
		EnginePath:            enginePath,
		CouncilTimeoutSeconds: 30,
		LawyerTimeoutSeconds:  30,
		RunID:                 "run-paired-arbd",
		CaseID:                "paired-arbd",
	}, caseAPIAddr, logDir)
	if err != nil {
		cancel()
		t.Fatalf("start paired core: %v", err)
	}
	baseURL := "http://" + caseAPIAddr
	if err := waitForHealth(ctx, baseURL+"/health", 20*time.Second); err != nil {
		cancel()
		outcome := <-done
		t.Fatalf("wait for paired core API: %v; core outcome: %v", err, outcome.err)
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, baseURL+"/lawyerapi/v1/status?case_id=paired-arbd&role_id=plaintiff", nil)
	if err != nil {
		cancel()
		t.Fatalf("build status request: %v", err)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		cancel()
		t.Fatalf("read paired core status: %v", err)
	}
	if err := resp.Body.Close(); err != nil {
		cancel()
		t.Fatalf("close paired core status: %v", err)
	}
	if resp.StatusCode != http.StatusOK {
		cancel()
		t.Fatalf("paired core status HTTP = %d", resp.StatusCode)
	}
	cancel()
	select {
	case outcome := <-done:
		if outcome.err == nil {
			t.Fatalf("canceled paired core returned no process error")
		}
	case <-time.After(5 * time.Second):
		t.Fatalf("paired core did not exit after cancellation")
	}
}

func TestPiCouncilInstructionsUseProxyToolNames(t *testing.T) {
	path := DefaultCouncilInstructionsPath()
	got, err := renderInstructions(path, instructionData{
		CaseID:    "case-1",
		MemberID:  "C1",
		MCPServer: defaultPiMCPServer,
		MCPURL:    "http://127.0.0.1:19780/mcp?case_id=case-1&member_id=C1",
	})
	if err != nil {
		t.Fatalf("render instructions: %v", err)
	}
	for _, want := range []string{"aard_wait_for_opportunity", "aard_get_case", "aard_list_evidence", "aard_stat_evidence", "aard_read_evidence_range", "aard_submit_council_answer"} {
		if !strings.Contains(got, want) {
			t.Fatalf("rendered instructions missing %q:\n%s", want, got)
		}
	}
	for _, want := range []string{"After `aard_submit_council_answer` returns `ok: true`", "Do not call `aard_wait_for_opportunity` again after your answer is accepted"} {
		if !strings.Contains(got, want) {
			t.Fatalf("rendered instructions missing stop rule %q:\n%s", want, got)
		}
	}
}

func TestRemoteLawyerSkillIncludesConnectionAndWorkLoop(t *testing.T) {
	path := DefaultRemoteLawyerSkillPath()
	mcpJSON := `{"url":"http://aard.example:8001/mcp?case_id=case-1&role_id=plaintiff","transport":"streamable-http","headers":{"Authorization":"Bearer token-1"}}`
	got, err := renderInstructions(path, instructionData{
		CaseID:    "case-1",
		RoleID:    "plaintiff",
		MCPServer: "aard-case-1-plaintiff",
		MCPURL:    "http://aard.example:8001/mcp?case_id=case-1&role_id=plaintiff",
		MCPJSON:   mcpJSON,
	})
	if err != nil {
		t.Fatalf("render instructions: %v", err)
	}
	for _, want := range []string{"openclaw mcp set", "aard-case-1-plaintiff", "Bearer token-1", "wait_for_opportunity", "send_work_notes", "submit_evidence", "submit_decision"} {
		if !strings.Contains(got, want) {
			t.Fatalf("rendered skill missing %q:\n%s", want, got)
		}
	}
}

func TestWritePiConfigFromRosterEntry(t *testing.T) {
	maxTokens := int64(1234)
	allowFallbacks := false
	home := t.TempDir()
	model, err := writePiConfig(home, councilRosterEntry{
		MemberID: "C1",
		RequestSpec: &modelrequest.Spec{
			Endpoint: "openrouter",
			Model:    "anthropic/claude-sonnet-4",
			Provider: &modelrequest.ProviderConstraints{
				Only:           []string{"anthropic"},
				AllowFallbacks: &allowFallbacks,
				Quantizations:  []string{"bf16"},
			},
			Request: modelrequest.RequestParameters{MaxOutputTokens: &maxTokens},
		},
	}, "aard-case-C1", "http://127.0.0.1:19780/mcp?case_id=case-1&member_id=C1", "token-1")
	if err != nil {
		t.Fatalf("write Pi config: %v", err)
	}
	if model != "anthropic/claude-sonnet-4" {
		t.Fatalf("model = %q", model)
	}
	settings := readJSONMap(t, filepath.Join(home, ".pi", "agent", "settings.json"))
	if settings["defaultProvider"] != "openrouter" || settings["defaultModel"] != "anthropic/claude-sonnet-4" {
		t.Fatalf("settings = %#v", settings)
	}
	models := readJSONMap(t, filepath.Join(home, ".pi", "agent", "models.json"))
	providers := models["providers"].(map[string]any)
	openrouter := providers["openrouter"].(map[string]any)
	modelList := openrouter["models"].([]any)
	modelEntry := modelList[0].(map[string]any)
	if modelEntry["maxTokens"] != float64(maxTokens) {
		t.Fatalf("model entry maxTokens = %#v", modelEntry["maxTokens"])
	}
	compat := modelEntry["compat"].(map[string]any)
	routing := compat["openRouterRouting"].(map[string]any)
	if routing["allow_fallbacks"] != false {
		t.Fatalf("routing = %#v", routing)
	}
	quantizations := routing["quantizations"].([]any)
	if len(quantizations) != 1 || quantizations[0] != "bf16" {
		t.Fatalf("routing quantizations = %#v", routing["quantizations"])
	}
	mcpConfig := readJSONMap(t, filepath.Join(home, ".mcp.json"))
	servers := mcpConfig["mcpServers"].(map[string]any)
	server := servers["aard-case-C1"].(map[string]any)
	if server["url"] != "http://127.0.0.1:19780/mcp?case_id=case-1&member_id=C1" {
		t.Fatalf("mcp server = %#v", server)
	}
	headers := server["headers"].(map[string]any)
	if headers["Authorization"] != "Bearer token-1" {
		t.Fatalf("headers = %#v", headers)
	}
}

func TestWritePiConfigAddsDefaultMaxTokens(t *testing.T) {
	home := t.TempDir()
	_, err := writePiConfig(home, councilRosterEntry{
		MemberID: "C1",
		RequestSpec: &modelrequest.Spec{
			Endpoint: "openrouter",
			Model:    "anthropic/claude-opus-4.6-fast",
		},
	}, "aard-case-C1", "http://127.0.0.1:19780/mcp?case_id=case-1&member_id=C1", "token-1")
	if err != nil {
		t.Fatalf("write Pi config: %v", err)
	}
	models := readJSONMap(t, filepath.Join(home, ".pi", "agent", "models.json"))
	providers := models["providers"].(map[string]any)
	openrouter := providers["openrouter"].(map[string]any)
	modelList := openrouter["models"].([]any)
	modelEntry := modelList[0].(map[string]any)
	want := float64(DefaultCouncilMaxOutputTokens)
	if modelEntry["maxTokens"] != want {
		t.Fatalf("model entry maxTokens = %#v, want %#v", modelEntry["maxTokens"], want)
	}
}

func TestWritePiConfigRejectsMissingRequestSpec(t *testing.T) {
	_, err := writePiConfig(t.TempDir(), councilRosterEntry{
		MemberID: "C1",
		Model:    "openrouter://anthropic/claude-sonnet-4",
	}, "server", "http://example/mcp", "token")
	if err == nil || !strings.Contains(err.Error(), "request_spec") {
		t.Fatalf("error = %v", err)
	}
}

func TestWritePiConfigRejectsUnsupportedRequestFields(t *testing.T) {
	temperature := 0.2
	_, err := writePiConfig(t.TempDir(), councilRosterEntry{
		MemberID: "C1",
		RequestSpec: &modelrequest.Spec{
			Endpoint: "openrouter",
			Model:    "model",
			Request:  modelrequest.RequestParameters{Temperature: &temperature},
		},
	}, "server", "http://example/mcp", "token")
	if err == nil || !strings.Contains(err.Error(), "temperature") {
		t.Fatalf("error = %v", err)
	}
}

func TestResolveOpenClawAuthAutoPrefersCodexAuth(t *testing.T) {
	t.Setenv("OPENAI_API_KEY", "api-key")
	path := writeCodexAuth(t, t.TempDir())
	auth, err := resolveOpenClawAuth(Options{
		OpenClawAuth:          "auto",
		OpenClawCodexAuthPath: path,
	})
	if err != nil {
		t.Fatalf("resolve OpenClaw auth: %v", err)
	}
	if auth.Mode != "codex" || auth.CodexAuthPath != path {
		t.Fatalf("auth = %#v", auth)
	}
}

func TestResolveOpenClawAuthAutoFallsBackToAPIKey(t *testing.T) {
	t.Setenv("OPENAI_API_KEY", "api-key")
	auth, err := resolveOpenClawAuth(Options{
		OpenClawAuth:          "auto",
		OpenClawCodexAuthPath: filepath.Join(t.TempDir(), "missing-auth.json"),
	})
	if err != nil {
		t.Fatalf("resolve OpenClaw auth: %v", err)
	}
	if auth.Mode != "api-key" {
		t.Fatalf("auth = %#v", auth)
	}
}

func TestResolveOpenClawAuthRequiresSelectedCredential(t *testing.T) {
	t.Setenv("OPENAI_API_KEY", "")
	_, err := resolveOpenClawAuth(Options{
		OpenClawAuth:          "auto",
		OpenClawCodexAuthPath: filepath.Join(t.TempDir(), "missing-auth.json"),
	})
	if err == nil || !strings.Contains(err.Error(), "OpenClaw auth requires") {
		t.Fatalf("error = %v", err)
	}
	_, err = resolveOpenClawAuth(Options{OpenClawAuth: "api-key"})
	if err == nil || !strings.Contains(err.Error(), "OPENAI_API_KEY") {
		t.Fatalf("api-key error = %v", err)
	}
}

func TestOpenClawAuthArgsForAPIKey(t *testing.T) {
	state := &runState{openClawAuth: openClawAuthConfig{Mode: "api-key"}}
	args, prefix, err := state.openClawAuthArgs("plaintiff")
	if err != nil {
		t.Fatalf("auth args: %v", err)
	}
	if prefix != "" {
		t.Fatalf("prefix = %q", prefix)
	}
	if strings.Join(args, "\x00") != "-e\x00OPENAI_API_KEY" {
		t.Fatalf("args = %#v", args)
	}
}

func TestOpenClawAuthArgsForCodex(t *testing.T) {
	out := t.TempDir()
	source := writeCodexAuth(t, t.TempDir())
	state := &runState{
		opts:         Options{OutputDir: out},
		openClawAuth: openClawAuthConfig{Mode: "codex", CodexAuthPath: source},
	}
	args, prefix, err := state.openClawAuthArgs("plaintiff")
	if err != nil {
		t.Fatalf("auth args: %v", err)
	}
	for _, want := range []string{
		"unset OPENAI_API_KEY",
		"CODEX_HOME",
		"tokens.access_token",
		"openclaw models auth paste-token --provider openai --profile-id openai:codex",
		"unset codex_token",
	} {
		if !strings.Contains(prefix, want) {
			t.Fatalf("prefix missing %q:\n%s", want, prefix)
		}
	}
	joined := strings.Join(args, "\n")
	if strings.Contains(joined, "OPENAI_API_KEY") {
		t.Fatalf("args contain OPENAI_API_KEY: %#v", args)
	}
	if !strings.Contains(joined, "CODEX_HOME=/aard-codex") {
		t.Fatalf("args missing CODEX_HOME: %#v", args)
	}
	staged := filepath.Join(out, "openclaw-plaintiff-codex", "auth.json")
	raw, err := os.ReadFile(staged)
	if err != nil {
		t.Fatalf("read staged auth: %v", err)
	}
	if !strings.Contains(string(raw), `"auth_mode"`) {
		t.Fatalf("staged auth = %s", string(raw))
	}
	info, err := os.Stat(staged)
	if err != nil {
		t.Fatalf("stat staged auth: %v", err)
	}
	if info.Mode().Perm() != 0o666 {
		t.Fatalf("staged auth mode = %o", info.Mode().Perm())
	}
	homeInfo, err := os.Stat(filepath.Dir(staged))
	if err != nil {
		t.Fatalf("stat staged auth home: %v", err)
	}
	if homeInfo.Mode().Perm() != 0o777 {
		t.Fatalf("staged auth home mode = %o", homeInfo.Mode().Perm())
	}
	if len(state.secretDirs) != 1 {
		t.Fatalf("secret dirs = %#v", state.secretDirs)
	}
	if err := state.cleanupSecrets(); err != nil {
		t.Fatalf("cleanup secrets: %v", err)
	}
	if _, err := os.Stat(staged); !os.IsNotExist(err) {
		t.Fatalf("staged auth still exists: %v", err)
	}
}

func TestOpenClawAuthArgsForCodexUsesAbsoluteMountPath(t *testing.T) {
	oldCwd, err := os.Getwd()
	if err != nil {
		t.Fatalf("get cwd: %v", err)
	}
	tmp := t.TempDir()
	if err := os.Chdir(tmp); err != nil {
		t.Fatalf("chdir: %v", err)
	}
	t.Cleanup(func() {
		if err := os.Chdir(oldCwd); err != nil {
			t.Fatalf("restore cwd: %v", err)
		}
	})

	source := writeCodexAuth(t, t.TempDir())
	state := &runState{
		opts:         Options{OutputDir: "relative-out"},
		openClawAuth: openClawAuthConfig{Mode: "codex", CodexAuthPath: source},
	}
	args, _, err := state.openClawAuthArgs("plaintiff")
	if err != nil {
		t.Fatalf("auth args: %v", err)
	}
	var mount string
	for i := 0; i+1 < len(args); i++ {
		if args[i] == "-v" {
			mount = args[i+1]
			break
		}
	}
	hostPath := strings.SplitN(mount, ":", 2)[0]
	if !filepath.IsAbs(hostPath) {
		t.Fatalf("mount host path is not absolute: %q", mount)
	}
	if err := state.cleanupSecrets(); err != nil {
		t.Fatalf("cleanup secrets: %v", err)
	}
}

func TestEffectiveLawyerTurnTimeoutSeconds(t *testing.T) {
	if got := effectiveLawyerTurnTimeoutSeconds(Options{}); got != DefaultRunLawyerTimeoutSeconds {
		t.Fatalf("default timeout = %d", got)
	}
	if got := effectiveLawyerTurnTimeoutSeconds(Options{LawyerTimeoutSeconds: 123}); got != 123 {
		t.Fatalf("override timeout = %d", got)
	}
}

func TestOpenClawConfigPatchCommandUsesLawyerTimeout(t *testing.T) {
	cmd, err := openClawConfigPatchCommand(900)
	if err != nil {
		t.Fatalf("config patch command: %v", err)
	}
	start := strings.Index(cmd, "\n")
	end := strings.Index(cmd, "\nJSON\n")
	if start < 0 || end < 0 || end <= start {
		t.Fatalf("command does not contain JSON heredoc: %q", cmd)
	}
	raw := cmd[start+1 : end]
	var patch map[string]any
	if err := json.Unmarshal([]byte(raw), &patch); err != nil {
		t.Fatalf("decode patch: %v", err)
	}
	codex := patch["plugins"].(map[string]any)["entries"].(map[string]any)["codex"].(map[string]any)
	if codex["enabled"] != true {
		t.Fatalf("codex enabled = %#v", codex["enabled"])
	}
	appServer := codex["config"].(map[string]any)["appServer"].(map[string]any)
	for _, name := range []string{"turnCompletionIdleTimeoutMs", "postToolRawAssistantCompletionIdleTimeoutMs"} {
		if appServer[name] != float64(900000) {
			t.Fatalf("%s = %#v", name, appServer[name])
		}
	}
	if !strings.Contains(cmd, "openclaw config patch --file /tmp/aard-openclaw-config.json") {
		t.Fatalf("command = %q", cmd)
	}
}

func TestApplyDefaultsOpenClawStartDelay(t *testing.T) {
	if got := applyDefaults(Options{OpenClawStartDelaySeconds: -1}).OpenClawStartDelaySeconds; got != defaultOpenClawStartDelay {
		t.Fatalf("default start delay = %d", got)
	}
	if got := applyDefaults(Options{OpenClawStartDelaySeconds: 0}).OpenClawStartDelaySeconds; got != 0 {
		t.Fatalf("zero start delay = %d", got)
	}
	if got := applyDefaults(Options{OpenClawStartDelaySeconds: 27}).OpenClawStartDelaySeconds; got != 27 {
		t.Fatalf("override start delay = %d", got)
	}
}

func TestApplyDefaultsRunTurnTimeouts(t *testing.T) {
	opts := applyDefaults(Options{})
	if opts.CouncilTimeoutSeconds != DefaultRunCouncilTimeoutSeconds {
		t.Fatalf("default council timeout = %d", opts.CouncilTimeoutSeconds)
	}
	if opts.LawyerTimeoutSeconds != DefaultRunLawyerTimeoutSeconds {
		t.Fatalf("default lawyer timeout = %d", opts.LawyerTimeoutSeconds)
	}
	opts = applyDefaults(Options{CouncilTimeoutSeconds: 123, LawyerTimeoutSeconds: 456})
	if opts.CouncilTimeoutSeconds != 123 || opts.LawyerTimeoutSeconds != 456 {
		t.Fatalf("timeouts = council %d lawyer %d", opts.CouncilTimeoutSeconds, opts.LawyerTimeoutSeconds)
	}
}

func TestApplyDefaultsOpenClawNetworkHostMCPHost(t *testing.T) {
	opts := applyDefaults(Options{OpenClawNetwork: "host"})
	if opts.DockerMCPHost != "127.0.0.1" {
		t.Fatalf("DockerMCPHost = %q", opts.DockerMCPHost)
	}
	opts = applyDefaults(Options{OpenClawNetwork: "host", DockerMCPHost: "custom"})
	if opts.DockerMCPHost != "custom" {
		t.Fatalf("custom DockerMCPHost = %q", opts.DockerMCPHost)
	}
	opts = applyDefaults(Options{})
	if opts.DockerMCPHost != "host.docker.internal" {
		t.Fatalf("default DockerMCPHost = %q", opts.DockerMCPHost)
	}
}

func TestOpenClawDockerRunArgsNetworkHost(t *testing.T) {
	args := openClawDockerRunArgs(Options{OpenClawNetwork: "host"}, "aard-test")
	joined := strings.Join(args, "\n")
	for _, want := range []string{"run", "--rm", "--name\naard-test", "--network\nhost"} {
		if !strings.Contains(joined, want) {
			t.Fatalf("args missing %q: %#v", want, args)
		}
	}
	if strings.Contains(joined, "host.docker.internal") {
		t.Fatalf("host-network args contain add-host: %#v", args)
	}
}

func TestValidateOptionsRejectsInvalidOpenClawNetwork(t *testing.T) {
	dir := t.TempDir()
	instruction := filepath.Join(dir, "instruction.md")
	if err := os.WriteFile(instruction, []byte("instruction"), 0o600); err != nil {
		t.Fatal(err)
	}
	t.Setenv("OPENROUTER_API_KEY", "key")
	err := validateOptions(Options{
		ComplaintPath:           "complaint.md",
		OutputDir:               dir,
		CaseID:                  "case",
		AutoLawyers:             DefaultAutoLawyers,
		CouncilOutputLimitBytes: 1,
		LawyerInstructionsPath:  instruction,
		RemoteLawyerSkillPath:   instruction,
		CouncilInstructionsPath: instruction,
		OpenClawNetwork:         "bridge",
	})
	if err == nil || !strings.Contains(err.Error(), "invalid OpenClaw network") {
		t.Fatalf("validateOptions error = %v", err)
	}
}

func TestApplyDefaultsCouncilOutputLimit(t *testing.T) {
	if got := applyDefaults(Options{}).CouncilOutputLimitBytes; got != DefaultCouncilOutputLimitBytes {
		t.Fatalf("default council output limit = %d", got)
	}
	if got := applyDefaults(Options{CouncilOutputLimitBytes: 123}).CouncilOutputLimitBytes; got != 123 {
		t.Fatalf("council output limit override = %d", got)
	}
}

func TestCouncilProcessOutputSizeCountsLogs(t *testing.T) {
	dir := t.TempDir()
	stdoutPath := filepath.Join(dir, "pi-C1.stdout")
	stderrPath := filepath.Join(dir, "pi-C1.stderr")
	if err := os.WriteFile(stdoutPath, []byte("abcdef"), 0o644); err != nil {
		t.Fatalf("write stdout: %v", err)
	}
	if err := os.WriteFile(stderrPath, []byte("xyz"), 0o644); err != nil {
		t.Fatalf("write stderr: %v", err)
	}
	size, err := councilProcessOutputSize(&processRecord{
		name:       "pi-C1",
		stdoutPath: stdoutPath,
		stderrPath: stderrPath,
	})
	if err != nil {
		t.Fatalf("council process output size: %v", err)
	}
	if size.Stdout != 6 || size.Stderr != 3 || size.Total != 9 {
		t.Fatalf("size = %#v", size)
	}
}

func TestCouncilProcessOutputSizeUsesStdoutCounter(t *testing.T) {
	dir := t.TempDir()
	stdoutPath := filepath.Join(dir, "pi-C1.stdout")
	stderrPath := filepath.Join(dir, "pi-C1.stderr")
	if err := os.WriteFile(stdoutPath, []byte("abc"), 0o644); err != nil {
		t.Fatalf("write stdout: %v", err)
	}
	if err := os.WriteFile(stderrPath, []byte("xy"), 0o644); err != nil {
		t.Fatalf("write stderr: %v", err)
	}
	var out bytes.Buffer
	counter := newProcessOutputCounter(&out)
	if _, err := counter.Write([]byte("abcdef")); err != nil {
		t.Fatalf("write counter: %v", err)
	}
	size, err := councilProcessOutputSize(&processRecord{
		name:          "pi-C1",
		stdoutPath:    stdoutPath,
		stderrPath:    stderrPath,
		stdoutCounter: counter,
	})
	if err != nil {
		t.Fatalf("council process output size: %v", err)
	}
	if size.Stdout != 6 || size.Stderr != 2 || size.Total != 8 {
		t.Fatalf("size = %#v", size)
	}
}

func TestMonitorCouncilOutputKillsProcessOverLimit(t *testing.T) {
	dir := t.TempDir()
	stdoutPath := filepath.Join(dir, "pi-C1.stdout")
	stderrPath := filepath.Join(dir, "pi-C1.stderr")
	stdout, err := os.Create(stdoutPath)
	if err != nil {
		t.Fatalf("create stdout: %v", err)
	}
	stderr, err := os.Create(stderrPath)
	if err != nil {
		t.Fatalf("create stderr: %v", err)
	}
	if _, err := stdout.WriteString("abcdef"); err != nil {
		t.Fatalf("write stdout: %v", err)
	}
	cmd := exec.Command("sleep", "60")
	cmd.Stdout = stdout
	cmd.Stderr = stderr
	if err := cmd.Start(); err != nil {
		t.Fatalf("start sleep: %v", err)
	}
	proc := &processRecord{
		name:       "pi-C1",
		kind:       "podman",
		command:    cmd,
		done:       make(chan error, 1),
		stdoutPath: stdoutPath,
		stderrPath: stderrPath,
		finished:   make(chan struct{}),
	}
	go func() {
		waitErr := cmd.Wait()
		closeOut := stdout.Close()
		closeErr := stderr.Close()
		proc.markExited()
		proc.done <- errors.Join(waitErr, closeOut, closeErr)
	}()
	t.Cleanup(func() {
		if !proc.isExited() {
			_ = cmd.Process.Kill()
			<-proc.finished
		}
	})

	state := &runState{
		opts:      Options{CouncilOutputLimitBytes: 5},
		agentErrs: make(chan error, 1),
	}
	state.monitorCouncilOutput(context.Background(), proc, councilProcessTarget{
		memberID:      "C1",
		opportunityID: "deliberation:1:C1",
	}, 10*time.Millisecond)
	select {
	case <-proc.finished:
	case err := <-state.agentErrs:
		t.Fatalf("agent error: %v", err)
	case <-time.After(2 * time.Second):
		t.Fatalf("process was not killed")
	}
	reason, message, details := proc.forcedFailure()
	if reason != councilFailureOutputLimit {
		t.Fatalf("forced reason = %q", reason)
	}
	if !strings.Contains(message, "exceeded the output limit") {
		t.Fatalf("message = %q", message)
	}
	if details["output_bytes"] != int64(6) || details["output_limit_bytes"] != int64(5) {
		t.Fatalf("details = %#v", details)
	}
}

func TestPiMessageUpdateTailFilterCompactsAccumulatedThinking(t *testing.T) {
	var filter piMessageUpdateTailFilter
	first := []byte(`{"type":"message_update","assistantMessageEvent":{"type":"thinking_start","contentIndex":0,"partial":{"responseId":"r1","content":[{"type":"thinking","thinking":"abc","thinkingSignature":"reasoning"}]}},"message":{"responseId":"r1","content":[{"type":"thinking","thinking":"abc","thinkingSignature":"reasoning"}]}}`)
	if got := filter.filterLine(first); string(got) != string(first) {
		t.Fatalf("first update changed:\n%s", got)
	}
	second := []byte(`{"type":"message_update","assistantMessageEvent":{"type":"thinking_delta","contentIndex":0,"delta":"def","partial":{"responseId":"r1","content":[{"type":"thinking","thinking":"abcdef","thinkingSignature":"reasoning"}]}},"message":{"responseId":"r1","content":[{"type":"thinking","thinking":"abcdef","thinkingSignature":"reasoning"}]}}`)
	got := filter.filterLine(second)
	if string(got) == string(second) {
		t.Fatalf("second update was not compacted")
	}

	var event map[string]any
	if err := json.Unmarshal(got, &event); err != nil {
		t.Fatalf("unmarshal filtered event: %v", err)
	}
	logFilter, ok := event["aard_log_filter"].(map[string]any)
	if !ok {
		t.Fatalf("missing aard_log_filter: %#v", event)
	}
	if logFilter["message"] != repeatedMessageUpdateLogFilterMessage {
		t.Fatalf("filter message = %#v", logFilter["message"])
	}
	if logFilter["dropped_prefix_bytes"] != float64(3) || logFilter["tail_bytes"] != float64(3) {
		t.Fatalf("filter details = %#v", logFilter)
	}

	assistantEvent, ok := piMapValue(event["assistantMessageEvent"])
	if !ok {
		t.Fatalf("missing assistantMessageEvent")
	}
	partial, ok := piMapValue(assistantEvent["partial"])
	if !ok {
		t.Fatalf("missing partial")
	}
	_, value, ok := piContentString(partial, 0)
	if !ok || value != "def" {
		t.Fatalf("partial content = %q, %v", value, ok)
	}
	message, ok := piMapValue(event["message"])
	if !ok {
		t.Fatalf("missing message")
	}
	_, value, ok = piContentString(message, 0)
	if !ok || value != "def" {
		t.Fatalf("message content = %q, %v", value, ok)
	}
}

func TestPiMessageUpdateTailFilterLeavesNonPrefixUpdate(t *testing.T) {
	var filter piMessageUpdateTailFilter
	first := []byte(`{"type":"message_update","assistantMessageEvent":{"type":"thinking_start","contentIndex":0,"partial":{"responseId":"r1","content":[{"type":"thinking","thinking":"abc"}]}}}`)
	second := []byte(`{"type":"message_update","assistantMessageEvent":{"type":"thinking_delta","contentIndex":0,"partial":{"responseId":"r1","content":[{"type":"thinking","thinking":"zabc"}]}}}`)
	_ = filter.filterLine(first)
	if got := filter.filterLine(second); string(got) != string(second) {
		t.Fatalf("non-prefix update changed:\n%s", got)
	}
}

func TestPiTailLogWriterHandlesChunkedLines(t *testing.T) {
	var out bytes.Buffer
	writer := newPiTailLogWriter(&out)
	first := `{"type":"message_update","assistantMessageEvent":{"type":"thinking_start","contentIndex":0,"partial":{"responseId":"r1","content":[{"type":"thinking","thinking":"abc"}]}}}`
	second := `{"type":"message_update","assistantMessageEvent":{"type":"thinking_delta","contentIndex":0,"partial":{"responseId":"r1","content":[{"type":"thinking","thinking":"abcdef"}]}}}`
	raw := []byte(first + "\n" + second + "\n")
	if _, err := writer.Write(raw[:17]); err != nil {
		t.Fatalf("write first chunk: %v", err)
	}
	if _, err := writer.Write(raw[17:]); err != nil {
		t.Fatalf("write second chunk: %v", err)
	}
	if err := writer.Flush(); err != nil {
		t.Fatalf("flush: %v", err)
	}
	got := out.String()
	if !strings.Contains(got, repeatedMessageUpdateLogFilterMessage) {
		t.Fatalf("filtered log missing marker:\n%s", got)
	}
	if !strings.Contains(got, `"thinking":"def"`) {
		t.Fatalf("filtered log missing tail content:\n%s", got)
	}
	if !strings.Contains(got, first) {
		t.Fatalf("first line changed:\n%s", got)
	}
}

func TestAutoLawyerRoles(t *testing.T) {
	tests := []struct {
		mode string
		want string
	}{
		{mode: "both", want: "plaintiff,defendant"},
		{mode: "plaintiff", want: "plaintiff"},
		{mode: "defendant", want: "defendant"},
	}
	for _, tc := range tests {
		got, err := autoLawyerRoles(tc.mode)
		if err != nil {
			t.Fatalf("%s: %v", tc.mode, err)
		}
		if strings.Join(got, ",") != tc.want {
			t.Fatalf("%s roles = %#v", tc.mode, got)
		}
	}
	if _, err := autoLawyerRoles("none"); err == nil {
		t.Fatalf("expected invalid mode error")
	}
	if got := strings.Join(manualLawyerRoles("defendant"), ","); got != "plaintiff" {
		t.Fatalf("manual roles = %q", got)
	}
}

func TestPublicMCPBaseAndManualAddressValidation(t *testing.T) {
	base, err := publicMCPBase("http://aard.example:8001/", "0.0.0.0:1234")
	if err != nil {
		t.Fatalf("public base: %v", err)
	}
	if base != "http://aard.example:8001" {
		t.Fatalf("base = %q", base)
	}
	if err := validateManualLawyerAddress("", "0.0.0.0:1234"); err == nil {
		t.Fatalf("expected wildcard listen error")
	}
	if err := validateManualLawyerAddress("", "192.0.2.10:1234"); err != nil {
		t.Fatalf("non-wildcard listen: %v", err)
	}
}

func TestWriteRemoteLawyerSkill(t *testing.T) {
	dir := t.TempDir()
	templatePath := filepath.Join(dir, "remote.md.tmpl")
	if err := os.WriteFile(templatePath, []byte("case={{.CaseID}} role={{.RoleID}} server={{.MCPServer}} url={{.MCPURL}} json={{.MCPJSON}}\n"), 0o644); err != nil {
		t.Fatalf("write template: %v", err)
	}
	state := &runState{
		opts: Options{
			CaseID:                "case-1",
			OutputDir:             dir,
			RemoteLawyerSkillPath: templatePath,
		},
		mcpPublicBase: "http://aard.example:8001",
		token:         "token-1",
	}
	if err := state.writeRemoteLawyerSkill("plaintiff"); err != nil {
		t.Fatalf("write remote skill: %v", err)
	}
	path := filepath.Join(dir, "openclaw-plaintiff-lawyer-skill.md")
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read skill: %v", err)
	}
	text := string(raw)
	for _, want := range []string{"case=case-1", "role=plaintiff", "http://aard.example:8001/mcp?case_id=case-1&role_id=plaintiff", "Bearer token-1"} {
		if !strings.Contains(text, want) {
			t.Fatalf("skill missing %q: %s", want, text)
		}
	}
	info, err := os.Stat(path)
	if err != nil {
		t.Fatalf("stat skill: %v", err)
	}
	if info.Mode().Perm() != 0o600 {
		t.Fatalf("skill mode = %o", info.Mode().Perm())
	}
}

func TestWriteRunSummaryIncludesOpenClawStartDelay(t *testing.T) {
	dir := t.TempDir()
	if err := writeRunSummary(dir, Result{
		CaseID: "case-1",
		RunID:  "run-1",
		Status: "ok",
	}, Options{OpenClawStartDelaySeconds: 15, AutoLawyers: "defendant", MCPPublicBaseURL: "http://aard.example:8001"}); err != nil {
		t.Fatalf("write run summary: %v", err)
	}
	summary := readJSONMap(t, filepath.Join(dir, "local-run.json"))
	if summary["openclaw_lawyer_start_delay_seconds"] != float64(15) {
		t.Fatalf("summary = %#v", summary)
	}
	if summary["auto_lawyers"] != "defendant" || summary["mcp_public_base_url"] != "http://aard.example:8001" {
		t.Fatalf("summary = %#v", summary)
	}
}

func TestOutputSubdirReturnsAbsolutePath(t *testing.T) {
	got, err := outputSubdir("relative-out", "pi-C1")
	if err != nil {
		t.Fatalf("output subdir: %v", err)
	}
	if !filepath.IsAbs(got) {
		t.Fatalf("path is not absolute: %q", got)
	}
	if !strings.HasSuffix(got, filepath.Join("relative-out", "pi-C1")) {
		t.Fatalf("path = %q", got)
	}
}

func TestResolveListenAddrAllocatesPort(t *testing.T) {
	addr, err := resolveListenAddr("0.0.0.0:0", "127.0.0.1")
	if err != nil {
		t.Fatalf("resolve listen addr: %v", err)
	}
	host, port, err := net.SplitHostPort(addr)
	if err != nil {
		t.Fatalf("split listen addr: %v", err)
	}
	if host != "0.0.0.0" || port == "0" || port == "" {
		t.Fatalf("addr = %q", addr)
	}
}

func TestContainerNameSanitizesAndBounds(t *testing.T) {
	got := containerName("AARD/case with spaces and @ symbols " + strings.Repeat("x", 100))
	if len(got) > 63 {
		t.Fatalf("container name length = %d", len(got))
	}
	if strings.ContainsAny(got, "/ @") {
		t.Fatalf("container name = %q", got)
	}
}

func readJSONMap(t *testing.T, path string) map[string]any {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var out map[string]any
	if err := json.Unmarshal(raw, &out); err != nil {
		t.Fatalf("decode %s: %v", path, err)
	}
	return out
}

func writeCodexAuth(t *testing.T, dir string) string {
	t.Helper()
	path := filepath.Join(dir, "auth.json")
	raw := []byte(`{"auth_mode":"chatgpt","tokens":{"access_token":"test","refresh_token":"test"}}` + "\n")
	if err := os.WriteFile(path, raw, 0o600); err != nil {
		t.Fatalf("write Codex auth: %v", err)
	}
	return path
}
