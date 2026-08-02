package localrun

import (
	"context"
	"encoding/json"
	"flag"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"syscall"
	"testing"
	"time"

	"adjudication/common/modelrequest"
)

var pairedCoreBinDir = flag.String("carve-bin-dir", "", "Directory containing paired carve executables")
var pairedCoreRoot = flag.String("carve-root", "", "Paired carve checkout root")

func TestCoreCaseArgsUseProcessInterface(t *testing.T) {
	complaintArgs := coreCaseArgs(Options{
		ComplaintPath:        "/case/complaint.md",
		OutputDir:            "/out",
		Court:                "court.json",
		Model:                "runtime-model",
		DigestModel:          "report-model",
		NonJurorModel:        "non-juror-model",
		PlaintiffModel:       "plaintiff-model",
		DefendantModel:       "defendant-model",
		JudgeModel:           "judge-model",
		ClerkModel:           "clerk-model",
		PlannerModel:         "planner-model",
		Temperature:          "0.2",
		NonJurorTemperature:  "0.3",
		JurorTemperature:     "0.4",
		JurorPersonasPath:    "/case/jurors.jsonl",
		TrialMode:            "jury",
		SkipVoirDire:         true,
		JurorCount:           8,
		MinimumConcurring:    6,
		UnanimousRequired:    "false",
		Online:               true,
		LawyerTimeoutSeconds: 90,
		JurorTimeoutSeconds:  120,
		TimeoutSeconds:       30,
		MaxResponseBytes:     4096,
		InvalidAttemptLimit:  2,
		EnginePath:           "/bin/adcengine",
		RunID:                "run-1",
		CaseID:               "case-1",
	}, "127.0.0.1:9001")
	joined := strings.Join(complaintArgs, "\x00")
	for _, want := range []string{
		"case", "--complaint\x00/case/complaint.md", "--out-dir\x00/out",
		"--case-id\x00case-1", "--run-id\x00run-1", "--caseapi-addr\x00127.0.0.1:9001",
		"--court\x00court.json", "--model\x00runtime-model", "--report-model\x00report-model",
		"--non-juror-model\x00non-juror-model", "--plaintiff-model\x00plaintiff-model",
		"--defendant-model\x00defendant-model", "--judge-model\x00judge-model",
		"--clerk-model\x00clerk-model", "--planner-model\x00planner-model",
		"--temperature\x000.2", "--non-juror-temperature\x000.3", "--juror-temperature\x000.4",
		"--juror-personas\x00/case/jurors.jsonl", "--trial-mode\x00jury", "--skip-voir-dire",
		"--juror-count\x008", "--minimum-concurring\x006", "--unanimous-required\x00false",
		"--roleapi-timeout-seconds\x00120", "--timeout-seconds\x0030",
		"--max-response-bytes\x004096", "--invalid-attempt-limit\x002",
		"--engine\x00/bin/adcengine", "--online",
	} {
		if !strings.Contains(joined, want) {
			t.Fatalf("complaint core args lack %q: %#v", want, complaintArgs)
		}
	}
	if got := strings.Count(joined, "--external-role\x00"); got != 3 {
		t.Fatalf("complaint external role count = %d, want 3: %#v", got, complaintArgs)
	}

	scenarioArgs := coreCaseArgs(Options{
		ScenarioPath:      "/case/scenario.json",
		OutputDir:         "/out",
		DigestModel:       "report-model",
		Offline:           true,
		RunID:             "run-2",
		CaseID:            "case-2",
		EnginePath:        "/bin/adcengine",
		JurorCount:        6,
		MinimumConcurring: 6,
	}, "127.0.0.1:9002")
	joined = strings.Join(scenarioArgs, "\x00")
	for _, want := range []string{
		"scenario", "--scenario\x00/case/scenario.json", "--output\x00/out/run.json",
		"--runtime\x00/out/runtime.json", "--events\x00/out/events.ndjson",
		"--db\x00/out/run.db", "--transcript\x00/out/transcript.md", "--digest\x00/out/digest.md",
		"--allow-assertion-failures", "--report-model\x00report-model", "--offline",
		"--case-id\x00case-2", "--run-id\x00run-2", "--caseapi-addr\x00127.0.0.1:9002",
	} {
		if !strings.Contains(joined, want) {
			t.Fatalf("scenario core args lack %q: %#v", want, scenarioArgs)
		}
	}
	if got := strings.Count(joined, "--external-role\x00"); got != 3 {
		t.Fatalf("scenario external role count = %d, want 3: %#v", got, scenarioArgs)
	}
}

func TestStartCoreCaseReadsFreshResult(t *testing.T) {
	dir := t.TempDir()
	logDir := filepath.Join(dir, "logs")
	if err := os.MkdirAll(logDir, 0o755); err != nil {
		t.Fatalf("mkdir logs: %v", err)
	}
	core := filepath.Join(dir, "adc-core")
	script := `#!/bin/sh
set -eu
out_dir=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out-dir) out_dir=$2; shift 2 ;;
    *) shift ;;
  esac
done
printf '{"scenario":"fake","assertions":[],"turn_logs":[],"final_state":{"status":"ok"},"extra":"preserved"}\n' > "$out_dir/run.json"
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
	if outcome.result.Scenario != "fake" || outcome.result.FinalState["status"] != "ok" {
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
	if err := os.WriteFile(filepath.Join(dir, "run.json"), []byte(`{"scenario":"stale"}`+"\n"), 0o644); err != nil {
		t.Fatalf("write stale result: %v", err)
	}
	core := filepath.Join(dir, "adc-core")
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
	coreCommand := filepath.Join(binDir, "adc")
	enginePath := filepath.Join(carveRoot, "adc", "engine", ".lake", "build", "bin", "adcengine")
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
	scenarioPath := filepath.Join(dir, "scenario.json")
	if err := writeJSONFile(scenarioPath, map[string]any{
		"name":       "paired-adc",
		"court_name": "United States District",
		"roles": []map[string]any{{
			"name": "plaintiff", "instructions": "Paired role.", "allowed_actions": []string{"get_case"},
		}},
		"turns": []map[string]any{{
			"role": "plaintiff", "prompt": "Wait for the paired client.", "max_steps": 1,
			"allowed_actions": []string{"get_case"},
		}},
	}); err != nil {
		t.Fatalf("write scenario: %v", err)
	}
	t.Setenv("OPENAI_API_KEY", "paired-key")
	caseAPIAddr, err := resolveListenAddr("127.0.0.1:0", "127.0.0.1")
	if err != nil {
		t.Fatalf("resolve case API address: %v", err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	done, err := startCoreCase(ctx, Options{
		CoreCommand:    coreCommand,
		CoreWorkingDir: filepath.Join(carveRoot, "adc"),
		ScenarioPath:   scenarioPath,
		OutputDir:      dir,
		EnginePath:     enginePath,
		RunID:          "run-paired-adc",
		CaseID:         "paired-adc",
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
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, baseURL+"/roleapi/v1/status?case_id=paired-adc&role_id=plaintiff", nil)
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

func TestMCPURLIncludesCaseRoleAndPrincipal(t *testing.T) {
	t.Parallel()

	raw := mcpURL("http://127.0.0.1:8001/", "case 1", map[string]string{
		"role_id":      "juror",
		"principal_id": "J1",
	})
	parsed, err := url.Parse(raw)
	if err != nil {
		t.Fatalf("parse MCP URL: %v", err)
	}
	if parsed.Scheme != "http" || parsed.Host != "127.0.0.1:8001" || parsed.Path != "/mcp" {
		t.Fatalf("URL = %q", raw)
	}
	values := parsed.Query()
	if values.Get("case_id") != "case 1" {
		t.Fatalf("case_id = %q", values.Get("case_id"))
	}
	if values.Get("role_id") != "juror" {
		t.Fatalf("role_id = %q", values.Get("role_id"))
	}
	if values.Get("principal_id") != "J1" {
		t.Fatalf("principal_id = %q", values.Get("principal_id"))
	}
}

func TestAutoLawyerRoles(t *testing.T) {
	t.Parallel()

	cases := map[string][]string{
		"both":      {"plaintiff", "defendant"},
		"plaintiff": {"plaintiff"},
		"defendant": {"defendant"},
	}
	for mode, want := range cases {
		got, err := autoLawyerRoles(mode)
		if err != nil {
			t.Fatalf("autoLawyerRoles(%q): %v", mode, err)
		}
		if len(got) != len(want) {
			t.Fatalf("autoLawyerRoles(%q) len = %d, want %d", mode, len(got), len(want))
		}
		for i := range want {
			if got[i] != want[i] {
				t.Fatalf("autoLawyerRoles(%q)[%d] = %q, want %q", mode, i, got[i], want[i])
			}
		}
	}
	if _, err := autoLawyerRoles("none"); err == nil {
		t.Fatalf("autoLawyerRoles accepted invalid mode")
	}
}

func TestOpenClawCodexAuthCommandImportsAccessToken(t *testing.T) {
	t.Parallel()

	cmd := openClawCodexAuthCommand()
	for _, want := range []string{
		"unset OPENAI_API_KEY",
		"CODEX_HOME",
		"auth.json",
		"tokens.access_token",
		"openclaw models auth paste-token --provider openai --profile-id openai:codex",
		"unset codex_token",
	} {
		if !strings.Contains(cmd, want) {
			t.Fatalf("auth command missing %q:\n%s", want, cmd)
		}
	}
}

func TestStageOpenClawCodexAuthUsesContainerReadableModes(t *testing.T) {
	t.Parallel()

	root := t.TempDir()
	authPath := filepath.Join(root, "auth.json")
	if err := os.WriteFile(authPath, []byte(`{"tokens":{"access_token":"token-1"}}`), 0o600); err != nil {
		t.Fatalf("write auth: %v", err)
	}
	state := &runState{
		opts: Options{
			OutputDir: root,
		},
		openClawAuth: openClawAuthConfig{
			Mode:          "codex",
			CodexAuthPath: authPath,
		},
	}
	home, err := state.stageOpenClawCodexAuth("plaintiff")
	if err != nil {
		t.Fatalf("stage auth: %v", err)
	}
	homeInfo, err := os.Stat(home)
	if err != nil {
		t.Fatalf("stat home: %v", err)
	}
	if got := homeInfo.Mode().Perm(); got != 0o777 {
		t.Fatalf("home mode = %o, want 777", got)
	}
	authInfo, err := os.Stat(filepath.Join(home, "auth.json"))
	if err != nil {
		t.Fatalf("stat staged auth: %v", err)
	}
	if got := authInfo.Mode().Perm(); got != 0o666 {
		t.Fatalf("auth mode = %o, want 666", got)
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
	args := openClawDockerRunArgs(Options{OpenClawNetwork: "host"}, "adc-test")
	joined := strings.Join(args, "\n")
	for _, want := range []string{"run", "--rm", "--name\nadc-test", "--network\nhost"} {
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
	file := filepath.Join(dir, "input.md")
	if err := os.WriteFile(file, []byte("input"), 0o600); err != nil {
		t.Fatal(err)
	}
	t.Setenv("OPENROUTER_API_KEY", "key")
	err := validateOptions(Options{
		ScenarioPath:           file,
		OutputDir:              dir,
		CaseID:                 "case",
		JurorPersonasPath:      file,
		AutoLawyers:            DefaultAutoLawyers,
		LawyerInstructionsPath: file,
		RemoteLawyerSkillPath:  file,
		JurorInstructionsPath:  file,
		OpenClawNetwork:        "bridge",
	})
	if err == nil || !strings.Contains(err.Error(), "invalid OpenClaw network") {
		t.Fatalf("validateOptions error = %v", err)
	}
}

func TestIsConnectionRefused(t *testing.T) {
	t.Parallel()

	err := &url.Error{
		Op:  "Get",
		URL: "http://127.0.0.1:1/roleapi/v1/status",
		Err: &os.SyscallError{Syscall: "connect", Err: syscall.ECONNREFUSED},
	}
	if !isConnectionRefused(err) {
		t.Fatalf("isConnectionRefused returned false for ECONNREFUSED")
	}
	if isConnectionRefused(os.ErrNotExist) {
		t.Fatalf("isConnectionRefused returned true for unrelated error")
	}
}

func TestWritePiConfigUsesFullOpenRouterSpec(t *testing.T) {
	t.Parallel()

	spec, err := modelrequest.ParseJSON([]byte(`{
		"endpoint":"openrouter",
		"model":"anthropic/claude-3.5-sonnet",
		"provider":{"only":["deepinfra"],"allow_fallbacks":false,"require_parameters":true,"quantizations":["bf16"]},
		"persona":"personas/j1.txt"
	}`))
	if err != nil {
		t.Fatalf("parse request spec: %v", err)
	}
	home := t.TempDir()
	model, err := writePiConfig(home, activeJurorOpportunity{
		principalID: "J1",
		requestSpec: &spec,
	}, "adc", "http://host/mcp?case_id=c&role_id=juror&principal_id=J1", "token-1")
	if err != nil {
		t.Fatalf("writePiConfig: %v", err)
	}
	if model != "anthropic/claude-3.5-sonnet" {
		t.Fatalf("model = %q", model)
	}

	models := readJSONMap(t, filepath.Join(home, ".pi", "agent", "models.json"))
	openrouter := models["providers"].(map[string]any)["openrouter"].(map[string]any)
	entries := openrouter["models"].([]any)
	entry := entries[0].(map[string]any)
	if entry["maxTokens"].(float64) != float64(DefaultJurorMaxOutputTokens) {
		t.Fatalf("maxTokens = %#v", entry["maxTokens"])
	}
	routing := entry["compat"].(map[string]any)["openRouterRouting"].(map[string]any)
	if routing["allow_fallbacks"] != false {
		t.Fatalf("allow_fallbacks = %#v", routing["allow_fallbacks"])
	}
	if routing["require_parameters"] != true {
		t.Fatalf("require_parameters = %#v", routing["require_parameters"])
	}
	if routing["only"].([]any)[0].(string) != "deepinfra" {
		t.Fatalf("provider.only = %#v", routing["only"])
	}
	if routing["quantizations"].([]any)[0].(string) != "bf16" {
		t.Fatalf("provider.quantizations = %#v", routing["quantizations"])
	}

	mcp := readJSONMap(t, filepath.Join(home, ".mcp.json"))
	server := mcp["mcpServers"].(map[string]any)["adc"].(map[string]any)
	if server["transport"].(string) != "streamable-http" {
		t.Fatalf("MCP transport = %#v", server["transport"])
	}
	if server["headers"].(map[string]any)["Authorization"].(string) != "Bearer token-1" {
		t.Fatalf("MCP auth header = %#v", server["headers"])
	}
}

func TestJurorInstructionsStopAfterActiveOpportunity(t *testing.T) {
	t.Parallel()

	text, err := renderInstructions(DefaultJurorInstructionsPath(), instructionData{
		CaseID:           "case-1",
		PrincipalID:      "J2",
		OpportunityID:    "opp-1",
		OpportunityPhase: "deliberation",
		MCPServer:        "adc",
	})
	if err != nil {
		t.Fatalf("renderInstructions: %v", err)
	}
	for _, want := range []string{
		"opportunity opp-1 in phase deliberation",
		"After `adc_submit_decision` returns `ok: true`, stop.",
		"Do not wait for another juror opportunity.",
		"ADC will start a new Pi process if juror J2 later receives another opportunity.",
		"the prompt includes the trial transcript from openings through closings",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("juror instructions missing %q:\n%s", want, text)
		}
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
