package compat

import (
	"bufio"
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
	"testing"
	"time"
)

var blackBoxFixtureDirs sync.Map

var serviceBinDir = flag.String("service-bin-dir", "", "Directory containing service executables")
var carveBinDir = flag.String("carve-bin-dir", "", "Directory containing carve executables")
var carveRoot = flag.String("carve-root", "", "Carve checkout root")

func TestBlackBoxLawyerAttemptFailureThroughService(t *testing.T) {
	fx := newBlackBoxFixture(t)
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	svc := fx.startService(ctx, t)
	defer svc.kill(t)

	caseID := "bb-lawyer-service"
	outDir := svc.outputDir("service-lawyer-case")
	createCase(ctx, t, svc.baseURL, map[string]any{
		"case_id":                 caseID,
		"run_id":                  "run-" + caseID,
		"complaint_path":          fx.complaintPath,
		"out_dir":                 outDir,
		"policy_path":             fx.policyPath,
		"council_pool_path":       fx.councilPoolPath,
		"common_root":             fx.commonRoot,
		"engine_path":             fx.enginePath,
		"invalid_attempt_limit":   1,
		"lawyer_timeout_seconds":  30,
		"council_timeout_seconds": 10,
	})

	ready := waitLawyerReady(ctx, t, svc.baseURL+"/lawyerapi/v1", caseID, "plaintiff")
	postLawyerTool(ctx, t, svc.baseURL+"/lawyerapi/v1", map[string]any{
		"case_id":        caseID,
		"role_id":        "plaintiff",
		"opportunity_id": stringAt(ready, "turn", "opportunity_id"),
		"tool":           "submit_decision",
		"arguments": map[string]any{
			"kind":      "tool",
			"tool_name": "record_opening_statement",
			"payload":   map[string]any{},
		},
	}, false)

	result := pollResultStatus(ctx, t, svc.baseURL, caseID, "failed")
	assertFailure(t, mapAny(result["failure"]), "plaintiff", "attempts_exhausted")
	record := pollCaseRecordStatus(ctx, t, svc.baseURL, caseID, "failed")
	assertServiceRecord(t, record, "failed", "failed")

	completedRead := getJSON(ctx, t, svc.baseURL+"/lawyerapi/v1/result?case_id="+url.QueryEscape(caseID)+"&role_id=observer")
	assertString(t, completedRead, "status", "failed")
	assertFailure(t, mapAny(completedRead["failure"]), "plaintiff", "attempts_exhausted")
	assertEventTypes(t, filepath.Join(outDir, "events.ndjson"), "opportunity_failed")
}

func TestBlackBoxLawyerDeadlineFailureThroughService(t *testing.T) {
	fx := newBlackBoxFixture(t)
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()

	svc := fx.startService(ctx, t)
	defer svc.kill(t)

	caseID := "bb-lawyer-deadline-service"
	outDir := svc.outputDir("service-lawyer-deadline-case")
	createCase(ctx, t, svc.baseURL, map[string]any{
		"case_id":                 caseID,
		"run_id":                  "run-" + caseID,
		"complaint_path":          fx.complaintPath,
		"out_dir":                 outDir,
		"policy_path":             fx.policyPath,
		"council_pool_path":       fx.councilPoolPath,
		"common_root":             fx.commonRoot,
		"engine_path":             fx.enginePath,
		"invalid_attempt_limit":   2,
		"lawyer_timeout_seconds":  1,
		"council_timeout_seconds": 10,
	})

	waitLawyerReady(ctx, t, svc.baseURL+"/lawyerapi/v1", caseID, "plaintiff")
	result := pollResultStatus(ctx, t, svc.baseURL, caseID, "failed")
	assertFailure(t, mapAny(result["failure"]), "plaintiff", "deadline_expired")
	record := pollCaseRecordStatus(ctx, t, svc.baseURL, caseID, "failed")
	assertServiceRecord(t, record, "failed", "failed")

	completedRead := getJSON(ctx, t, svc.baseURL+"/lawyerapi/v1/result?case_id="+url.QueryEscape(caseID)+"&role_id=observer")
	assertString(t, completedRead, "status", "failed")
	assertFailure(t, mapAny(completedRead["failure"]), "plaintiff", "deadline_expired")
	assertEventTypes(t, filepath.Join(outDir, "events.ndjson"), "opportunity_failed")
}

func TestBlackBoxCouncilMemberAttemptFailureThroughService(t *testing.T) {
	fx := newBlackBoxFixture(t)
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()

	svc := fx.startService(ctx, t)
	defer svc.kill(t)

	caseID := "bb-council-service"
	outDir := svc.outputDir("service-council-case")
	createCase(ctx, t, svc.baseURL, map[string]any{
		"case_id":                 caseID,
		"run_id":                  "run-" + caseID,
		"complaint_path":          fx.complaintPath,
		"out_dir":                 outDir,
		"policy_path":             fx.policyPath,
		"council_pool_path":       fx.councilPoolPath,
		"common_root":             fx.commonRoot,
		"engine_path":             fx.enginePath,
		"council_backend":         "councilapi",
		"invalid_attempt_limit":   1,
		"lawyer_timeout_seconds":  30,
		"council_timeout_seconds": 30,
	})

	lawyerBase := svc.baseURL + "/lawyerapi/v1"
	councilBase := svc.baseURL + "/councilapi/v1"
	completeLawyerPhases(ctx, t, lawyerBase, caseID)

	c1 := waitCouncilReady(ctx, t, councilBase, caseID, "C1")
	postCouncilTool(ctx, t, councilBase, map[string]any{
		"case_id":        caseID,
		"member_id":      "C1",
		"opportunity_id": stringAt(c1, "turn", "opportunity_id"),
		"tool":           "submit_council_vote",
		"arguments": map[string]any{
			"rationale": "missing vote",
		},
	}, false)

	failedC1 := getJSON(ctx, t, councilBase+"/get?case_id="+url.QueryEscape(caseID)+"&member_id=C1")
	assertString(t, failedC1, "status", "failed")
	assertFailure(t, mapAny(failedC1["failure"]), "council", "attempts_exhausted")
	assertString(t, mapAny(failedC1["failure"]), "member_id", "C1")

	c2 := waitCouncilReady(ctx, t, councilBase, caseID, "C2")
	postCouncilTool(ctx, t, councilBase, map[string]any{
		"case_id":        caseID,
		"member_id":      "C2",
		"opportunity_id": stringAt(c2, "turn", "opportunity_id"),
		"tool":           "submit_council_vote",
		"arguments": map[string]any{
			"vote":      "demonstrated",
			"rationale": "The minimal test record supports the proposition.",
		},
	}, true)

	c3 := waitCouncilReady(ctx, t, councilBase, caseID, "C3")
	postCouncilTool(ctx, t, councilBase, map[string]any{
		"case_id":        caseID,
		"member_id":      "C3",
		"opportunity_id": stringAt(c3, "turn", "opportunity_id"),
		"tool":           "submit_council_vote",
		"arguments": map[string]any{
			"vote":      "demonstrated",
			"rationale": "The minimal test record supports the proposition.",
		},
	}, true)

	result := pollResultStatus(ctx, t, svc.baseURL, caseID, "done")
	resultObj := mapAny(result["result"])
	assertString(t, resultObj, "resolution", "demonstrated")
	record := pollCaseRecordStatus(ctx, t, svc.baseURL, caseID, "completed")
	assertServiceRecord(t, record, "completed", "ok")

	run := readJSONFile(t, filepath.Join(outDir, "run.json"))
	assertString(t, run, "status", "ok")
	members := listOfMaps(mapAny(mapAny(run["final_state"])["case"])["council_members"])
	foundFailed := false
	for _, member := range members {
		if mapString(member["member_id"]) == "C1" {
			foundFailed = true
			assertString(t, member, "status", "failed")
			assertString(t, member, "failure_reason", "attempts_exhausted")
		}
	}
	if !foundFailed {
		t.Fatalf("final_state missing failed C1 member: %#v", members)
	}
	assertEventTypes(t, filepath.Join(outDir, "events.ndjson"), "opportunity_failed", "council_member_removed", "council_vote")
}

func TestBlackBoxCouncilMemberDeadlineFailureThroughService(t *testing.T) {
	fx := newBlackBoxFixture(t)
	ctx, cancel := context.WithTimeout(context.Background(), 90*time.Second)
	defer cancel()

	svc := fx.startService(ctx, t)
	defer svc.kill(t)

	caseID := "bb-council-deadline"
	outDir := svc.outputDir("service-council-deadline-case")
	createCase(ctx, t, svc.baseURL, map[string]any{
		"case_id":                 caseID,
		"run_id":                  "run-" + caseID,
		"complaint_path":          fx.complaintPath,
		"out_dir":                 outDir,
		"policy_path":             fx.policyPath,
		"council_pool_path":       fx.councilPoolPath,
		"common_root":             fx.commonRoot,
		"engine_path":             fx.enginePath,
		"council_backend":         "councilapi",
		"invalid_attempt_limit":   2,
		"lawyer_timeout_seconds":  30,
		"council_timeout_seconds": 1,
	})

	lawyerBase := svc.baseURL + "/lawyerapi/v1"
	councilBase := svc.baseURL + "/councilapi/v1"
	completeLawyerPhases(ctx, t, lawyerBase, caseID)

	waitCouncilReady(ctx, t, councilBase, caseID, "C1")
	failedC1 := waitCouncilStatus(ctx, t, councilBase, caseID, "C1", "failed")
	assertFailure(t, mapAny(failedC1["failure"]), "council", "deadline_expired")
	assertString(t, mapAny(failedC1["failure"]), "member_id", "C1")

	c2 := waitCouncilReady(ctx, t, councilBase, caseID, "C2")
	postCouncilTool(ctx, t, councilBase, map[string]any{
		"case_id":        caseID,
		"member_id":      "C2",
		"opportunity_id": stringAt(c2, "turn", "opportunity_id"),
		"tool":           "submit_council_vote",
		"arguments": map[string]any{
			"vote":      "demonstrated",
			"rationale": "The minimal test record supports the proposition.",
		},
	}, true)

	c3 := waitCouncilReady(ctx, t, councilBase, caseID, "C3")
	postCouncilTool(ctx, t, councilBase, map[string]any{
		"case_id":        caseID,
		"member_id":      "C3",
		"opportunity_id": stringAt(c3, "turn", "opportunity_id"),
		"tool":           "submit_council_vote",
		"arguments": map[string]any{
			"vote":      "demonstrated",
			"rationale": "The minimal test record supports the proposition.",
		},
	}, true)

	result := pollResultStatus(ctx, t, svc.baseURL, caseID, "done")
	resultObj := mapAny(result["result"])
	assertString(t, resultObj, "resolution", "demonstrated")
	record := pollCaseRecordStatus(ctx, t, svc.baseURL, caseID, "completed")
	assertServiceRecord(t, record, "completed", "ok")

	run := readJSONFile(t, filepath.Join(outDir, "run.json"))
	assertString(t, run, "status", "ok")
	members := listOfMaps(mapAny(mapAny(run["final_state"])["case"])["council_members"])
	foundFailed := false
	for _, member := range members {
		if mapString(member["member_id"]) == "C1" {
			foundFailed = true
			assertString(t, member, "status", "failed")
			assertString(t, member, "failure_reason", "deadline_expired")
		}
	}
	if !foundFailed {
		t.Fatalf("final_state missing failed C1 member: %#v", members)
	}
	assertEventTypes(t, filepath.Join(outDir, "events.ndjson"), "opportunity_failed", "council_member_removed", "council_vote")
}

type blackBoxFixture struct {
	dir             string
	arbRoot         string
	aarBin          string
	serviceBin      string
	mcpBin          string
	enginePath      string
	commonRoot      string
	complaintPath   string
	policyPath      string
	councilPoolPath string
	provider        *httptest.Server
	mu              sync.Mutex
	processSeq      int
}

func newBlackBoxFixture(t *testing.T) *blackBoxFixture {
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
	arbRoot := filepath.Join(carveCheckout, "arb")
	aarBin := filepath.Join(carveBins, "aar")
	serviceBin := filepath.Join(serviceBins, "aar-service")
	mcpBin := filepath.Join(serviceBins, "aar-mcp")
	enginePath := filepath.Join(arbRoot, "engine", ".lake", "build", "bin", "aarengine")
	for _, path := range []string{aarBin, serviceBin, mcpBin, enginePath} {
		if _, err := os.Stat(path); err != nil {
			t.Fatalf("stat compatibility executable %s: %v", path, err)
		}
	}
	provider := newFakeResponsesServer(t)
	dir, err := os.MkdirTemp("", "aar-blackbox-"+safeTestName(t.Name())+"-")
	if err != nil {
		t.Fatalf("create black-box fixture dir: %v", err)
	}
	blackBoxFixtureDirs.Store(t.Name(), dir)
	t.Logf("black-box fixture directory: %s", dir)
	t.Cleanup(func() {
		blackBoxFixtureDirs.Delete(t.Name())
		if t.Failed() {
			t.Logf("retained black-box fixture directory: %s", dir)
			return
		}
		if err := os.RemoveAll(dir); err != nil {
			t.Errorf("remove black-box fixture dir %s: %v", dir, err)
		}
	})
	complaintPath := filepath.Join(dir, "case", "complaint.md")
	mustWriteFile(t, complaintPath, "# Proposition\n\nThe proposition is true for this process and HTTP test.\n")
	policyPath := filepath.Join(dir, "policy.json")
	mustWriteJSON(t, policyPath, map[string]any{
		"council_size":                3,
		"required_votes_for_decision": 2,
		"max_deliberation_rounds":     1,
		"max_opening_chars":           1000,
		"max_argument_chars":          1000,
		"max_rebuttal_chars":          1000,
		"max_surrebuttal_chars":       1000,
		"max_closing_chars":           1000,
	})
	poolDir := filepath.Join(dir, "pool")
	for _, name := range []string{"c1.txt", "c2.txt", "c3.txt"} {
		mustWriteFile(t, filepath.Join(poolDir, name), "Process test council persona.\n")
	}
	councilPoolPath := filepath.Join(poolDir, "pool.jsonl")
	mustWriteFile(t, councilPoolPath, strings.Join([]string{
		`{"endpoint":"openai","model":"blackbox-council","persona":"c1.txt"}`,
		`{"endpoint":"openai","model":"blackbox-council","persona":"c2.txt"}`,
		`{"endpoint":"openai","model":"blackbox-council","persona":"c3.txt"}`,
		"",
	}, "\n"))
	t.Cleanup(provider.Close)
	return &blackBoxFixture{
		dir:             dir,
		arbRoot:         arbRoot,
		aarBin:          aarBin,
		serviceBin:      serviceBin,
		mcpBin:          mcpBin,
		enginePath:      enginePath,
		commonRoot:      filepath.Join(carveCheckout, "common"),
		complaintPath:   complaintPath,
		policyPath:      policyPath,
		councilPoolPath: councilPoolPath,
		provider:        provider,
	}
}

func newFakeResponsesServer(t *testing.T) *httptest.Server {
	t.Helper()
	return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost || r.URL.Path != "/v1/responses" {
			http.NotFound(w, r)
			return
		}
		if _, err := io.Copy(io.Discard, r.Body); err != nil {
			t.Errorf("read fake provider request: %v", err)
			return
		}
		w.Header().Set("Content-Type", "application/json")
		if err := json.NewEncoder(w).Encode(map[string]any{
			"id":         "resp_blackbox",
			"object":     "response",
			"created_at": time.Now().Unix(),
			"status":     "completed",
			"model":      "blackbox-council",
			"output": []map[string]any{
				{
					"id":     "msg_blackbox",
					"type":   "message",
					"status": "completed",
					"role":   "assistant",
					"content": []map[string]any{
						{
							"type":        "output_text",
							"text":        "ready",
							"annotations": []any{},
						},
					},
				},
			},
			"usage": map[string]any{
				"input_tokens":  1,
				"output_tokens": 1,
				"total_tokens":  2,
			},
		}); err != nil {
			t.Errorf("write fake provider response: %v", err)
		}
	}))
}

func (fx *blackBoxFixture) startCommand(ctx context.Context, command string, args ...string) *testProcess {
	cmd := exec.CommandContext(ctx, command, args...)
	cmd.Dir = fx.arbRoot
	cmd.Env = mergedEnv(map[string]string{
		"OPENAI_API_KEY":  "blackbox-key",
		"OPENAI_BASE_URL": fx.provider.URL + "/v1",
	})
	stdoutLog, stderrLog := fx.processLogPaths()
	return startTestProcess(cmd, stdoutLog, stderrLog)
}

func (fx *blackBoxFixture) processLogPaths() (string, string) {
	fx.mu.Lock()
	fx.processSeq++
	seq := fx.processSeq
	fx.mu.Unlock()
	dir := filepath.Join(fx.dir, "process-logs")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		panic(err)
	}
	return filepath.Join(dir, fmt.Sprintf("%02d-stdout.log", seq)), filepath.Join(dir, fmt.Sprintf("%02d-stderr.log", seq))
}

type serviceProcess struct {
	*testProcess
	baseURL string
	outRoot string
}

func (fx *blackBoxFixture) startService(ctx context.Context, t *testing.T) *serviceProcess {
	t.Helper()
	listen := freeListenAddr(t)
	outRoot := filepath.Join(fx.dir, "service-out-"+strings.ReplaceAll(listen, ":", "-"))
	proc := fx.startCommand(ctx, fx.serviceBin,
		"--listen", listen,
		"--registry-dir", filepath.Join(fx.dir, "registry-"+strings.ReplaceAll(listen, ":", "-")),
		"--out-root", outRoot,
		"--aar-bin", fx.aarBin,
		"--aar-working-dir", fx.arbRoot,
		"--common-root", fx.commonRoot,
		"--engine", fx.enginePath,
	)
	proc.waitForStderrPrefix(ctx, t, "aar service listening on ")
	return &serviceProcess{testProcess: proc, baseURL: "http://" + listen, outRoot: outRoot}
}

func (svc *serviceProcess) outputDir(name string) string {
	return filepath.Join(svc.outRoot, name)
}

type testProcess struct {
	cmd         *exec.Cmd
	stdout      lockedBuffer
	stderr      lockedBuffer
	stderrLines chan string
	done        chan error
	stdoutDone  chan error
	stderrDone  chan error
}

func startTestProcess(cmd *exec.Cmd, stdoutLogPath string, stderrLogPath string) *testProcess {
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		panic(err)
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		panic(err)
	}
	stdoutLog := createLogFile(stdoutLogPath)
	stderrLog := createLogFile(stderrLogPath)
	proc := &testProcess{
		cmd:         cmd,
		stderrLines: make(chan string, 128),
		done:        make(chan error, 1),
		stdoutDone:  make(chan error, 1),
		stderrDone:  make(chan error, 1),
	}
	if err := cmd.Start(); err != nil {
		panic(errors.Join(err, stdoutLog.Close(), stderrLog.Close()))
	}
	go func() {
		proc.stdoutDone <- scanLines(stdout, &proc.stdout, nil, stdoutLog)
	}()
	go func() {
		proc.stderrDone <- scanLines(stderr, &proc.stderr, proc.stderrLines, stderrLog)
		close(proc.stderrLines)
	}()
	go func() {
		stdoutErr := <-proc.stdoutDone
		stderrErr := <-proc.stderrDone
		waitErr := cmd.Wait()
		proc.done <- errors.Join(waitErr, stdoutErr, stderrErr)
	}()
	return proc
}

func createLogFile(path string) *os.File {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		panic(err)
	}
	f, err := os.Create(path)
	if err != nil {
		panic(err)
	}
	return f
}

func (p *testProcess) waitForStderrPrefix(ctx context.Context, t *testing.T, prefix string) string {
	t.Helper()
	ticker := time.NewTicker(10 * time.Millisecond)
	defer ticker.Stop()
	for {
		if value, ok := findLinePrefix(p.stderrString(), prefix); ok {
			return value
		}
		select {
		case line, ok := <-p.stderrLines:
			if !ok {
				t.Fatalf("process stderr ended before %q\nstderr:\n%s\nstdout:\n%s", prefix, p.stderrString(), p.stdoutString())
			}
			if strings.HasPrefix(line, prefix) {
				return strings.TrimSpace(strings.TrimPrefix(line, prefix))
			}
		case <-ticker.C:
		case err := <-p.done:
			t.Fatalf("process exited before %q: %v\nstderr:\n%s\nstdout:\n%s", prefix, err, p.stderrString(), p.stdoutString())
		case <-ctx.Done():
			t.Fatalf("timeout waiting for %q\nstderr:\n%s\nstdout:\n%s", prefix, p.stderrString(), p.stdoutString())
		}
	}
}

func (p *testProcess) kill(t *testing.T) {
	t.Helper()
	if p.cmd.Process != nil {
		if err := p.cmd.Process.Kill(); err != nil && !errors.Is(err, os.ErrProcessDone) {
			t.Errorf("kill process: %v", err)
		}
	}
}

func (p *testProcess) stdoutString() string {
	return p.stdout.String()
}

func (p *testProcess) stderrString() string {
	return p.stderr.String()
}

type lockedBuffer struct {
	mu sync.Mutex
	b  bytes.Buffer
}

func (b *lockedBuffer) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.Write(p)
}

func (b *lockedBuffer) String() string {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.b.String()
}

func scanLines(r io.Reader, buf *lockedBuffer, lines chan<- string, logFile *os.File) error {
	scanner := bufio.NewScanner(r)
	scanner.Buffer(make([]byte, 0, 64*1024), 16*1024*1024)
	var firstErr error
	for scanner.Scan() {
		line := scanner.Text()
		if _, err := buf.Write([]byte(line + "\n")); err != nil {
			return err
		}
		if logFile != nil && firstErr == nil {
			if _, err := fmt.Fprintln(logFile, line); err != nil {
				firstErr = fmt.Errorf("write process log: %w", err)
			}
		}
		if lines != nil {
			select {
			case lines <- line:
			default:
			}
		}
	}
	if logFile != nil {
		if err := logFile.Close(); err != nil && firstErr == nil {
			firstErr = fmt.Errorf("close process log: %w", err)
		}
	}
	return errors.Join(firstErr, scanner.Err())
}

func findLinePrefix(text string, prefix string) (string, bool) {
	for _, line := range strings.Split(text, "\n") {
		if strings.HasPrefix(line, prefix) {
			return strings.TrimSpace(strings.TrimPrefix(line, prefix)), true
		}
	}
	return "", false
}

func waitLawyerReady(ctx context.Context, t *testing.T, base string, caseID string, role string) map[string]any {
	t.Helper()
	endpoint := fmt.Sprintf("%s/wait?case_id=%s&role_id=%s&timeout_ms=5000", base, url.QueryEscape(caseID), url.QueryEscape(role))
	for {
		resp := getJSON(ctx, t, endpoint)
		switch mapString(resp["status"]) {
		case "ready":
			return resp
		case "failed", "done":
			t.Fatalf("lawyer %s status = %s, want ready: %#v", role, resp["status"], resp)
		}
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for lawyer %s ready", role)
		default:
		}
	}
}

func waitCouncilReady(ctx context.Context, t *testing.T, base string, caseID string, memberID string) map[string]any {
	t.Helper()
	endpoint := fmt.Sprintf("%s/wait?case_id=%s&member_id=%s&timeout_ms=5000", base, url.QueryEscape(caseID), url.QueryEscape(memberID))
	for {
		resp := getJSON(ctx, t, endpoint)
		switch mapString(resp["status"]) {
		case "ready":
			return resp
		case "failed", "done":
			t.Fatalf("council %s status = %s, want ready: %#v", memberID, resp["status"], resp)
		}
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for council %s ready", memberID)
		default:
		}
	}
}

func waitCouncilStatus(ctx context.Context, t *testing.T, base string, caseID string, memberID string, want string) map[string]any {
	t.Helper()
	endpoint := fmt.Sprintf("%s/wait?case_id=%s&member_id=%s&timeout_ms=5000", base, url.QueryEscape(caseID), url.QueryEscape(memberID))
	for {
		resp := getJSON(ctx, t, endpoint)
		status := mapString(resp["status"])
		if status == want {
			return resp
		}
		if status == "failed" || status == "done" {
			t.Fatalf("council %s status = %s, want %s: %#v", memberID, status, want, resp)
		}
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for council %s status %s", memberID, want)
		case <-time.After(50 * time.Millisecond):
		}
	}
}

func completeLawyerPhases(ctx context.Context, t *testing.T, base string, caseID string) {
	t.Helper()
	submitLawyerDecision(ctx, t, base, caseID, "plaintiff", "record_opening_statement", map[string]any{"text": "Plaintiff opening."})
	submitLawyerDecision(ctx, t, base, caseID, "defendant", "record_opening_statement", map[string]any{"text": "Defendant opening."})
	submitLawyerDecision(ctx, t, base, caseID, "plaintiff", "submit_argument", map[string]any{"text": "Plaintiff argument.", "offered_evidence": []any{}, "technical_reports": []any{}})
	submitLawyerDecision(ctx, t, base, caseID, "defendant", "submit_argument", map[string]any{"text": "Defendant argument.", "offered_evidence": []any{}, "technical_reports": []any{}})
	submitLawyerPass(ctx, t, base, caseID, "plaintiff")
	submitLawyerPass(ctx, t, base, caseID, "defendant")
	submitLawyerDecision(ctx, t, base, caseID, "plaintiff", "deliver_closing_statement", map[string]any{"text": "Plaintiff closing."})
	submitLawyerDecision(ctx, t, base, caseID, "defendant", "deliver_closing_statement", map[string]any{"text": "Defendant closing."})
}

func submitLawyerDecision(ctx context.Context, t *testing.T, base string, caseID string, role string, toolName string, payload map[string]any) {
	t.Helper()
	ready := waitLawyerReady(ctx, t, base, caseID, role)
	postLawyerTool(ctx, t, base, map[string]any{
		"case_id":        caseID,
		"role_id":        role,
		"opportunity_id": stringAt(ready, "turn", "opportunity_id"),
		"tool":           "submit_decision",
		"arguments": map[string]any{
			"kind":      "tool",
			"tool_name": toolName,
			"payload":   payload,
		},
	}, true)
}

func submitLawyerPass(ctx context.Context, t *testing.T, base string, caseID string, role string) {
	t.Helper()
	ready := waitLawyerReady(ctx, t, base, caseID, role)
	postLawyerTool(ctx, t, base, map[string]any{
		"case_id":        caseID,
		"role_id":        role,
		"opportunity_id": stringAt(ready, "turn", "opportunity_id"),
		"tool":           "submit_decision",
		"arguments": map[string]any{
			"kind": "pass",
		},
	}, true)
}

func postLawyerTool(ctx context.Context, t *testing.T, base string, body map[string]any, wantOK bool) map[string]any {
	t.Helper()
	return postJSONExpectOK(ctx, t, base+"/do", body, wantOK)
}

func postCouncilTool(ctx context.Context, t *testing.T, base string, body map[string]any, wantOK bool) map[string]any {
	t.Helper()
	return postJSONExpectOK(ctx, t, base+"/do", body, wantOK)
}

func postJSONExpectOK(ctx context.Context, t *testing.T, endpoint string, body map[string]any, wantOK bool) map[string]any {
	t.Helper()
	resp := postJSON(ctx, t, endpoint, body)
	if got := boolAt(resp, "ok"); got != wantOK {
		t.Fatalf("POST %s ok = %t, want %t; body=%#v response=%#v", endpoint, got, wantOK, body, resp)
	}
	return resp
}

func createCase(ctx context.Context, t *testing.T, serviceBase string, body map[string]any) map[string]any {
	t.Helper()
	return postJSONExpectOK(ctx, t, serviceBase+"/api/v1/cases", body, true)
}

func pollResultStatus(ctx context.Context, t *testing.T, serviceBase string, caseID string, want string) map[string]any {
	t.Helper()
	endpoint := serviceBase + "/api/v1/cases/" + url.PathEscape(caseID) + "/result"
	for {
		resp := getJSON(ctx, t, endpoint)
		if mapString(resp["status"]) == want {
			return resp
		}
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for result status %q; last response=%#v", want, resp)
		case <-time.After(100 * time.Millisecond):
		}
	}
}

func pollCaseRecordStatus(ctx context.Context, t *testing.T, serviceBase string, caseID string, want string) map[string]any {
	t.Helper()
	endpoint := serviceBase + "/api/v1/cases/" + url.PathEscape(caseID)
	for {
		resp := getJSON(ctx, t, endpoint)
		if mapString(mapAny(resp["case"])["status"]) == want {
			return resp
		}
		select {
		case <-ctx.Done():
			t.Fatalf("timeout waiting for case record status %q; last response=%#v", want, resp)
		case <-time.After(100 * time.Millisecond):
		}
	}
}

func getJSON(ctx context.Context, t *testing.T, endpoint string) map[string]any {
	t.Helper()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, endpoint, nil)
	if err != nil {
		t.Fatalf("new GET request: %v", err)
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("GET %s: %v", endpoint, err)
	}
	defer func() {
		if err := resp.Body.Close(); err != nil {
			t.Errorf("close GET response body: %v", err)
		}
	}()
	return decodeHTTPJSON(t, resp, endpoint, nil)
}

func postJSON(ctx context.Context, t *testing.T, endpoint string, body map[string]any) map[string]any {
	t.Helper()
	wire, err := json.Marshal(body)
	if err != nil {
		t.Fatalf("marshal POST body: %v", err)
	}
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, endpoint, bytes.NewReader(wire))
	if err != nil {
		t.Fatalf("new POST request: %v", err)
	}
	req.Header.Set("Content-Type", "application/json")
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("POST %s: %v", endpoint, err)
	}
	defer func() {
		if err := resp.Body.Close(); err != nil {
			t.Errorf("close POST response body: %v", err)
		}
	}()
	return decodeHTTPJSON(t, resp, endpoint, wire)
}

func decodeHTTPJSON(t *testing.T, resp *http.Response, endpoint string, requestBody []byte) map[string]any {
	t.Helper()
	raw, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read response body: %v", err)
	}
	logHTTPExchange(t, resp.Request.Method, endpoint, requestBody, resp.StatusCode, raw)
	var out map[string]any
	if err := json.Unmarshal(raw, &out); err != nil {
		t.Fatalf("%s returned non-JSON HTTP %d: %s", endpoint, resp.StatusCode, string(raw))
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		t.Fatalf("%s returned HTTP %d: %#v", endpoint, resp.StatusCode, out)
	}
	return out
}

func logHTTPExchange(t *testing.T, method string, endpoint string, requestBody []byte, status int, responseBody []byte) {
	t.Helper()
	rawDir, ok := blackBoxFixtureDirs.Load(t.Name())
	if !ok {
		return
	}
	dir, ok := rawDir.(string)
	if !ok || strings.TrimSpace(dir) == "" {
		return
	}
	entry := map[string]any{
		"time":     time.Now().UTC().Format(time.RFC3339Nano),
		"method":   method,
		"endpoint": endpoint,
		"status":   status,
	}
	if len(requestBody) > 0 {
		entry["request"] = jsonForLog(requestBody)
	}
	if len(responseBody) > 0 {
		entry["response"] = jsonForLog(responseBody)
	}
	appendJSONLine(t, filepath.Join(dir, "http.ndjson"), entry)
}

func appendJSONLine(t *testing.T, path string, value any) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatalf("mkdir %s: %v", filepath.Dir(path), err)
	}
	f, err := os.OpenFile(path, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
	if err != nil {
		t.Fatalf("open %s: %v", path, err)
	}
	defer func() {
		if err := f.Close(); err != nil {
			t.Errorf("close %s: %v", path, err)
		}
	}()
	wire, err := json.Marshal(value)
	if err != nil {
		t.Fatalf("marshal log entry for %s: %v", path, err)
	}
	if _, err := f.Write(append(wire, '\n')); err != nil {
		t.Fatalf("write %s: %v", path, err)
	}
}

func jsonForLog(raw []byte) any {
	var value any
	if err := json.Unmarshal(raw, &value); err == nil {
		return value
	}
	return string(raw)
}

func readJSONFile(t *testing.T, path string) map[string]any {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	var out map[string]any
	if err := json.Unmarshal(raw, &out); err != nil {
		t.Fatalf("parse %s: %v", path, err)
	}
	return out
}

func assertEventTypes(t *testing.T, path string, want ...string) {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	found := map[string]bool{}
	for _, line := range strings.Split(strings.TrimSpace(string(raw)), "\n") {
		if strings.TrimSpace(line) == "" {
			continue
		}
		var event map[string]any
		if err := json.Unmarshal([]byte(line), &event); err != nil {
			t.Fatalf("parse event line %q: %v", line, err)
		}
		found[mapString(event["type"])] = true
	}
	for _, eventType := range want {
		if !found[eventType] {
			t.Fatalf("events in %s missing %q; found=%v", path, eventType, found)
		}
	}
}

func assertFailure(t *testing.T, failure map[string]any, role string, reason string) {
	t.Helper()
	if len(failure) == 0 {
		t.Fatalf("failure object is empty")
	}
	if got := mapString(failure["type"]); got != "" && got != "opportunity_failed" {
		t.Fatalf("failure.type = %q, want opportunity_failed", got)
	}
	if got := mapString(failure["failure_type"]); got != "" && got != "opportunity_failed" {
		t.Fatalf("failure.failure_type = %q, want opportunity_failed", got)
	}
	assertString(t, failure, "role", role)
	assertString(t, failure, "reason", reason)
	if mapString(failure["opportunity_id"]) == "" {
		t.Fatalf("failure missing opportunity_id: %#v", failure)
	}
}

func assertServiceRecord(t *testing.T, record map[string]any, wantStatus string, wantSummaryStatus string) {
	t.Helper()
	caseObj := mapAny(record["case"])
	assertString(t, caseObj, "status", wantStatus)
	if got := intValue(caseObj["exit_code"]); got != 0 {
		t.Fatalf("exit_code = %d, want 0 in %#v", got, caseObj)
	}
	summary := mapAny(caseObj["summary"])
	assertString(t, summary, "status", wantSummaryStatus)
	for _, key := range []string{"stdout_log", "stderr_log"} {
		path := mapString(caseObj[key])
		if path == "" {
			t.Fatalf("case record missing %s: %#v", key, caseObj)
		}
		if _, err := os.Stat(path); err != nil {
			t.Fatalf("stat %s %q: %v", key, path, err)
		}
	}
}

func assertString(t *testing.T, m map[string]any, key string, want string) {
	t.Helper()
	if got := mapString(m[key]); got != want {
		t.Fatalf("%s = %q, want %q in %#v", key, got, want, m)
	}
}

func stringAt(m map[string]any, keys ...string) string {
	var value any = m
	for _, key := range keys {
		value = mapAny(value)[key]
	}
	return mapString(value)
}

func boolAt(m map[string]any, key string) bool {
	value, _ := m[key].(bool)
	return value
}

func mapAny(value any) map[string]any {
	out, _ := value.(map[string]any)
	if out == nil {
		return map[string]any{}
	}
	return out
}

func listOfMaps(value any) []map[string]any {
	switch v := value.(type) {
	case []map[string]any:
		return v
	case []any:
		out := make([]map[string]any, 0, len(v))
		for _, raw := range v {
			if entry := mapAny(raw); len(entry) > 0 {
				out = append(out, entry)
			}
		}
		return out
	default:
		return nil
	}
}

func mapString(value any) string {
	switch v := value.(type) {
	case nil:
		return ""
	case string:
		return strings.TrimSpace(v)
	default:
		return strings.TrimSpace(fmt.Sprintf("%v", value))
	}
}

func intValue(value any) int {
	switch v := value.(type) {
	case int:
		return v
	case int64:
		return int(v)
	case float64:
		return int(v)
	case json.Number:
		i, _ := v.Int64()
		return int(i)
	default:
		return 0
	}
}

func safeTestName(name string) string {
	var b strings.Builder
	for _, r := range name {
		switch {
		case r >= 'a' && r <= 'z':
			b.WriteRune(r)
		case r >= 'A' && r <= 'Z':
			b.WriteRune(r)
		case r >= '0' && r <= '9':
			b.WriteRune(r)
		default:
			b.WriteByte('_')
		}
	}
	out := strings.Trim(b.String(), "_")
	if out == "" {
		return "test"
	}
	return out
}

func mustWriteFile(t *testing.T, path string, text string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatalf("mkdir %s: %v", filepath.Dir(path), err)
	}
	if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
		t.Fatalf("write %s: %v", path, err)
	}
}

func mustWriteJSON(t *testing.T, path string, value any) {
	t.Helper()
	wire, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		t.Fatalf("marshal %s: %v", path, err)
	}
	mustWriteFile(t, path, string(wire)+"\n")
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

func mergedEnv(overrides map[string]string) []string {
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
