package service

import (
	"bytes"
	"context"
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"sync"
	"time"
)

const (
	DefaultListenAddr      = "127.0.0.1:19770"
	DefaultCaseStartupWait = 30 * time.Second

	defaultCaseAPIAddr       = "127.0.0.1:0"
	defaultCouncilBackend    = "direct"
	defaultAARRunCommand     = "aar-run"
	defaultMaxProxyBodyBytes = 32 << 20
	detachedProcessMessage   = "service restarted and child process is not attached"
)

type Config struct {
	ListenAddr    string
	RegistryDir   string
	OutputRoot    string
	AARBin        string
	AARRunBin     string
	AARWorkingDir string
	CommonRoot    string
	EnginePath    string
	BearerToken   string
	Attested      AttestedClerkConfig
	StartupWait   time.Duration
	Log           io.Writer
}

type Server struct {
	cfg        Config
	mu         sync.Mutex
	cond       *sync.Cond
	cases      map[string]*CaseRecord
	clerkCases map[string]*ClerkRecord
	client     *http.Client
}

type CaseCreateRequest struct {
	CaseID                  string   `json:"case_id,omitempty"`
	RunID                   string   `json:"run_id,omitempty"`
	ComplaintPath           string   `json:"complaint_path"`
	CaseFiles               []string `json:"case_files,omitempty"`
	PolicyPath              string   `json:"policy_path,omitempty"`
	OutputDir               string   `json:"out_dir,omitempty"`
	CouncilBackend          string   `json:"council_backend,omitempty"`
	LawyerTimeoutSeconds    int      `json:"lawyer_timeout_seconds,omitempty"`
	CouncilTimeoutSeconds   int      `json:"council_timeout_seconds,omitempty"`
	InvalidAttemptLimit     int      `json:"invalid_attempt_limit,omitempty"`
	MaxResponseBytes        int      `json:"max_response_bytes,omitempty"`
	CommonRoot              string   `json:"common_root,omitempty"`
	EnginePath              string   `json:"engine_path,omitempty"`
	CouncilPoolPath         string   `json:"council_pool_path,omitempty"`
	AttorneyInstructions    string   `json:"attorney_instructions,omitempty"`
	PromptDir               string   `json:"prompt_dir,omitempty"`
	AttorneyCommonPrompt    string   `json:"attorney_common_prompt,omitempty"`
	AttorneyArgumentsPrompt string   `json:"attorney_arguments_prompt,omitempty"`
	AttorneyRebuttalsPrompt string   `json:"attorney_rebuttals_prompt,omitempty"`
}

type CaseRecord struct {
	CaseID         string         `json:"case_id"`
	RunID          string         `json:"run_id"`
	PID            int            `json:"pid,omitempty"`
	Status         string         `json:"status"`
	ComplaintPath  string         `json:"complaint_path"`
	OutputDir      string         `json:"out_dir"`
	CaseAPIBase    string         `json:"caseapi_base,omitempty"`
	CouncilBackend string         `json:"council_backend"`
	CreatedAt      string         `json:"created_at"`
	StartedAt      string         `json:"started_at,omitempty"`
	FinishedAt     string         `json:"finished_at,omitempty"`
	ExitCode       *int           `json:"exit_code,omitempty"`
	Summary        map[string]any `json:"summary,omitempty"`
	Error          string         `json:"error,omitempty"`
	StdoutLog      string         `json:"stdout_log,omitempty"`
	StderrLog      string         `json:"stderr_log,omitempty"`

	canceling bool
	cmd       *exec.Cmd
}

func New(cfg Config) (*Server, error) {
	cfg.ListenAddr = strings.TrimSpace(cfg.ListenAddr)
	if cfg.ListenAddr == "" {
		cfg.ListenAddr = DefaultListenAddr
	}
	if strings.TrimSpace(cfg.RegistryDir) == "" {
		return nil, fmt.Errorf("registry dir is required")
	}
	if strings.TrimSpace(cfg.OutputRoot) == "" {
		return nil, fmt.Errorf("output root is required")
	}
	if strings.TrimSpace(cfg.AARBin) == "" {
		return nil, fmt.Errorf("aar binary path is required")
	}
	if strings.TrimSpace(cfg.AARRunBin) == "" {
		cfg.AARRunBin = defaultAARRunCommand
	}
	if cfg.StartupWait <= 0 {
		cfg.StartupWait = DefaultCaseStartupWait
	}
	if err := os.MkdirAll(cfg.RegistryDir, 0o755); err != nil {
		return nil, fmt.Errorf("create registry dir: %w", err)
	}
	if err := os.MkdirAll(cfg.OutputRoot, 0o755); err != nil {
		return nil, fmt.Errorf("create output root: %w", err)
	}
	s := &Server{
		cfg:        cfg,
		cases:      map[string]*CaseRecord{},
		clerkCases: map[string]*ClerkRecord{},
		client: &http.Client{
			Timeout: 10 * time.Minute,
		},
	}
	s.cond = sync.NewCond(&s.mu)
	if err := s.loadRegistry(); err != nil {
		return nil, err
	}
	return s, nil
}

func Run(ctx context.Context, cfg Config) error {
	server, err := New(cfg)
	if err != nil {
		return err
	}
	ln, err := server.Listen()
	if err != nil {
		return err
	}
	if cfg.Log != nil {
		fmt.Fprintf(cfg.Log, "aar service listening on http://%s\n", ln.Addr().String())
	}
	return server.Serve(ctx, ln)
}

func (s *Server) ListenAddr() string {
	return s.cfg.ListenAddr
}

func (s *Server) Listen() (net.Listener, error) {
	return net.Listen("tcp", s.cfg.ListenAddr)
}

func (s *Server) Serve(ctx context.Context, ln net.Listener) error {
	if ln == nil {
		return fmt.Errorf("listener is required")
	}
	if ctx == nil {
		ctx = context.Background()
	}
	server := &http.Server{
		Handler: s.Handler(),
	}
	shutdownDone := make(chan error, 1)
	go func() {
		<-ctx.Done()
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		shutdownDone <- server.Shutdown(shutdownCtx)
	}()
	err := server.Serve(ln)
	if errors.Is(err, http.ErrServerClosed) {
		if shutdownErr := <-shutdownDone; shutdownErr != nil {
			return shutdownErr
		}
		return nil
	}
	return err
}

func (s *Server) Handler() http.Handler {
	mux := http.NewServeMux()
	mux.HandleFunc("/clerk/v1/cases", s.handleClerkCases)
	mux.HandleFunc("/clerk/v1/cases/", s.handleClerkCase)
	mux.HandleFunc("/api/v1/cases", s.handleCases)
	mux.HandleFunc("/api/v1/cases/", s.handleCase)
	mux.HandleFunc("/lawyerapi/v1/get", s.proxyLawyerGET)
	mux.HandleFunc("/lawyerapi/v1/wait", s.proxyLawyerGET)
	mux.HandleFunc("/lawyerapi/v1/status", s.proxyLawyerGET)
	mux.HandleFunc("/lawyerapi/v1/result", s.proxyLawyerGET)
	mux.HandleFunc("/lawyerapi/v1/do", s.proxyLawyerDo)
	mux.HandleFunc("/councilapi/v1/get", s.proxyCouncilGET)
	mux.HandleFunc("/councilapi/v1/wait", s.proxyCouncilGET)
	mux.HandleFunc("/councilapi/v1/do", s.proxyCouncilDo)
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if !s.authorized(r) {
			writeJSON(w, http.StatusUnauthorized, map[string]any{
				"ok":    false,
				"error": apiError("unauthorized", "missing or invalid bearer token"),
			})
			return
		}
		mux.ServeHTTP(w, r)
	})
}

func (s *Server) authorized(r *http.Request) bool {
	token := strings.TrimSpace(s.cfg.BearerToken)
	if token == "" {
		return true
	}
	return strings.TrimSpace(r.Header.Get("Authorization")) == "Bearer "+token
}

func (s *Server) handleCases(w http.ResponseWriter, r *http.Request) {
	switch r.Method {
	case http.MethodPost:
		s.handleCreateCase(w, r)
	case http.MethodGet:
		s.handleListCases(w, r)
	default:
		writeJSON(w, http.StatusMethodNotAllowed, map[string]any{"ok": false, "error": apiError("method_not_allowed", "use GET or POST")})
	}
}

func (s *Server) handleCreateCase(w http.ResponseWriter, r *http.Request) {
	var req CaseCreateRequest
	dec := json.NewDecoder(http.MaxBytesReader(w, r.Body, 1<<20))
	if err := dec.Decode(&req); err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("bad_json", err.Error())})
		return
	}
	rec, err := s.startCase(r.Context(), req)
	if err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("start_case_failed", err.Error())})
		return
	}
	writeJSON(w, http.StatusAccepted, map[string]any{"ok": true, "case": rec})
}

func (s *Server) handleListCases(w http.ResponseWriter, r *http.Request) {
	s.mu.Lock()
	records := make([]CaseRecord, 0, len(s.cases))
	for _, rec := range s.cases {
		if status := strings.TrimSpace(r.URL.Query().Get("status")); status != "" && rec.Status != status {
			continue
		}
		records = append(records, publicRecord(rec))
	}
	s.mu.Unlock()
	sort.Slice(records, func(i, j int) bool {
		return records[i].CreatedAt < records[j].CreatedAt
	})
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "cases": records})
}

func (s *Server) handleCase(w http.ResponseWriter, r *http.Request) {
	rest := strings.TrimPrefix(r.URL.Path, "/api/v1/cases/")
	parts := strings.Split(strings.Trim(rest, "/"), "/")
	if len(parts) == 0 || parts[0] == "" {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "error": apiError("not_found", "case id is required")})
		return
	}
	caseID := parts[0]
	if len(parts) == 1 && r.Method == http.MethodGet {
		rec, ok := s.getCase(caseID)
		if !ok {
			writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": rec})
		return
	}
	if len(parts) == 2 && parts[1] == "result" && r.Method == http.MethodGet {
		s.handleCaseResult(w, caseID)
		return
	}
	if len(parts) == 2 && parts[1] == "cancel" && r.Method == http.MethodPost {
		s.handleCancelCase(w, caseID)
		return
	}
	if len(parts) >= 2 && parts[1] == "artifacts" && r.Method == http.MethodGet {
		name := strings.Join(parts[2:], "/")
		s.handleArtifact(w, r, caseID, name)
		return
	}
	if len(parts) == 3 && parts[1] == "evidence" && r.Method == http.MethodGet {
		s.handleEvidence(w, r, caseID, parts[2])
		return
	}
	writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("not_found", "unknown case route")})
}

func (s *Server) startCase(ctx context.Context, req CaseCreateRequest) (CaseRecord, error) {
	caseID := strings.TrimSpace(req.CaseID)
	if caseID == "" {
		caseID = "arb-" + time.Now().UTC().Format("20060102150405") + "-" + randomHex(4)
	}
	if err := validateID(caseID, "case_id"); err != nil {
		return CaseRecord{}, err
	}
	runID := strings.TrimSpace(req.RunID)
	if runID == "" {
		runID = "run-" + caseID
	}
	complaintPath := strings.TrimSpace(req.ComplaintPath)
	if complaintPath == "" {
		return CaseRecord{}, fmt.Errorf("complaint_path is required")
	}
	if _, err := os.Stat(complaintPath); err != nil {
		return CaseRecord{}, fmt.Errorf("complaint_path: %w", err)
	}
	outDir := strings.TrimSpace(req.OutputDir)
	if outDir == "" {
		outDir = filepath.Join(s.cfg.OutputRoot, caseID)
	}
	if err := validateServiceOutputDir(s.cfg.OutputRoot, outDir); err != nil {
		return CaseRecord{}, err
	}
	if err := os.MkdirAll(outDir, 0o755); err != nil {
		return CaseRecord{}, fmt.Errorf("create case output dir: %w", err)
	}
	logDir := filepath.Join(outDir, "service-logs")
	if err := os.MkdirAll(logDir, 0o755); err != nil {
		return CaseRecord{}, fmt.Errorf("create service log dir: %w", err)
	}

	councilBackend := strings.TrimSpace(req.CouncilBackend)
	if councilBackend == "" {
		councilBackend = defaultCouncilBackend
	}
	caseAPIAddr, err := chooseLocalCaseAPIAddr()
	if err != nil {
		return CaseRecord{}, err
	}
	caseAPIBase := "http://" + caseAPIAddr
	args := []string{
		"case",
		"--case-id", caseID,
		"--run-id", runID,
		"--complaint", complaintPath,
		"--out-dir", outDir,
		"--caseapi-addr", caseAPIAddr,
		"--council-backend", councilBackend,
	}
	for _, file := range req.CaseFiles {
		if strings.TrimSpace(file) != "" {
			args = append(args, "--file", strings.TrimSpace(file))
		}
	}
	addStringFlag := func(name string, value string) {
		if strings.TrimSpace(value) != "" {
			args = append(args, name, strings.TrimSpace(value))
		}
	}
	addIntFlag := func(name string, value int) {
		if value > 0 {
			args = append(args, name, fmt.Sprintf("%d", value))
		}
	}
	addStringFlag("--policy", req.PolicyPath)
	addStringFlag("--common-root", firstNonEmpty(req.CommonRoot, s.cfg.CommonRoot))
	addStringFlag("--engine", firstNonEmpty(req.EnginePath, s.cfg.EnginePath))
	addStringFlag("--council-pool", req.CouncilPoolPath)
	addStringFlag("--attorney-instructions", req.AttorneyInstructions)
	addStringFlag("--prompt-dir", req.PromptDir)
	addStringFlag("--attorney-common-prompt", req.AttorneyCommonPrompt)
	addStringFlag("--attorney-arguments-prompt", req.AttorneyArgumentsPrompt)
	addStringFlag("--attorney-rebuttals-prompt", req.AttorneyRebuttalsPrompt)
	addIntFlag("--lawyer-timeout-seconds", req.LawyerTimeoutSeconds)
	addIntFlag("--timeout-seconds", req.CouncilTimeoutSeconds)
	addIntFlag("--invalid-attempt-limit", req.InvalidAttemptLimit)
	addIntFlag("--max-response-bytes", req.MaxResponseBytes)

	stdoutPath := filepath.Join(logDir, "aar.stdout")
	stderrPath := filepath.Join(logDir, "aar.stderr")
	stdoutFile, err := os.Create(stdoutPath)
	if err != nil {
		return CaseRecord{}, fmt.Errorf("create stdout log: %w", err)
	}
	stderrFile, err := os.Create(stderrPath)
	if err != nil {
		_ = stdoutFile.Close()
		return CaseRecord{}, fmt.Errorf("create stderr log: %w", err)
	}

	cmd := exec.CommandContext(context.Background(), s.cfg.AARBin, args...)
	if strings.TrimSpace(s.cfg.AARWorkingDir) != "" {
		cmd.Dir = strings.TrimSpace(s.cfg.AARWorkingDir)
	}
	cmd.Stdout = stdoutFile
	cmd.Stderr = stderrFile
	closeLogs := func() error {
		return errors.Join(stdoutFile.Close(), stderrFile.Close())
	}
	now := time.Now().UTC().Format(time.RFC3339)
	rec := &CaseRecord{
		CaseID:         caseID,
		RunID:          runID,
		Status:         "starting",
		ComplaintPath:  complaintPath,
		OutputDir:      outDir,
		CaseAPIBase:    caseAPIBase,
		CouncilBackend: councilBackend,
		CreatedAt:      now,
		StdoutLog:      stdoutPath,
		StderrLog:      stderrPath,
		cmd:            cmd,
	}
	s.mu.Lock()
	if _, exists := s.cases[caseID]; exists {
		s.mu.Unlock()
		return CaseRecord{}, errors.Join(fmt.Errorf("case_id already exists"), closeLogs())
	}
	s.cases[caseID] = rec
	s.mu.Unlock()
	if err := s.persistRecord(rec); err != nil {
		s.mu.Lock()
		delete(s.cases, caseID)
		s.mu.Unlock()
		return CaseRecord{}, errors.Join(err, closeLogs())
	}
	if err := cmd.Start(); err != nil {
		s.markFailed(rec, fmt.Sprintf("start child: %v", err))
		return CaseRecord{}, errors.Join(fmt.Errorf("start child: %w", err), closeLogs())
	}
	s.mu.Lock()
	rec.PID = cmd.Process.Pid
	rec.StartedAt = time.Now().UTC().Format(time.RFC3339)
	s.mu.Unlock()
	s.persistRecordBestEffort(rec)

	go s.waitChild(rec, stdoutFile, stderrFile)
	go s.pollCaseAPIStartup(rec, s.cfg.StartupWait)

	if err := ctx.Err(); err != nil {
		return CaseRecord{}, err
	}
	s.mu.Lock()
	out := publicRecord(rec)
	s.mu.Unlock()
	return out, nil
}

func chooseLocalCaseAPIAddr() (string, error) {
	ln, err := net.Listen("tcp", defaultCaseAPIAddr)
	if err != nil {
		return "", fmt.Errorf("choose caseapi address: %w", err)
	}
	addr := ln.Addr().String()
	if err := ln.Close(); err != nil {
		return "", fmt.Errorf("close caseapi address probe: %w", err)
	}
	return addr, nil
}

func (s *Server) pollCaseAPIStartup(rec *CaseRecord, timeout time.Duration) {
	if timeout <= 0 {
		timeout = DefaultCaseStartupWait
	}
	deadline := time.Now().Add(timeout)
	for {
		if !s.caseStillStarting(rec.CaseID) {
			return
		}
		if s.caseAPIHealthy(rec.CaseAPIBase) {
			s.markRunning(rec)
			return
		}
		if !time.Now().Before(deadline) {
			s.markStartupFailed(rec, fmt.Sprintf("case API did not become healthy within %s", timeout))
			return
		}
		time.Sleep(50 * time.Millisecond)
	}
}

func (s *Server) caseStillStarting(caseID string) bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	rec := s.cases[caseID]
	return rec != nil && rec.Status == "starting"
}

func (s *Server) caseAPIHealthy(base string) bool {
	u := strings.TrimRight(strings.TrimSpace(base), "/") + "/health"
	ctx, cancel := context.WithTimeout(context.Background(), 500*time.Millisecond)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, u, nil)
	if err != nil {
		return false
	}
	resp, err := s.client.Do(req)
	if err != nil {
		return false
	}
	defer resp.Body.Close()
	return resp.StatusCode == http.StatusNoContent
}

func (s *Server) markRunning(rec *CaseRecord) {
	s.mu.Lock()
	if rec.Status != "starting" {
		s.mu.Unlock()
		return
	}
	rec.Status = "running"
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistRecordBestEffort(rec)
}

func (s *Server) markStartupFailed(rec *CaseRecord, message string) {
	s.mu.Lock()
	if rec.Status != "starting" {
		s.mu.Unlock()
		return
	}
	rec.Status = "failed"
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistRecordBestEffort(rec)
}

func (s *Server) waitChild(rec *CaseRecord, stdoutFile *os.File, stderrFile *os.File) {
	err := rec.cmd.Wait()
	exitCode := 0
	if err != nil {
		exitCode = 1
		var exitErr *exec.ExitError
		if errors.As(err, &exitErr) {
			exitCode = exitErr.ExitCode()
		}
	}
	logErr := errors.Join(stdoutFile.Close(), stderrFile.Close())
	s.mu.Lock()
	rec.FinishedAt = time.Now().UTC().Format(time.RFC3339)
	rec.ExitCode = &exitCode
	rec.cmd = nil
	rec.PID = 0
	if logErr != nil {
		rec.Error = fmt.Sprintf("close process logs: %v", logErr)
	} else {
		stdoutRaw, readErr := os.ReadFile(rec.StdoutLog)
		if readErr != nil {
			rec.Error = fmt.Sprintf("read stdout log: %v", readErr)
		} else if summary := parseLastJSON(string(stdoutRaw)); summary != nil {
			rec.Summary = summary
		}
	}
	switch {
	case rec.canceling:
		rec.Status = "canceled"
	case logErr != nil:
		rec.Status = "failed"
	case rec.Error != "" && rec.Summary == nil:
		rec.Status = "failed"
	case exitCode == 0 && mapString(rec.Summary["status"]) == "failed":
		rec.Status = "failed"
		rec.Error = mapString(rec.Summary["error"])
	case exitCode == 0:
		rec.Status = "completed"
	default:
		rec.Status = "failed"
		if rec.Error == "" {
			rec.Error = fmt.Sprintf("child exited with code %d", exitCode)
		}
	}
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistRecordBestEffort(rec)
}

func parseLastJSON(stdout string) map[string]any {
	lines := strings.Split(strings.TrimSpace(stdout), "\n")
	for i := len(lines) - 1; i >= 0; i-- {
		line := strings.TrimSpace(lines[i])
		if line == "" {
			continue
		}
		var m map[string]any
		if err := json.Unmarshal([]byte(line), &m); err == nil {
			return m
		}
	}
	return nil
}

func (s *Server) handleCancelCase(w http.ResponseWriter, caseID string) {
	s.mu.Lock()
	rec := s.cases[caseID]
	if rec == nil {
		s.mu.Unlock()
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	rec.canceling = true
	cmd := rec.cmd
	rec.Status = "canceling"
	s.mu.Unlock()
	if cmd != nil && cmd.Process != nil {
		_ = cmd.Process.Signal(os.Interrupt)
		time.Sleep(2 * time.Second)
		if cmd.ProcessState == nil {
			_ = cmd.Process.Kill()
		}
	}
	s.persistRecordBestEffort(rec)
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": publicRecord(rec)})
}

func (s *Server) proxyLawyerGET(w http.ResponseWriter, r *http.Request) {
	caseID := strings.TrimSpace(r.URL.Query().Get("case_id"))
	roleID := strings.TrimSpace(r.URL.Query().Get("role_id"))
	if caseID == "" {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("missing_case_id", "case_id is required")})
		return
	}
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "role_id": roleID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if rec.Status == "running" && rec.CaseAPIBase != "" {
		s.forward(w, r, rec.CaseAPIBase)
		return
	}
	if isActive(rec) {
		s.startingLawyerRead(w, r, rec, roleID)
		return
	}
	s.completedLawyerRead(w, r, rec, roleID)
}

func (s *Server) proxyCouncilGET(w http.ResponseWriter, r *http.Request) {
	caseID := strings.TrimSpace(r.URL.Query().Get("case_id"))
	memberID := strings.TrimSpace(r.URL.Query().Get("member_id"))
	if caseID == "" {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("missing_case_id", "case_id is required")})
		return
	}
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "member_id": memberID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if rec.CouncilBackend != "councilapi" {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "member_id": memberID, "error": apiError("councilapi_unavailable", "case did not start with councilapi backend")})
		return
	}
	if rec.Status == "running" && rec.CaseAPIBase != "" {
		s.forward(w, r, rec.CaseAPIBase)
		return
	}
	if isActive(rec) {
		s.startingCouncilRead(w, r, rec, memberID)
		return
	}
	s.completedCouncilRead(w, r, rec, memberID)
}

func (s *Server) proxyLawyerDo(w http.ResponseWriter, r *http.Request) {
	s.proxyDo(w, r, "lawyer")
}

func (s *Server) proxyCouncilDo(w http.ResponseWriter, r *http.Request) {
	s.proxyDo(w, r, "council")
}

func (s *Server) proxyDo(w http.ResponseWriter, r *http.Request, kind string) {
	if r.Method != http.MethodPost {
		writeJSON(w, http.StatusMethodNotAllowed, map[string]any{"ok": false, "error": apiError("method_not_allowed", "use POST")})
		return
	}
	raw, err := io.ReadAll(http.MaxBytesReader(w, r.Body, defaultMaxProxyBodyBytes))
	if err != nil {
		writeJSON(w, http.StatusRequestEntityTooLarge, map[string]any{"ok": false, "error": apiError("request_too_large", err.Error())})
		return
	}
	var req struct {
		CaseID   string `json:"case_id"`
		RoleID   string `json:"role_id"`
		MemberID string `json:"member_id"`
	}
	if err := json.Unmarshal(raw, &req); err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("bad_json", err.Error())})
		return
	}
	caseID := strings.TrimSpace(req.CaseID)
	if caseID == "" {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("missing_case_id", "case_id is required")})
		return
	}
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if !isActive(rec) {
		writeJSON(w, http.StatusGone, map[string]any{"ok": false, "case_id": caseID, "error": apiError("case_not_active", "case has no active case process for mutating requests")})
		return
	}
	if kind == "council" {
		if rec.CouncilBackend != "councilapi" {
			writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("councilapi_unavailable", "case did not start with councilapi backend")})
			return
		}
	}
	if rec.Status != "running" || rec.CaseAPIBase == "" {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "case_id": caseID, "error": apiError("private_api_unavailable", "private case API is not available")})
		return
	}
	s.forwardRaw(w, r, rec.CaseAPIBase, raw)
}

func (s *Server) forward(w http.ResponseWriter, r *http.Request, base string) {
	target, err := joinBaseAndPath(base, r.URL.Path)
	if err != nil {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "error": apiError("bad_private_api", err.Error())})
		return
	}
	target.RawQuery = r.URL.RawQuery
	req, err := http.NewRequestWithContext(r.Context(), r.Method, target.String(), nil)
	if err != nil {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "error": apiError("proxy_failed", err.Error())})
		return
	}
	resp, err := s.client.Do(req)
	if err != nil {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "error": apiError("private_api_failed", err.Error())})
		return
	}
	defer resp.Body.Close()
	copyResponse(w, resp)
}

func (s *Server) forwardRaw(w http.ResponseWriter, r *http.Request, base string, raw []byte) {
	target, err := joinBaseAndPath(base, r.URL.Path)
	if err != nil {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "error": apiError("bad_private_api", err.Error())})
		return
	}
	req, err := http.NewRequestWithContext(r.Context(), r.Method, target.String(), bytes.NewReader(raw))
	if err != nil {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "error": apiError("proxy_failed", err.Error())})
		return
	}
	req.Header.Set("Content-Type", "application/json")
	resp, err := s.client.Do(req)
	if err != nil {
		writeJSON(w, http.StatusBadGateway, map[string]any{"ok": false, "error": apiError("private_api_failed", err.Error())})
		return
	}
	defer resp.Body.Close()
	copyResponse(w, resp)
}

func joinBaseAndPath(base string, requestPath string) (*url.URL, error) {
	u, err := url.Parse(base)
	if err != nil {
		return nil, err
	}
	basePath := strings.TrimRight(u.Path, "/")
	if basePath == "" {
		u.Path = requestPath
		return u, nil
	}
	suffix := strings.TrimPrefix(requestPath, "/lawyerapi/v1")
	suffix = strings.TrimPrefix(suffix, "/councilapi/v1")
	u.Path = basePath + suffix
	return u, nil
}

func copyResponse(w http.ResponseWriter, resp *http.Response) {
	for key, values := range resp.Header {
		for _, value := range values {
			w.Header().Add(key, value)
		}
	}
	w.WriteHeader(resp.StatusCode)
	_, _ = io.Copy(w, resp.Body)
}

func (s *Server) completedLawyerRead(w http.ResponseWriter, r *http.Request, rec *CaseRecord, roleID string) {
	run, err := readRunJSON(rec)
	if err != nil {
		writeJSON(w, http.StatusGone, map[string]any{"ok": false, "case_id": rec.CaseID, "role_id": roleID, "error": apiError("case_not_active", "case has no active case process and no readable final artifact")})
		return
	}
	switch pathBase(r.URL.Path) {
	case "result":
		writeJSON(w, http.StatusOK, finalResultResponse(rec.CaseID, roleID, run))
	case "wait":
		resp := finalStatusResponse(rec.CaseID, roleID, run, true)
		writeJSON(w, http.StatusOK, resp)
	default:
		writeJSON(w, http.StatusOK, finalStatusResponse(rec.CaseID, roleID, run, false))
	}
}

func (s *Server) completedCouncilRead(w http.ResponseWriter, r *http.Request, rec *CaseRecord, memberID string) {
	run, err := readRunJSON(rec)
	if err != nil {
		writeJSON(w, http.StatusGone, map[string]any{"ok": false, "case_id": rec.CaseID, "member_id": memberID, "error": apiError("case_not_active", "case has no active case process and no readable final artifact")})
		return
	}
	status := "done"
	if mapString(run["status"]) == "failed" || mapString(mapAny(mapAny(run["final_state"])["case"])["status"]) == "failed" {
		status = "failed"
	}
	resp := map[string]any{
		"ok":        true,
		"case_id":   rec.CaseID,
		"member_id": memberID,
		"status":    status,
		"prompt":    "",
		"tools":     []map[string]any{},
		"turn":      nil,
	}
	if status == "failed" {
		resp["error"] = mapString(run["error"])
		resp["failure"] = mapAny(run["failure"])
	}
	if reason := mapString(run["final_reason"]); reason != "" {
		resp["final_reason"] = reason
	}
	if pathBase(r.URL.Path) == "wait" {
		resp["wait"] = map[string]any{"reason": status, "version": 0, "state_version": stateVersionFromRun(run)}
	}
	writeJSON(w, http.StatusOK, resp)
}

func (s *Server) startingLawyerRead(w http.ResponseWriter, r *http.Request, rec *CaseRecord, roleID string) {
	resp := map[string]any{
		"ok":                  true,
		"case_id":             rec.CaseID,
		"role_id":             roleID,
		"status":              "waiting",
		"case_status":         rec.Status,
		"phase":               "starting",
		"prompt":              "",
		"tools":               []map[string]any{},
		"turn":                nil,
		"current_opportunity": nil,
		"message":             "The case process is starting.",
	}
	if pathBase(r.URL.Path) == "wait" {
		resp["wait"] = map[string]any{"reason": "starting", "version": 0}
	}
	writeJSON(w, http.StatusOK, resp)
}

func (s *Server) startingCouncilRead(w http.ResponseWriter, r *http.Request, rec *CaseRecord, memberID string) {
	resp := map[string]any{
		"ok":        true,
		"case_id":   rec.CaseID,
		"member_id": memberID,
		"status":    "waiting",
		"phase":     "starting",
		"prompt":    "",
		"tools":     []map[string]any{},
		"turn":      nil,
		"message":   "The case process is starting.",
	}
	if pathBase(r.URL.Path) == "wait" {
		resp["wait"] = map[string]any{"reason": "starting", "version": 0}
	}
	writeJSON(w, http.StatusOK, resp)
}

func finalStatusResponse(caseID string, roleID string, run map[string]any, includeWait bool) map[string]any {
	caseObj := mapAny(mapAny(run["final_state"])["case"])
	status := "done"
	message := "The case is done."
	if mapString(run["status"]) == "failed" || mapString(caseObj["status"]) == "failed" {
		status = "failed"
		message = "The case failed."
	}
	resp := map[string]any{
		"ok":                  true,
		"case_id":             caseID,
		"role_id":             roleID,
		"status":              status,
		"phase":               mapString(run["phase"]),
		"case_status":         mapString(caseObj["status"]),
		"resolution":          mapString(run["resolution"]),
		"prompt":              "",
		"tools":               []map[string]any{},
		"turn":                nil,
		"current_opportunity": nil,
		"message":             message,
	}
	if status == "failed" {
		resp["error"] = mapString(run["error"])
		resp["failure"] = mapAny(run["failure"])
	}
	if reason := mapString(run["final_reason"]); reason != "" {
		resp["final_reason"] = reason
	}
	if includeWait {
		resp["wait"] = map[string]any{"reason": status, "version": 0, "state_version": stateVersionFromRun(run)}
	}
	return resp
}

func finalResultResponse(caseID string, roleID string, run map[string]any) map[string]any {
	finalState := mapAny(run["final_state"])
	caseObj := mapAny(finalState["case"])
	votes := mapList(caseObj["council_votes"])
	status := "done"
	if mapString(run["status"]) == "failed" || mapString(caseObj["status"]) == "failed" {
		status = "failed"
	}
	resp := map[string]any{
		"ok":          true,
		"case_id":     caseID,
		"role_id":     roleID,
		"turn":        nil,
		"phase":       mapString(run["phase"]),
		"case_status": mapString(caseObj["status"]),
		"status":      status,
		"result": map[string]any{
			"resolution":         mapString(run["resolution"]),
			"phase":              mapString(run["phase"]),
			"case_status":        mapString(caseObj["status"]),
			"final_reason":       mapString(run["final_reason"]),
			"council_votes":      votes,
			"vote_tally":         voteTally(votes),
			"deliberation_round": intNumber(caseObj["deliberation_round"]),
		},
	}
	if status == "failed" {
		resp["error"] = mapString(run["error"])
		resp["failure"] = mapAny(run["failure"])
		resp["result"] = nil
	}
	if reason := mapString(run["final_reason"]); reason != "" {
		resp["final_reason"] = reason
	}
	return resp
}

func (s *Server) handleCaseResult(w http.ResponseWriter, caseID string) {
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if rec.Status == "running" && rec.CaseAPIBase != "" {
		u := strings.TrimRight(rec.CaseAPIBase, "/") + "/lawyerapi/v1/result?case_id=" + url.QueryEscape(caseID) + "&role_id=observer"
		req, err := http.NewRequest(http.MethodGet, u, nil)
		if err == nil {
			resp, err := s.client.Do(req)
			if err == nil {
				defer resp.Body.Close()
				copyResponse(w, resp)
				return
			}
		}
	}
	run, err := readRunJSON(rec)
	if err != nil {
		if rec.Status == "failed" {
			writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case_id": caseID, "status": "failed", "error": rec.Error})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case_id": caseID, "status": rec.Status, "message": "The case is still pending or has no final result."})
		return
	}
	writeJSON(w, http.StatusOK, finalResultResponse(caseID, "observer", run))
}

func readRunJSON(rec *CaseRecord) (map[string]any, error) {
	return readRunJSONFromDir(rec.OutputDir)
}

func readRunJSONFromDir(outDir string) (map[string]any, error) {
	raw, err := os.ReadFile(filepath.Join(outDir, "run.json"))
	if err != nil {
		return nil, err
	}
	var run map[string]any
	if err := json.Unmarshal(raw, &run); err != nil {
		return nil, err
	}
	return run, nil
}

func (s *Server) handleArtifact(w http.ResponseWriter, r *http.Request, caseID string, name string) {
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if name == "" {
		files, err := listArtifacts(rec.OutputDir)
		if err != nil {
			writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("artifact_list_failed", err.Error())})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case_id": caseID, "artifacts": files})
		return
	}
	serveListedArtifactFile(w, r, caseID, rec.OutputDir, name)
}

func (s *Server) handleEvidence(w http.ResponseWriter, r *http.Request, caseID string, evidenceID string) {
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	serveEvidenceFile(w, r, caseID, rec.OutputDir, evidenceID, rec.Status == "starting" || rec.Status == "running")
}

func serveEvidenceFile(w http.ResponseWriter, r *http.Request, caseID string, outDir string, evidenceID string, pending bool) {
	manifestPath := filepath.Join(outDir, "evidence-manifest.json")
	raw, err := os.ReadFile(manifestPath)
	if err != nil {
		if pending && os.IsNotExist(err) {
			writeJSON(w, http.StatusConflict, map[string]any{"ok": false, "case_id": caseID, "error": apiError("evidence_manifest_pending", "evidence manifest is not available yet; try again after the case accepts evidence or writes its output packet")})
			return
		}
		if os.IsNotExist(err) {
			writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("manifest_missing", "evidence manifest is missing from the output packet: "+manifestPath)})
			return
		}
		writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("manifest_unreadable", "read evidence manifest: "+err.Error())})
		return
	}
	manifest, err := parseEvidenceManifest(raw)
	if err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("bad_manifest", "parse evidence manifest: "+err.Error())})
		return
	}
	for _, item := range manifest {
		if mapString(item["evidence_id"]) == evidenceID {
			name := evidenceFileArtifactName(item)
			if name == "" {
				writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "evidence_id": evidenceID, "error": apiError("evidence_path_missing", "manifest item has no readable file name")})
				return
			}
			serveOutputFile(w, r, caseID, outDir, name)
			return
		}
	}
	writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "evidence_id": evidenceID, "error": apiError("unknown_evidence", "evidence_id is not listed in the evidence manifest")})
}

func parseEvidenceManifest(raw []byte) ([]map[string]any, error) {
	var legacy []map[string]any
	if err := json.Unmarshal(raw, &legacy); err == nil {
		return legacy, nil
	}
	var current struct {
		Evidence []map[string]any `json:"evidence"`
	}
	if err := json.Unmarshal(raw, &current); err != nil {
		return nil, err
	}
	if current.Evidence == nil {
		return nil, fmt.Errorf("manifest has no evidence array")
	}
	return current.Evidence, nil
}

func evidenceFileArtifactName(item map[string]any) string {
	if storageName := mapString(item["storage_name"]); storageName != "" {
		return filepath.Join("evidence-store", storageName)
	}
	name := mapString(item["name"])
	if name == "" {
		name = mapString(item["original_name"])
	}
	if name == "" {
		return ""
	}
	return filepath.Join("submitted-evidence", name)
}

func (s *Server) serveCaseFile(w http.ResponseWriter, r *http.Request, rec *CaseRecord, name string) {
	serveOutputFile(w, r, rec.CaseID, rec.OutputDir, name)
}

func serveOutputFile(w http.ResponseWriter, r *http.Request, caseID string, outDir string, name string) {
	path, err := safeArtifactPath(outDir, name)
	if err != nil {
		writeArtifactAccessError(w, caseID, name, err)
		return
	}
	http.ServeFile(w, r, path)
}

func serveListedArtifactFile(w http.ResponseWriter, r *http.Request, caseID string, outDir string, name string) {
	if !listedArtifactName(name) {
		writeUnknownArtifact(w, caseID, name)
		return
	}
	serveOutputFile(w, r, caseID, outDir, name)
}

func writeUnknownArtifact(w http.ResponseWriter, caseID string, name string) {
	writeJSON(w, http.StatusNotFound, map[string]any{
		"ok":            false,
		"case_id":       caseID,
		"artifact_name": name,
		"error":         apiError("unknown_artifact", "unknown artifact"),
	})
}

func writeArtifactAccessError(w http.ResponseWriter, caseID string, name string, err error) {
	if errors.Is(err, os.ErrNotExist) {
		writeJSON(w, http.StatusNotFound, map[string]any{
			"ok":            false,
			"case_id":       caseID,
			"artifact_name": name,
			"error":         apiError("artifact_missing", "artifact is not available"),
		})
		return
	}
	writeJSON(w, http.StatusBadRequest, map[string]any{
		"ok":            false,
		"case_id":       caseID,
		"artifact_name": name,
		"error":         apiError("bad_artifact_path", "artifact path is invalid"),
	})
}

func safeArtifactPath(root string, name string) (string, error) {
	name = strings.TrimPrefix(filepath.Clean("/"+name), "/")
	if name == "" || strings.HasPrefix(name, "..") {
		return "", fmt.Errorf("artifact path is invalid")
	}
	rootAbs, err := filepath.Abs(root)
	if err != nil {
		return "", err
	}
	path := filepath.Join(rootAbs, name)
	eval, err := filepath.EvalSymlinks(path)
	if err != nil {
		return "", err
	}
	if !strings.HasPrefix(eval, rootAbs+string(os.PathSeparator)) && eval != rootAbs {
		return "", fmt.Errorf("artifact path escapes case output directory")
	}
	return eval, nil
}

func listArtifacts(root string) ([]map[string]any, error) {
	var out []map[string]any
	for _, name := range listedArtifactNames() {
		path, err := safeArtifactPath(root, name)
		if err != nil {
			continue
		}
		st, err := os.Stat(path)
		if err != nil {
			continue
		}
		out = append(out, map[string]any{"name": name, "size_bytes": st.Size()})
	}
	return out, nil
}

func listedArtifactNames() []string {
	return []string{"run.json", "certificate.json", "digest.md", "transcript.md", "work-notes.ndjson", "events.ndjson", "evidence-manifest.json", "service-logs/aar.stdout", "service-logs/aar.stderr"}
}

func listedArtifactName(name string) bool {
	for _, allowed := range listedArtifactNames() {
		if name == allowed {
			return true
		}
	}
	return false
}

func (s *Server) getCase(caseID string) (CaseRecord, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	rec := s.cases[caseID]
	if rec == nil {
		return CaseRecord{}, false
	}
	return publicRecord(rec), true
}

func (s *Server) getCasePtr(caseID string) (*CaseRecord, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	rec := s.cases[caseID]
	return rec, rec != nil
}

func isActive(rec *CaseRecord) bool {
	return rec.Status == "starting" || rec.Status == "running" || rec.Status == "canceling"
}

func publicRecord(rec *CaseRecord) CaseRecord {
	out := *rec
	out.cmd = nil
	out.canceling = false
	return out
}

func (s *Server) markFailed(rec *CaseRecord, message string) {
	s.mu.Lock()
	rec.Status = "failed"
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistRecordBestEffort(rec)
}

func (s *Server) persistRecord(rec *CaseRecord) error {
	public := publicRecord(rec)
	raw, err := json.MarshalIndent(public, "", "  ")
	if err != nil {
		return err
	}
	tmp := filepath.Join(s.cfg.RegistryDir, public.CaseID+".json.tmp")
	final := filepath.Join(s.cfg.RegistryDir, public.CaseID+".json")
	if err := os.WriteFile(tmp, raw, 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, final)
}

func (s *Server) persistRecordBestEffort(rec *CaseRecord) {
	_ = s.persistRecord(rec)
}

func (s *Server) loadRegistry() error {
	entries, err := os.ReadDir(s.cfg.RegistryDir)
	if err != nil {
		return err
	}
	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".json") {
			continue
		}
		raw, err := os.ReadFile(filepath.Join(s.cfg.RegistryDir, entry.Name()))
		if err != nil {
			return err
		}
		var rec CaseRecord
		if err := json.Unmarshal(raw, &rec); err != nil {
			return err
		}
		if rec.CaseID == "" {
			continue
		}
		if isActive(&rec) || rec.Error == detachedProcessMessage {
			reconciled, changed := reconcileDetachedCaseRecord(rec)
			rec = reconciled
			if changed {
				if err := s.persistRecord(&rec); err != nil {
					return err
				}
			}
		}
		s.cases[rec.CaseID] = &rec
	}
	return nil
}

func reconcileDetachedCaseRecord(rec CaseRecord) (CaseRecord, bool) {
	if !isActive(&rec) && rec.Error != detachedProcessMessage {
		return rec, false
	}
	original := rec
	if run, err := readRunJSON(&rec); err == nil {
		applyRunJSONToRecord(&rec, run)
	} else if isActive(&rec) {
		rec.Status = "failed"
		rec.PID = 0
		rec.cmd = nil
		rec.canceling = false
		if rec.Error == "" {
			rec.Error = detachedProcessMessage
		}
	}
	return rec, caseRecordChanged(original, rec)
}

func applyRunJSONToRecord(rec *CaseRecord, run map[string]any) {
	rec.PID = 0
	rec.cmd = nil
	rec.canceling = false
	rec.Summary = run
	if finishedAt := mapString(run["finished_at"]); finishedAt != "" {
		rec.FinishedAt = finishedAt
	}
	if mapString(run["status"]) == "failed" || mapString(mapAny(mapAny(run["final_state"])["case"])["status"]) == "failed" {
		rec.Status = "failed"
		rec.Error = firstNonEmpty(mapString(run["error"]), "case wrote failed run.json")
		return
	}
	rec.Status = "completed"
	rec.Error = ""
}

func caseRecordChanged(a CaseRecord, b CaseRecord) bool {
	return a.Status != b.Status ||
		a.PID != b.PID ||
		a.FinishedAt != b.FinishedAt ||
		a.Error != b.Error ||
		!reflect.DeepEqual(a.Summary, b.Summary)
}

func validateID(value string, name string) error {
	if value == "" {
		return fmt.Errorf("%s is required", name)
	}
	if value == "." || value == ".." {
		return fmt.Errorf("%s is invalid", name)
	}
	for _, r := range value {
		if r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || r == '-' || r == '_' || r == '.' {
			continue
		}
		return fmt.Errorf("%s contains invalid character %q", name, r)
	}
	return nil
}

func validateServiceOutputDir(outputRoot string, outDir string) error {
	rootAbs, err := filepath.Abs(strings.TrimSpace(outputRoot))
	if err != nil {
		return fmt.Errorf("resolve output root: %w", err)
	}
	outAbs, err := filepath.Abs(strings.TrimSpace(outDir))
	if err != nil {
		return fmt.Errorf("resolve out_dir: %w", err)
	}
	if filepath.Dir(outAbs) != rootAbs {
		return fmt.Errorf("out_dir must be an immediate child of the service output root")
	}
	if filepath.Base(outAbs) == "." || filepath.Base(outAbs) == string(os.PathSeparator) {
		return fmt.Errorf("out_dir is invalid")
	}
	return nil
}

func randomHex(bytesLen int) string {
	raw := make([]byte, bytesLen)
	if _, err := rand.Read(raw); err != nil {
		return fmt.Sprintf("%d", time.Now().UTC().UnixNano())
	}
	return hex.EncodeToString(raw)
}

func firstNonEmpty(values ...string) string {
	for _, value := range values {
		if strings.TrimSpace(value) != "" {
			return strings.TrimSpace(value)
		}
	}
	return ""
}

func pathBase(path string) string {
	return strings.TrimPrefix(filepath.Base(path), "/")
}

func writeJSON(w http.ResponseWriter, status int, value map[string]any) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(value)
}

func apiError(code string, message string) map[string]any {
	return map[string]any{"code": code, "message": message}
}

func mapAny(value any) map[string]any {
	if m, ok := value.(map[string]any); ok {
		return m
	}
	return map[string]any{}
}

func mapList(value any) []map[string]any {
	switch v := value.(type) {
	case []map[string]any:
		return v
	case []any:
		out := make([]map[string]any, 0, len(v))
		for _, item := range v {
			out = append(out, mapAny(item))
		}
		return out
	default:
		return nil
	}
}

func mapString(value any) string {
	if value == nil {
		return ""
	}
	if s, ok := value.(string); ok {
		return s
	}
	return fmt.Sprintf("%v", value)
}

func intNumber(value any) int {
	switch v := value.(type) {
	case int:
		return v
	case int64:
		return int(v)
	case float64:
		return int(v)
	case json.Number:
		n, _ := v.Int64()
		return int(n)
	default:
		return 0
	}
}

func stateVersionFromRun(run map[string]any) int {
	return intNumber(mapAny(run["final_state"])["state_version"])
}

func voteTally(votes []map[string]any) map[string]any {
	counts := map[string]int{}
	for _, vote := range votes {
		counts[mapString(vote["vote"])]++
	}
	return map[string]any{
		"demonstrated":     counts["demonstrated"],
		"not_demonstrated": counts["not_demonstrated"],
	}
}
