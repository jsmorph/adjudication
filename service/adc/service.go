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
	DefaultListenAddr      = "127.0.0.1:19870"
	DefaultCaseStartupWait = 30 * time.Second

	defaultMaxProxyBodyBytes = 32 << 20
	detachedProcessMessage   = "service restarted and child process is not attached"
)

type Config struct {
	ListenAddr  string
	OutputRoot  string
	ADCBin      string
	CommonRoot  string
	EnginePath  string
	BearerToken string
	Attested    AttestedClerkConfig
	StartupWait time.Duration
	Log         io.Writer
}

type Server struct {
	cfg    Config
	mu     sync.Mutex
	cond   *sync.Cond
	cases  map[string]*CaseRecord
	client *http.Client
}

type CaseCreateRequest struct {
	Mode                      string                 `json:"mode,omitempty"`
	CaseID                    string                 `json:"case_id,omitempty"`
	RunID                     string                 `json:"run_id,omitempty"`
	ComplaintPath             string                 `json:"complaint_path"`
	ScenarioPath              string                 `json:"scenario_path,omitempty"`
	OutputDir                 string                 `json:"out_dir,omitempty"`
	Court                     string                 `json:"court,omitempty"`
	Model                     string                 `json:"model,omitempty"`
	NonJurorModel             string                 `json:"non_juror_model,omitempty"`
	PlaintiffModel            string                 `json:"plaintiff_model,omitempty"`
	DefendantModel            string                 `json:"defendant_model,omitempty"`
	JudgeModel                string                 `json:"judge_model,omitempty"`
	ClerkModel                string                 `json:"clerk_model,omitempty"`
	PlannerModel              string                 `json:"planner_model,omitempty"`
	ReportModel               string                 `json:"report_model,omitempty"`
	Temperature               string                 `json:"temperature,omitempty"`
	NonJurorTemperature       string                 `json:"non_juror_temperature,omitempty"`
	JurorTemperature          string                 `json:"juror_temperature,omitempty"`
	JurorPersonas             string                 `json:"juror_personas,omitempty"`
	TrialMode                 string                 `json:"trial_mode,omitempty"`
	SkipVoirDire              bool                   `json:"skip_voir_dire,omitempty"`
	JurorCount                int                    `json:"juror_count,omitempty"`
	MinimumConcurring         int                    `json:"minimum_concurring,omitempty"`
	UnanimousRequired         *bool                  `json:"unanimous_required,omitempty"`
	Online                    bool                   `json:"online,omitempty"`
	Offline                   bool                   `json:"offline,omitempty"`
	TimeoutSeconds            int                    `json:"timeout_seconds,omitempty"`
	RoleAPITimeoutSeconds     int                    `json:"roleapi_timeout_seconds,omitempty"`
	LawyerTimeoutSeconds      int                    `json:"lawyer_timeout_seconds,omitempty"`
	JurorTimeoutSeconds       int                    `json:"juror_timeout_seconds,omitempty"`
	InvalidAttemptLimit       int                    `json:"invalid_attempt_limit,omitempty"`
	MaxResponseBytes          int                    `json:"max_response_bytes,omitempty"`
	EnginePath                string                 `json:"engine_path,omitempty"`
	ExternalRoles             []string               `json:"external_roles,omitempty"`
	MCPListenAddr             string                 `json:"mcp_listen,omitempty"`
	MCPPublicBaseURL          string                 `json:"mcp_public_base_url,omitempty"`
	MCPBearerToken            string                 `json:"mcp_bearer_token,omitempty"`
	LawyerInstructions        string                 `json:"lawyer_instructions,omitempty"`
	RemoteLawyerSkill         string                 `json:"remote_lawyer_skill,omitempty"`
	JurorInstructions         string                 `json:"juror_instructions,omitempty"`
	AutoLawyers               string                 `json:"auto_lawyers,omitempty"`
	DockerCommand             string                 `json:"docker_command,omitempty"`
	PodmanCommand             string                 `json:"podman_command,omitempty"`
	OpenClawImage             string                 `json:"openclaw_image,omitempty"`
	OpenClawModel             string                 `json:"openclaw_model,omitempty"`
	OpenClawThinking          string                 `json:"openclaw_thinking,omitempty"`
	OpenClawTimeoutSeconds    int                    `json:"openclaw_timeout_seconds,omitempty"`
	OpenClawAuth              string                 `json:"openclaw_auth,omitempty"`
	OpenClawCodexAuthPath     string                 `json:"openclaw_codex_auth_path,omitempty"`
	OpenClawStartDelaySeconds *int                   `json:"openclaw_lawyer_start_delay_seconds,omitempty"`
	PiImage                   string                 `json:"pi_image,omitempty"`
	PiMCPAdapter              string                 `json:"pi_mcp_adapter,omitempty"`
	JurorOutputLimitBytes     int64                  `json:"juror_output_limit_bytes,omitempty"`
	DockerMCPHost             string                 `json:"docker_mcp_host,omitempty"`
	PodmanMCPHost             string                 `json:"podman_mcp_host,omitempty"`
	Execution                 *ClerkExecutionRequest `json:"execution,omitempty"`
}

type CaseRecord struct {
	Mode          string                `json:"mode"`
	CaseID        string                `json:"case_id"`
	RunID         string                `json:"run_id"`
	PID           int                   `json:"pid,omitempty"`
	Status        string                `json:"status"`
	ComplaintPath string                `json:"complaint_path"`
	ScenarioPath  string                `json:"scenario_path,omitempty"`
	OutputDir     string                `json:"out_dir"`
	CaseAPIBase   string                `json:"caseapi_base,omitempty"`
	CreatedAt     string                `json:"created_at"`
	StartedAt     string                `json:"started_at,omitempty"`
	FinishedAt    string                `json:"finished_at,omitempty"`
	ExitCode      *int                  `json:"exit_code,omitempty"`
	Summary       map[string]any        `json:"summary,omitempty"`
	Error         string                `json:"error,omitempty"`
	StdoutLog     string                `json:"stdout_log,omitempty"`
	StderrLog     string                `json:"stderr_log,omitempty"`
	Execution     *ClerkExecutionRecord `json:"execution,omitempty"`

	killing bool
	cmd     *exec.Cmd
}

func New(cfg Config) (*Server, error) {
	cfg.ListenAddr = strings.TrimSpace(cfg.ListenAddr)
	if cfg.ListenAddr == "" {
		cfg.ListenAddr = DefaultListenAddr
	}
	if strings.TrimSpace(cfg.OutputRoot) == "" {
		return nil, fmt.Errorf("output root is required")
	}
	if strings.TrimSpace(cfg.ADCBin) == "" {
		return nil, fmt.Errorf("adc binary path is required")
	}
	if cfg.StartupWait <= 0 {
		cfg.StartupWait = DefaultCaseStartupWait
	}
	if err := os.MkdirAll(cfg.OutputRoot, 0o755); err != nil {
		return nil, fmt.Errorf("create output root: %w", err)
	}
	s := &Server{
		cfg:   cfg,
		cases: map[string]*CaseRecord{},
		client: &http.Client{
			Timeout: 10 * time.Minute,
		},
	}
	s.cond = sync.NewCond(&s.mu)
	if err := s.loadCaseRecords(); err != nil {
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
		fmt.Fprintf(cfg.Log, "adc service listening on http://%s\n", ln.Addr().String())
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
	mux.HandleFunc("/clerk/v1/cases", s.handleCases)
	mux.HandleFunc("/clerk/v1/cases/", s.handleClerkCaseCompat)
	mux.HandleFunc("/api/v1/cases", s.handleCases)
	mux.HandleFunc("/api/v1/cases/", s.handleCase)
	mux.HandleFunc("/roleapi/v1/get", s.proxyRoleAPI)
	mux.HandleFunc("/roleapi/v1/wait_for_opportunity", s.proxyRoleAPI)
	mux.HandleFunc("/roleapi/v1/status", s.proxyRoleAPI)
	mux.HandleFunc("/roleapi/v1/result", s.proxyRoleAPI)
	mux.HandleFunc("/roleapi/v1/do", s.proxyRoleAPI)
	mux.HandleFunc("/roleapi/v1/fail", s.proxyRoleAPI)
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
		public := publicRecord(rec)
		public.Summary = nil
		records = append(records, public)
	}
	s.mu.Unlock()
	sort.Slice(records, func(i, j int) bool {
		return records[i].CreatedAt < records[j].CreatedAt
	})
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "cases": records})
}

func (s *Server) handleClerkCaseCompat(w http.ResponseWriter, r *http.Request) {
	r2 := r.Clone(r.Context())
	u := *r.URL
	u.Path = "/api/v1/cases/" + strings.TrimPrefix(r.URL.Path, "/clerk/v1/cases/")
	r2.URL = &u
	s.handleCase(w, r2)
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
	if len(parts) == 2 && parts[1] == "kill" && r.Method == http.MethodPost {
		s.handleKillCase(w, caseID)
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
	if len(parts) == 3 && parts[1] == "attestation" && parts[2] == "events" && r.Method == http.MethodGet {
		s.handleCaseAttestationEvents(w, r, caseID)
		return
	}
	writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("not_found", "unknown case route")})
}

func (s *Server) startCase(ctx context.Context, req CaseCreateRequest) (CaseRecord, error) {
	if err := ctx.Err(); err != nil {
		return CaseRecord{}, err
	}
	mode := normalizeCreateMode(req.Mode)
	if mode != "run" && mode != "direct" {
		return CaseRecord{}, fmt.Errorf("mode must be run or direct")
	}
	if req.OpenClawStartDelaySeconds != nil && *req.OpenClawStartDelaySeconds < 0 {
		return CaseRecord{}, fmt.Errorf("openclaw_lawyer_start_delay_seconds must be non-negative")
	}
	if err := validateJuryConfigRequest(req); err != nil {
		return CaseRecord{}, err
	}
	caseID := strings.TrimSpace(req.CaseID)
	if caseID == "" {
		caseID = "adc-" + time.Now().UTC().Format("20060102150405") + "-" + randomHex(4)
	}
	if err := validateID(caseID, "case_id"); err != nil {
		return CaseRecord{}, err
	}
	runID := strings.TrimSpace(req.RunID)
	if runID == "" {
		runID = "run-" + caseID
	}
	complaintPath := strings.TrimSpace(req.ComplaintPath)
	scenarioPath := strings.TrimSpace(req.ScenarioPath)
	switch {
	case complaintPath == "" && scenarioPath == "":
		return CaseRecord{}, fmt.Errorf("complaint_path or scenario_path is required")
	case complaintPath != "" && scenarioPath != "":
		return CaseRecord{}, fmt.Errorf("provide complaint_path or scenario_path, not both")
	}
	if complaintPath != "" {
		if _, err := os.Stat(complaintPath); err != nil {
			return CaseRecord{}, fmt.Errorf("complaint_path: %w", err)
		}
		if req.Offline {
			return CaseRecord{}, fmt.Errorf("offline mode cannot prepare a complaint-based case")
		}
	}
	if scenarioPath != "" {
		if _, err := os.Stat(scenarioPath); err != nil {
			return CaseRecord{}, fmt.Errorf("scenario_path: %w", err)
		}
	}
	execution, err := s.resolveCaseExecution(req, mode, runID)
	if err != nil {
		return CaseRecord{}, err
	}
	isAttested := execution != nil && execution.Mode == clerkExecutionAttested
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

	caseAPIAddr := ""
	caseAPIBase := ""
	var commandPath string
	var args []string
	if !isAttested {
		var err error
		caseAPIAddr, err = chooseLocalCaseAPIAddr()
		if err != nil {
			return CaseRecord{}, err
		}
		caseAPIBase = "http://" + caseAPIAddr
		args = s.caseProcessArgs(mode, req, caseID, runID, outDir, caseAPIAddr, complaintPath, scenarioPath)
		commandPath = s.cfg.ADCBin
	}

	stdoutPath := filepath.Join(logDir, "adc.stdout")
	stderrPath := filepath.Join(logDir, "adc.stderr")
	stdoutFile, err := os.Create(stdoutPath)
	if err != nil {
		return CaseRecord{}, fmt.Errorf("create stdout log: %w", err)
	}
	stderrFile, err := os.Create(stderrPath)
	if err != nil {
		return CaseRecord{}, errors.Join(fmt.Errorf("create stderr log: %w", err), stdoutFile.Close())
	}
	closeLogFiles := func() error {
		return errors.Join(stdoutFile.Close(), stderrFile.Close())
	}

	now := time.Now().UTC().Format(time.RFC3339)
	rec := &CaseRecord{
		Mode:          mode,
		CaseID:        caseID,
		RunID:         runID,
		Status:        "starting",
		ComplaintPath: complaintPath,
		ScenarioPath:  scenarioPath,
		OutputDir:     outDir,
		CaseAPIBase:   caseAPIBase,
		CreatedAt:     now,
		StdoutLog:     stdoutPath,
		StderrLog:     stderrPath,
		Execution:     execution,
	}
	if isAttested {
		commandPath, args, err = attestedCaseCommand(req, rec, outDir)
		if err != nil {
			return CaseRecord{}, errors.Join(err, closeLogFiles())
		}
	}
	cmd := exec.CommandContext(context.Background(), commandPath, args...)
	rec.cmd = cmd
	cmd.Stdout = stdoutFile
	cmd.Stderr = stderrFile
	s.mu.Lock()
	if _, exists := s.cases[caseID]; exists {
		s.mu.Unlock()
		return CaseRecord{}, errors.Join(fmt.Errorf("case_id already exists"), closeLogFiles())
	}
	s.cases[caseID] = rec
	s.mu.Unlock()
	if err := s.persistRecord(rec); err != nil {
		s.mu.Lock()
		delete(s.cases, caseID)
		s.mu.Unlock()
		return CaseRecord{}, errors.Join(err, closeLogFiles())
	}
	if err := cmd.Start(); err != nil {
		startErr := fmt.Errorf("start child: %w", err)
		markErr := s.markFailed(rec, fmt.Sprintf("start child: %v", err))
		return CaseRecord{}, errors.Join(startErr, markErr, closeLogFiles())
	}
	go s.waitChild(rec, stdoutFile, stderrFile)
	s.mu.Lock()
	rec.PID = cmd.Process.Pid
	rec.StartedAt = time.Now().UTC().Format(time.RFC3339)
	if isAttested {
		rec.Status = "running"
	}
	s.mu.Unlock()
	if err := s.persistRecord(rec); err != nil {
		stopErr := stopProcess(cmd, 2*time.Second)
		s.setRecordError(rec, "failed", fmt.Sprintf("persist service record: %v", err))
		return CaseRecord{}, errors.Join(fmt.Errorf("persist service record: %w", err), stopErr)
	}
	if !isAttested {
		go s.pollCaseAPIStartup(rec, s.cfg.StartupWait)
	}

	s.mu.Lock()
	out := publicRecord(rec)
	s.mu.Unlock()
	return out, nil
}

func (s *Server) caseProcessArgs(mode string, req CaseCreateRequest, caseID string, runID string, outDir string, caseAPIAddr string, complaintPath string, scenarioPath string) []string {
	mode = normalizeCreateMode(mode)
	addString := func(args []string, name string, value string) []string {
		if strings.TrimSpace(value) == "" {
			return args
		}
		return append(args, name, strings.TrimSpace(value))
	}
	addInt := func(args []string, name string, value int) []string {
		if value <= 0 {
			return args
		}
		return append(args, name, fmt.Sprintf("%d", value))
	}
	addInt64 := func(args []string, name string, value int64) []string {
		if value <= 0 {
			return args
		}
		return append(args, name, fmt.Sprintf("%d", value))
	}
	addBoolPtr := func(args []string, name string, value *bool) []string {
		if value == nil {
			return args
		}
		return append(args, name, fmt.Sprintf("%t", *value))
	}
	addCommon := func(args []string) []string {
		args = addString(args, "--model", req.Model)
		args = addString(args, "--temperature", req.Temperature)
		args = addString(args, "--juror-personas", req.JurorPersonas)
		args = addString(args, "--engine", firstNonEmpty(req.EnginePath, s.cfg.EnginePath))
		args = addInt(args, "--timeout-seconds", req.TimeoutSeconds)
		args = addInt(args, "--invalid-attempt-limit", req.InvalidAttemptLimit)
		args = addInt(args, "--max-response-bytes", req.MaxResponseBytes)
		args = addInt(args, "--juror-count", req.JurorCount)
		args = addInt(args, "--minimum-concurring", req.MinimumConcurring)
		args = addBoolPtr(args, "--unanimous-required", req.UnanimousRequired)
		if req.Online {
			args = append(args, "--online")
		}
		return args
	}
	addDirectCommon := func(args []string) []string {
		args = addCommon(args)
		args = addInt(args, "--roleapi-timeout-seconds", req.RoleAPITimeoutSeconds)
		for _, role := range req.ExternalRoles {
			if strings.TrimSpace(role) != "" {
				args = append(args, "--external-role", strings.TrimSpace(role))
			}
		}
		return args
	}
	addComplaintSetup := func(args []string) []string {
		args = addString(args, "--court", req.Court)
		args = addString(args, "--non-juror-model", req.NonJurorModel)
		args = addString(args, "--plaintiff-model", req.PlaintiffModel)
		args = addString(args, "--defendant-model", req.DefendantModel)
		args = addString(args, "--judge-model", req.JudgeModel)
		args = addString(args, "--clerk-model", req.ClerkModel)
		args = addString(args, "--planner-model", req.PlannerModel)
		args = addString(args, "--report-model", req.ReportModel)
		args = addString(args, "--non-juror-temperature", req.NonJurorTemperature)
		args = addString(args, "--juror-temperature", req.JurorTemperature)
		args = addString(args, "--trial-mode", req.TrialMode)
		if req.SkipVoirDire {
			args = append(args, "--skip-voir-dire")
		}
		return args
	}

	if mode == "run" {
		args := []string{
			"run",
			"--case-id", caseID,
			"--run-id", runID,
			"--out-dir", outDir,
			"--caseapi-addr", caseAPIAddr,
		}
		if strings.TrimSpace(scenarioPath) != "" {
			args = append(args, "--scenario", strings.TrimSpace(scenarioPath))
		} else {
			args = append(args, "--complaint", strings.TrimSpace(complaintPath))
			args = addComplaintSetup(args)
		}
		args = addCommon(args)
		if req.Offline {
			args = append(args, "--offline")
		}
		args = addString(args, "--mcp-listen", req.MCPListenAddr)
		args = addString(args, "--mcp-public-base-url", req.MCPPublicBaseURL)
		args = addString(args, "--mcp-bearer-token", req.MCPBearerToken)
		args = addInt(args, "--lawyer-timeout-seconds", firstPositive(req.LawyerTimeoutSeconds, req.RoleAPITimeoutSeconds))
		args = addInt(args, "--juror-timeout-seconds", firstPositive(req.JurorTimeoutSeconds, req.RoleAPITimeoutSeconds))
		args = addString(args, "--lawyer-instructions", req.LawyerInstructions)
		args = addString(args, "--remote-lawyer-skill", req.RemoteLawyerSkill)
		args = addString(args, "--juror-instructions", req.JurorInstructions)
		args = addString(args, "--auto-lawyers", req.AutoLawyers)
		args = addString(args, "--docker", req.DockerCommand)
		args = addString(args, "--podman", req.PodmanCommand)
		args = addString(args, "--openclaw-image", req.OpenClawImage)
		args = addString(args, "--openclaw-model", req.OpenClawModel)
		args = addString(args, "--openclaw-thinking", req.OpenClawThinking)
		args = addInt(args, "--openclaw-timeout-seconds", req.OpenClawTimeoutSeconds)
		args = addString(args, "--openclaw-auth", req.OpenClawAuth)
		args = addString(args, "--openclaw-codex-auth", req.OpenClawCodexAuthPath)
		if req.OpenClawStartDelaySeconds != nil {
			args = append(args, "--openclaw-lawyer-start-delay-seconds", fmt.Sprintf("%d", *req.OpenClawStartDelaySeconds))
		}
		args = addString(args, "--pi-image", req.PiImage)
		args = addString(args, "--pi-mcp-adapter", req.PiMCPAdapter)
		args = addInt64(args, "--juror-output-limit-bytes", req.JurorOutputLimitBytes)
		args = addString(args, "--docker-mcp-host", req.DockerMCPHost)
		args = addString(args, "--podman-mcp-host", req.PodmanMCPHost)
		return args
	}

	if strings.TrimSpace(scenarioPath) != "" {
		args := []string{
			"scenario",
			"--case-id", caseID,
			"--run-id", runID,
			"--scenario", strings.TrimSpace(scenarioPath),
			"--output", filepath.Join(outDir, "run.json"),
			"--runtime", filepath.Join(outDir, "runtime.json"),
			"--events", filepath.Join(outDir, "events.ndjson"),
			"--db", filepath.Join(outDir, "run.db"),
			"--transcript", filepath.Join(outDir, "transcript.md"),
			"--digest", filepath.Join(outDir, "digest.md"),
			"--caseapi-addr", caseAPIAddr,
		}
		if req.Offline {
			args = append(args, "--offline")
		}
		return addDirectCommon(args)
	}

	args := []string{
		"case",
		"--case-id", caseID,
		"--run-id", runID,
		"--complaint", strings.TrimSpace(complaintPath),
		"--out-dir", outDir,
		"--caseapi-addr", caseAPIAddr,
	}
	args = addComplaintSetup(args)
	return addDirectCommon(args)
}

func chooseLocalCaseAPIAddr() (string, error) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
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
	if err := s.persistRecord(rec); err != nil {
		s.failForPersistenceError(rec, err)
	}
}

func (s *Server) markStartupFailed(rec *CaseRecord, message string) {
	s.mu.Lock()
	if rec.Status != "starting" {
		s.mu.Unlock()
		return
	}
	cmd := rec.cmd
	rec.Status = "failed"
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
	var errs []error
	if err := s.persistRecord(rec); err != nil {
		errs = append(errs, fmt.Errorf("persist service record: %w", err))
	}
	if err := stopProcess(cmd, 2*time.Second); err != nil {
		errs = append(errs, err)
	}
	if len(errs) > 0 {
		s.setRecordError(rec, "failed", fmt.Sprintf("%s; %s", message, errors.Join(errs...).Error()))
		if err := s.persistRecord(rec); err != nil {
			s.setRecordError(rec, "failed", fmt.Sprintf("%s; %s; persist service record: %v", message, errors.Join(errs...).Error(), err))
		}
	}
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
	isAttested := rec.Execution != nil && rec.Execution.Mode == clerkExecutionAttested
	attested := attestedCaseUpdate{}
	s.mu.Lock()
	rec.FinishedAt = time.Now().UTC().Format(time.RFC3339)
	rec.ExitCode = &exitCode
	rec.cmd = nil
	rec.PID = 0
	if logErr != nil {
		rec.Error = fmt.Sprintf("close process logs: %v", logErr)
	} else if isAttested {
		attested = buildAttestedCaseUpdate(rec, exitCode)
		if attested.summary != nil {
			rec.Summary = attested.summary
		}
	} else {
		stdoutRaw, readErr := os.ReadFile(rec.StdoutLog)
		if readErr != nil {
			rec.Error = fmt.Sprintf("read stdout log: %v", readErr)
		} else if summary := parseLastJSON(string(stdoutRaw)); summary != nil {
			rec.Summary = summary
		}
	}
	if isAttested && rec.Execution != nil && attested.attestation != nil {
		rec.Execution.Attestation = attested.attestation
	}
	switch {
	case rec.killing:
		rec.Status = "killed"
	case logErr != nil:
		rec.Status = "failed"
	case isAttested && attested.err != "":
		rec.Status = "failed"
		rec.Error = attested.err
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
	if err := s.persistRecord(rec); err != nil {
		s.setRecordError(rec, "failed", fmt.Sprintf("persist service record: %v", err))
	}
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

func (s *Server) handleKillCase(w http.ResponseWriter, caseID string) {
	s.mu.Lock()
	rec := s.cases[caseID]
	if rec == nil {
		s.mu.Unlock()
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if !isActive(rec) || rec.cmd == nil {
		status := rec.Status
		s.mu.Unlock()
		writeJSON(w, http.StatusConflict, map[string]any{"ok": false, "case_id": caseID, "status": status, "error": apiError("case_not_active", "case has no attached active process")})
		return
	}
	rec.killing = true
	cmd := rec.cmd
	rec.Status = "killing"
	s.mu.Unlock()
	if err := s.persistRecord(rec); err != nil {
		s.setRecordError(rec, "failed", fmt.Sprintf("persist service record: %v", err))
		writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("persist_failed", err.Error())})
		return
	}
	if err := stopProcess(cmd, 2*time.Second); err != nil {
		s.setRecordError(rec, "failed", err.Error())
		if persistErr := s.persistRecord(rec); persistErr != nil {
			s.setRecordError(rec, "failed", fmt.Sprintf("%s; persist service record: %v", err.Error(), persistErr))
		}
		writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("kill_failed", err.Error())})
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": publicRecord(rec)})
}

func (s *Server) proxyRoleAPI(w http.ResponseWriter, r *http.Request) {
	raw, err := readProxyBody(w, r)
	if err != nil {
		return
	}
	caseID, err := caseIDFromRoleAPIRequest(r, raw)
	if err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("missing_case_id", err.Error())})
		return
	}
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if rec.Status == "running" && rec.CaseAPIBase != "" {
		if r.Method == http.MethodPost {
			s.forwardRaw(w, r, rec.CaseAPIBase, raw)
			return
		}
		s.forward(w, r, rec.CaseAPIBase)
		return
	}
	if isActive(rec) {
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case_id": caseID, "status": "waiting", "message": "The case process is starting."})
		return
	}
	if pathBase(r.URL.Path) == "result" {
		s.writeStoredResult(w, rec)
		return
	}
	writeJSON(w, http.StatusGone, map[string]any{"ok": false, "case_id": caseID, "status": rec.Status, "error": apiError("case_not_active", "case has no active role API")})
}

func readProxyBody(w http.ResponseWriter, r *http.Request) ([]byte, error) {
	if r.Method != http.MethodPost {
		return nil, nil
	}
	raw, err := io.ReadAll(http.MaxBytesReader(w, r.Body, defaultMaxProxyBodyBytes))
	if err != nil {
		writeJSON(w, http.StatusRequestEntityTooLarge, map[string]any{"ok": false, "error": apiError("request_too_large", err.Error())})
		return nil, err
	}
	return raw, nil
}

func caseIDFromRoleAPIRequest(r *http.Request, raw []byte) (string, error) {
	if r.Method == http.MethodGet {
		caseID := strings.TrimSpace(r.URL.Query().Get("case_id"))
		if caseID == "" {
			return "", fmt.Errorf("case_id is required")
		}
		return caseID, nil
	}
	var req struct {
		CaseID string `json:"case_id"`
	}
	if err := json.Unmarshal(raw, &req); err != nil {
		return "", fmt.Errorf("bad JSON: %w", err)
	}
	caseID := strings.TrimSpace(req.CaseID)
	if caseID == "" {
		return "", fmt.Errorf("case_id is required")
	}
	return caseID, nil
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
	suffix := strings.TrimPrefix(requestPath, "/roleapi/v1")
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

func (s *Server) writeStoredResult(w http.ResponseWriter, rec *CaseRecord) {
	run, err := readRunJSON(rec)
	if err != nil {
		writeJSON(w, http.StatusOK, map[string]any{"ok": rec.Status != "failed", "case_id": rec.CaseID, "status": rec.Status, "error": rec.Error})
		return
	}
	status := "done"
	if mapString(run["status"]) == "failed" {
		status = "failed"
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": status != "failed", "case_id": rec.CaseID, "status": status, "result": run})
}

func (s *Server) handleCaseResult(w http.ResponseWriter, caseID string) {
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if rec.Status == "running" && rec.CaseAPIBase != "" {
		u := strings.TrimRight(rec.CaseAPIBase, "/") + "/roleapi/v1/result?case_id=" + url.QueryEscape(caseID) + "&role_id=observer"
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
	status := "done"
	if mapString(run["status"]) == "failed" {
		status = "failed"
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": status != "failed", "case_id": caseID, "status": status, "result": run})
}

func readRunJSON(rec *CaseRecord) (map[string]any, error) {
	return readRunJSONFromDir(caseEffectiveOutputDir(publicRecord(rec)))
}

func readRunJSONFromDir(dir string) (map[string]any, error) {
	raw, err := os.ReadFile(filepath.Join(dir, "run.json"))
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
		files, err := listCaseArtifacts(publicRecord(rec))
		if err != nil {
			writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("artifact_list_failed", err.Error())})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case_id": caseID, "artifacts": files})
		return
	}
	if !listedArtifactName(name) && !listedCaseTopArtifactName(name) {
		writeUnknownArtifact(w, caseID, name)
		return
	}
	path, err := caseArtifactPath(publicRecord(rec), name)
	if err != nil {
		writeArtifactAccessError(w, caseID, name, err)
		return
	}
	http.ServeFile(w, r, path)
}

func (s *Server) handleEvidence(w http.ResponseWriter, r *http.Request, caseID string, evidenceID string) {
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	outDir := caseEffectiveOutputDir(publicRecord(rec))
	manifestPath := filepath.Join(outDir, "evidence-manifest.json")
	raw, err := os.ReadFile(manifestPath)
	if err != nil {
		if isActive(rec) && os.IsNotExist(err) {
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
			s.serveCaseFile(w, r, rec, name)
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
	path, err := safeArtifactPath(caseEffectiveOutputDir(publicRecord(rec)), name)
	if err != nil {
		writeArtifactAccessError(w, rec.CaseID, name, err)
		return
	}
	http.ServeFile(w, r, path)
}

func serveListedArtifactFile(w http.ResponseWriter, r *http.Request, caseID string, outDir string, name string) {
	if !listedArtifactName(name) {
		writeUnknownArtifact(w, caseID, name)
		return
	}
	path, err := safeArtifactPath(outDir, name)
	if err != nil {
		writeArtifactAccessError(w, caseID, name, err)
		return
	}
	http.ServeFile(w, r, path)
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
	return []string{"run.json", "state.json", "certificate.json", "digest.md", "transcript.md", "work-notes.ndjson", "events.ndjson", "evidence-manifest.json", "service-logs/adc.stdout", "service-logs/adc.stderr"}
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
	return rec.Status == "starting" || rec.Status == "running" || rec.Status == "killing"
}

func publicRecord(rec *CaseRecord) CaseRecord {
	out := *rec
	out.cmd = nil
	out.killing = false
	return out
}

func (s *Server) markFailed(rec *CaseRecord, message string) error {
	s.mu.Lock()
	rec.Status = "failed"
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
	if err := s.persistRecord(rec); err != nil {
		s.setRecordError(rec, "failed", fmt.Sprintf("%s; persist service record: %v", message, err))
		return fmt.Errorf("persist service record: %w", err)
	}
	return nil
}

func (s *Server) persistRecord(rec *CaseRecord) error {
	public := publicRecord(rec)
	raw, err := json.MarshalIndent(public, "", "  ")
	if err != nil {
		return err
	}
	if err := os.MkdirAll(public.OutputDir, 0o755); err != nil {
		return fmt.Errorf("create case output dir: %w", err)
	}
	tmp := filepath.Join(public.OutputDir, "service-case.json.tmp")
	final := filepath.Join(public.OutputDir, "service-case.json")
	if err := os.WriteFile(tmp, raw, 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, final)
}

func (s *Server) loadCaseRecords() error {
	entries, err := os.ReadDir(s.cfg.OutputRoot)
	if err != nil {
		return err
	}
	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		raw, err := os.ReadFile(filepath.Join(s.cfg.OutputRoot, entry.Name(), "service-case.json"))
		if err != nil {
			if errors.Is(err, os.ErrNotExist) {
				continue
			}
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
		rec.killing = false
		if rec.Error == "" {
			rec.Error = detachedProcessMessage
		}
	}
	return rec, caseRecordChanged(original, rec)
}

func applyRunJSONToRecord(rec *CaseRecord, run map[string]any) {
	rec.PID = 0
	rec.cmd = nil
	rec.killing = false
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

func normalizeCreateMode(mode string) string {
	mode = strings.ToLower(strings.TrimSpace(mode))
	if mode == "" {
		return "run"
	}
	return mode
}

func firstPositive(values ...int) int {
	for _, value := range values {
		if value > 0 {
			return value
		}
	}
	return 0
}

func validateJuryConfigRequest(req CaseCreateRequest) error {
	if req.JurorCount < 0 {
		return fmt.Errorf("juror_count must be non-negative")
	}
	if req.JurorCount > 0 && (req.JurorCount < 6 || req.JurorCount > 12) {
		return fmt.Errorf("juror_count must be between 6 and 12")
	}
	if req.MinimumConcurring < 0 {
		return fmt.Errorf("minimum_concurring must be non-negative")
	}
	if req.MinimumConcurring > 0 && (req.MinimumConcurring < 6 || req.MinimumConcurring > 12) {
		return fmt.Errorf("minimum_concurring must be between 6 and 12")
	}
	if req.JurorCount > 0 && req.MinimumConcurring > req.JurorCount {
		return fmt.Errorf("minimum_concurring cannot exceed juror_count")
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

func (s *Server) setRecordError(rec *CaseRecord, status string, message string) {
	s.mu.Lock()
	rec.Status = status
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
}

func (s *Server) failForPersistenceError(rec *CaseRecord, err error) {
	message := fmt.Sprintf("persist service record: %v", err)
	s.mu.Lock()
	cmd := rec.cmd
	rec.Status = "failed"
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
	if stopErr := stopProcess(cmd, 2*time.Second); stopErr != nil {
		s.setRecordError(rec, "failed", fmt.Sprintf("%s; %v", message, stopErr))
	}
}

func stopProcess(cmd *exec.Cmd, grace time.Duration) error {
	if cmd == nil || cmd.Process == nil || cmd.ProcessState != nil {
		return nil
	}
	if err := cmd.Process.Signal(os.Interrupt); err != nil && !errors.Is(err, os.ErrProcessDone) {
		return fmt.Errorf("interrupt child: %w", err)
	}
	if grace > 0 {
		time.Sleep(grace)
	}
	if cmd.ProcessState == nil {
		if err := cmd.Process.Kill(); err != nil && !errors.Is(err, os.ErrProcessDone) {
			return fmt.Errorf("kill child: %w", err)
		}
	}
	return nil
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
