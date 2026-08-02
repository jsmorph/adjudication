package service

import (
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"time"
)

const (
	clerkRecordName = "clerk.json"
	clerkKillGrace  = 10 * time.Second
)

var (
	errInvalidClerkExample = errors.New("invalid clerk example")
	errUnknownClerkExample = errors.New("unknown clerk example")
)

type ClerkCreateRequest struct {
	Example                    string                 `json:"example,omitempty"`
	CaseID                     string                 `json:"case_id,omitempty"`
	RunID                      string                 `json:"run_id,omitempty"`
	ComplaintPath              string                 `json:"complaint_path,omitempty"`
	CaseFiles                  []string               `json:"case_files,omitempty"`
	OutputDir                  string                 `json:"out_dir,omitempty"`
	PolicyPath                 string                 `json:"policy_path,omitempty"`
	CouncilSize                int                    `json:"council_size,omitempty"`
	JudgmentStandard           string                 `json:"judgment_standard,omitempty"`
	AttorneyInstructionsPath   string                 `json:"attorney_instructions,omitempty"`
	PromptDir                  string                 `json:"prompt_dir,omitempty"`
	AttorneyCommonPromptPath   string                 `json:"attorney_common_prompt,omitempty"`
	AttorneyArgumentPromptPath string                 `json:"attorney_arguments_prompt,omitempty"`
	AttorneyRebuttalPromptPath string                 `json:"attorney_rebuttals_prompt,omitempty"`
	CommonRoot                 string                 `json:"common_root,omitempty"`
	CouncilPoolPath            string                 `json:"council_pool_path,omitempty"`
	CaseAPIAddr                string                 `json:"caseapi_addr,omitempty"`
	MCPListenAddr              string                 `json:"mcp_listen,omitempty"`
	MCPBearerToken             string                 `json:"mcp_bearer_token,omitempty"`
	CouncilTimeoutSeconds      int                    `json:"council_timeout_seconds,omitempty"`
	LawyerTimeoutSeconds       int                    `json:"lawyer_timeout_seconds,omitempty"`
	MaxResponseBytes           int                    `json:"max_response_bytes,omitempty"`
	InvalidAttemptLimit        int                    `json:"invalid_attempt_limit,omitempty"`
	EnginePath                 string                 `json:"engine_path,omitempty"`
	LawyerInstructionsPath     string                 `json:"lawyer_instructions,omitempty"`
	RemoteLawyerSkillPath      string                 `json:"remote_lawyer_skill,omitempty"`
	CouncilInstructionsPath    string                 `json:"council_instructions,omitempty"`
	AutoLawyers                string                 `json:"auto_lawyers,omitempty"`
	MCPPublicBaseURL           string                 `json:"mcp_public_base_url,omitempty"`
	DockerCommand              string                 `json:"docker_command,omitempty"`
	PodmanCommand              string                 `json:"podman_command,omitempty"`
	OpenClawImage              string                 `json:"openclaw_image,omitempty"`
	OpenClawModel              string                 `json:"openclaw_model,omitempty"`
	OpenClawThinking           string                 `json:"openclaw_thinking,omitempty"`
	OpenClawTimeoutSeconds     int                    `json:"openclaw_timeout_seconds,omitempty"`
	OpenClawAuth               string                 `json:"openclaw_auth,omitempty"`
	OpenClawCodexAuthPath      string                 `json:"openclaw_codex_auth_path,omitempty"`
	OpenClawStartDelaySeconds  *int                   `json:"openclaw_lawyer_start_delay_seconds,omitempty"`
	PiImage                    string                 `json:"pi_image,omitempty"`
	PiMCPAdapter               string                 `json:"pi_mcp_adapter,omitempty"`
	CouncilOutputLimitBytes    int64                  `json:"council_output_limit_bytes,omitempty"`
	DockerMCPHost              string                 `json:"docker_mcp_host,omitempty"`
	PodmanMCPHost              string                 `json:"podman_mcp_host,omitempty"`
	Execution                  *ClerkExecutionRequest `json:"execution,omitempty"`
}

type ClerkRecord struct {
	CaseID     string                `json:"case_id"`
	RunID      string                `json:"run_id"`
	Example    string                `json:"example,omitempty"`
	PID        int                   `json:"pid,omitempty"`
	Status     string                `json:"status"`
	OutDir     string                `json:"out_dir"`
	StdoutLog  string                `json:"stdout_log"`
	StderrLog  string                `json:"stderr_log"`
	CreatedAt  string                `json:"created_at"`
	StartedAt  string                `json:"started_at,omitempty"`
	FinishedAt string                `json:"finished_at,omitempty"`
	ExitCode   *int                  `json:"exit_code,omitempty"`
	Summary    map[string]any        `json:"summary,omitempty"`
	Error      string                `json:"error,omitempty"`
	Execution  *ClerkExecutionRecord `json:"execution,omitempty"`

	killing bool
	cmd     *exec.Cmd
	done    chan struct{}
}

func (s *Server) handleClerkCases(w http.ResponseWriter, r *http.Request) {
	switch r.Method {
	case http.MethodPost:
		s.handleCreateClerkCase(w, r)
	case http.MethodGet:
		s.handleListClerkCases(w, r)
	default:
		writeJSON(w, http.StatusMethodNotAllowed, map[string]any{"ok": false, "error": apiError("method_not_allowed", "use GET or POST")})
	}
}

func (s *Server) handleClerkCase(w http.ResponseWriter, r *http.Request) {
	rest := strings.TrimPrefix(r.URL.Path, "/clerk/v1/cases/")
	parts := strings.Split(strings.Trim(rest, "/"), "/")
	if len(parts) == 0 || parts[0] == "" {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "error": apiError("not_found", "case id is required")})
		return
	}
	caseID := parts[0]
	if len(parts) == 1 && r.Method == http.MethodGet {
		s.handleGetClerkCase(w, caseID)
		return
	}
	if len(parts) == 2 && parts[1] == "kill" && r.Method == http.MethodPost {
		s.handleKillClerkCase(w, caseID)
		return
	}
	if len(parts) == 2 && parts[1] == "result" && r.Method == http.MethodGet {
		s.handleClerkCaseResult(w, caseID)
		return
	}
	if len(parts) == 3 && parts[1] == "attestation" && parts[2] == "events" && r.Method == http.MethodGet {
		s.handleClerkAttestationEvents(w, r, caseID)
		return
	}
	if len(parts) >= 2 && parts[1] == "artifacts" && r.Method == http.MethodGet {
		name := strings.Join(parts[2:], "/")
		s.handleClerkArtifact(w, r, caseID, name)
		return
	}
	if len(parts) == 3 && parts[1] == "evidence" && r.Method == http.MethodGet {
		s.handleClerkEvidence(w, r, caseID, parts[2])
		return
	}
	writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("not_found", "unknown clerk route")})
}

func (s *Server) handleCreateClerkCase(w http.ResponseWriter, r *http.Request) {
	var req ClerkCreateRequest
	dec := json.NewDecoder(http.MaxBytesReader(w, r.Body, 1<<20))
	if err := dec.Decode(&req); err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError("bad_json", err.Error())})
		return
	}
	rec, err := s.startClerkCase(req)
	if err != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"ok": false, "error": apiError(clerkCreateErrorCode(err), err.Error())})
		return
	}
	writeJSON(w, http.StatusAccepted, map[string]any{"ok": true, "case": rec})
}

func (s *Server) handleListClerkCases(w http.ResponseWriter, r *http.Request) {
	records, err := s.listClerkRecords()
	if err != nil {
		writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "error": apiError("list_cases_failed", err.Error())})
		return
	}
	if status := strings.TrimSpace(r.URL.Query().Get("status")); status != "" {
		filtered := records[:0]
		for _, rec := range records {
			if rec.Status == status {
				filtered = append(filtered, rec)
			}
		}
		records = filtered
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "cases": records})
}

func (s *Server) startClerkCase(req ClerkCreateRequest) (ClerkRecord, error) {
	caseID := strings.TrimSpace(req.CaseID)
	if caseID == "" {
		caseID = "arbd-" + time.Now().UTC().Format("20060102150405") + "-" + randomHex(4)
	}
	if err := validateID(caseID, "case_id"); err != nil {
		return ClerkRecord{}, err
	}
	runID := strings.TrimSpace(req.RunID)
	if runID == "" {
		runID = "run-" + caseID
	}
	example := strings.TrimSpace(req.Example)
	if err := validateClerkExample(example); err != nil {
		return ClerkRecord{}, err
	}
	if err := validateClerkExampleExists(example); err != nil {
		return ClerkRecord{}, err
	}
	complaintPath := strings.TrimSpace(req.ComplaintPath)
	if example == "" && complaintPath == "" {
		return ClerkRecord{}, fmt.Errorf("complaint_path is required unless example is set")
	}
	if complaintPath != "" {
		if _, err := os.Stat(complaintPath); err != nil {
			return ClerkRecord{}, fmt.Errorf("complaint_path: %w", err)
		}
	}
	if err := validateClerkNumbers(req); err != nil {
		return ClerkRecord{}, err
	}
	execution, err := s.resolveClerkExecution(req)
	if err != nil {
		return ClerkRecord{}, err
	}
	outDir, err := resolveClerkOutDir(s.cfg.OutputRoot, caseID, req.OutputDir)
	if err != nil {
		return ClerkRecord{}, err
	}
	if err := s.reserveClerkCase(caseID, outDir); err != nil {
		return ClerkRecord{}, err
	}
	if err := os.MkdirAll(outDir, 0o755); err != nil {
		s.unreserveClerkCase(caseID)
		return ClerkRecord{}, fmt.Errorf("create clerk output dir: %w", err)
	}
	if err := rejectNonemptyClerkDir(outDir); err != nil {
		s.unreserveClerkCase(caseID)
		return ClerkRecord{}, err
	}
	commandPath := s.cfg.AardBin
	args := s.clerkRunArgs(req, caseID, runID, outDir, example)
	rec := &ClerkRecord{
		CaseID:    caseID,
		RunID:     runID,
		Example:   example,
		Status:    "starting",
		OutDir:    outDir,
		CreatedAt: time.Now().UTC().Format(time.RFC3339),
		Execution: execution,
		done:      make(chan struct{}),
	}
	if execution != nil && execution.Mode == clerkExecutionAttested {
		var err error
		commandPath, args, err = attestedClerkCommand(req, rec, outDir)
		if err != nil {
			s.unreserveClerkCase(caseID)
			return ClerkRecord{}, err
		}
	}
	stdoutPath := filepath.Join(outDir, "clerk.stdout")
	stderrPath := filepath.Join(outDir, "clerk.stderr")
	stdoutFile, err := os.Create(stdoutPath)
	if err != nil {
		s.unreserveClerkCase(caseID)
		return ClerkRecord{}, fmt.Errorf("create clerk stdout log: %w", err)
	}
	stderrFile, err := os.Create(stderrPath)
	if err != nil {
		s.unreserveClerkCase(caseID)
		_ = stdoutFile.Close()
		return ClerkRecord{}, fmt.Errorf("create clerk stderr log: %w", err)
	}
	closeLogs := func() error {
		return errors.Join(stdoutFile.Close(), stderrFile.Close())
	}
	cmd := exec.Command(commandPath, args...)
	cmd.Stdout = stdoutFile
	cmd.Stderr = stderrFile
	rec.StdoutLog = stdoutPath
	rec.StderrLog = stderrPath
	rec.cmd = cmd
	s.mu.Lock()
	s.clerkCases[caseID] = rec
	s.mu.Unlock()
	if err := s.persistClerkRecord(rec); err != nil {
		s.unreserveClerkCase(caseID)
		return ClerkRecord{}, errors.Join(err, closeLogs())
	}
	if err := cmd.Start(); err != nil {
		s.markClerkFailed(rec, fmt.Sprintf("start child: %v", err))
		close(rec.done)
		return ClerkRecord{}, errors.Join(fmt.Errorf("start child: %w", err), closeLogs())
	}
	s.mu.Lock()
	rec.PID = cmd.Process.Pid
	rec.StartedAt = time.Now().UTC().Format(time.RFC3339)
	rec.Status = "running"
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistClerkRecordBestEffort(rec)
	go s.waitClerkChild(rec, stdoutFile, stderrFile)
	s.mu.Lock()
	out := publicClerkRecord(rec)
	s.mu.Unlock()
	return out, nil
}

func (s *Server) clerkRunArgs(req ClerkCreateRequest, caseID string, runID string, outDir string, example string) []string {
	args := []string{"run", "--case-id", caseID, "--run-id", runID, "--out-dir", outDir}
	addString := func(name string, value string) {
		if strings.TrimSpace(value) != "" {
			args = append(args, name, strings.TrimSpace(value))
		}
	}
	addInt := func(name string, value int) {
		if value > 0 {
			args = append(args, name, fmt.Sprintf("%d", value))
		}
	}
	addInt64 := func(name string, value int64) {
		if value > 0 {
			args = append(args, name, fmt.Sprintf("%d", value))
		}
	}
	addString("--complaint", req.ComplaintPath)
	for _, file := range req.CaseFiles {
		addString("--file", file)
	}
	addString("--policy", req.PolicyPath)
	addInt("--council-size", req.CouncilSize)
	addString("--judgment-standard", req.JudgmentStandard)
	addString("--attorney-instructions", req.AttorneyInstructionsPath)
	addString("--prompt-dir", req.PromptDir)
	addString("--attorney-common-prompt", req.AttorneyCommonPromptPath)
	addString("--attorney-arguments-prompt", req.AttorneyArgumentPromptPath)
	addString("--attorney-rebuttals-prompt", req.AttorneyRebuttalPromptPath)
	addString("--common-root", firstNonEmpty(req.CommonRoot, s.cfg.CommonRoot))
	addString("--council-pool", req.CouncilPoolPath)
	addString("--caseapi-addr", req.CaseAPIAddr)
	addString("--mcp-listen", req.MCPListenAddr)
	addString("--mcp-bearer-token", req.MCPBearerToken)
	addInt("--council-timeout-seconds", req.CouncilTimeoutSeconds)
	addInt("--lawyer-timeout-seconds", req.LawyerTimeoutSeconds)
	addInt("--max-response-bytes", req.MaxResponseBytes)
	addInt("--invalid-attempt-limit", req.InvalidAttemptLimit)
	addString("--engine", firstNonEmpty(req.EnginePath, s.cfg.EnginePath))
	addString("--lawyer-instructions", req.LawyerInstructionsPath)
	addString("--remote-lawyer-skill", req.RemoteLawyerSkillPath)
	addString("--council-instructions", req.CouncilInstructionsPath)
	addString("--auto-lawyers", req.AutoLawyers)
	addString("--mcp-public-base-url", req.MCPPublicBaseURL)
	addString("--docker", req.DockerCommand)
	addString("--podman", req.PodmanCommand)
	addString("--openclaw-image", req.OpenClawImage)
	addString("--openclaw-model", req.OpenClawModel)
	addString("--openclaw-thinking", req.OpenClawThinking)
	addInt("--openclaw-timeout-seconds", req.OpenClawTimeoutSeconds)
	addString("--openclaw-auth", req.OpenClawAuth)
	addString("--openclaw-codex-auth", req.OpenClawCodexAuthPath)
	if req.OpenClawStartDelaySeconds != nil {
		args = append(args, "--openclaw-lawyer-start-delay-seconds", fmt.Sprintf("%d", *req.OpenClawStartDelaySeconds))
	}
	addString("--pi-image", req.PiImage)
	addString("--pi-mcp-adapter", req.PiMCPAdapter)
	addInt64("--council-output-limit-bytes", req.CouncilOutputLimitBytes)
	addString("--docker-mcp-host", req.DockerMCPHost)
	addString("--podman-mcp-host", req.PodmanMCPHost)
	if example != "" {
		args = append(args, example)
	}
	return args
}

func (s *Server) reserveClerkCase(caseID string, outDir string) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.clerkCases == nil {
		s.clerkCases = map[string]*ClerkRecord{}
	}
	if _, exists := s.clerkCases[caseID]; exists {
		return fmt.Errorf("case_id already exists")
	}
	if _, exists := s.cases[caseID]; exists {
		return fmt.Errorf("case_id already exists")
	}
	if _, err := os.Stat(filepath.Join(outDir, clerkRecordName)); err == nil {
		return fmt.Errorf("case_id already exists")
	} else if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	s.clerkCases[caseID] = nil
	return nil
}

func (s *Server) unreserveClerkCase(caseID string) {
	s.mu.Lock()
	delete(s.clerkCases, caseID)
	s.mu.Unlock()
}

func (s *Server) waitClerkChild(rec *ClerkRecord, stdoutFile *os.File, stderrFile *os.File) {
	defer close(rec.done)
	waitErr := rec.cmd.Wait()
	exitCode := 0
	if waitErr != nil {
		exitCode = 1
		var exitErr *exec.ExitError
		if errors.As(waitErr, &exitErr) {
			exitCode = exitErr.ExitCode()
		}
	}
	logErr := errors.Join(stdoutFile.Close(), stderrFile.Close())
	var summary map[string]any
	var readErr error
	isAttested := rec.Execution != nil && rec.Execution.Mode == clerkExecutionAttested
	attested := attestedClerkUpdate{}
	if isAttested {
		attested = buildAttestedClerkUpdate(rec, exitCode)
		summary = attested.summary
	} else if logErr == nil {
		var stdoutRaw []byte
		stdoutRaw, readErr = os.ReadFile(rec.StdoutLog)
		if readErr == nil {
			summary = parseLastJSON(string(stdoutRaw))
		}
	}
	s.mu.Lock()
	rec.FinishedAt = time.Now().UTC().Format(time.RFC3339)
	rec.ExitCode = &exitCode
	rec.PID = 0
	rec.cmd = nil
	rec.Summary = summary
	if isAttested && rec.Execution != nil && attested.attestation != nil {
		rec.Execution.Attestation = attested.attestation
	}
	switch {
	case rec.killing:
		rec.Status = "killed"
	case logErr != nil:
		rec.Status = "failed"
		rec.Error = fmt.Sprintf("close process logs: %v", logErr)
	case !isAttested && readErr != nil:
		rec.Status = "failed"
		rec.Error = fmt.Sprintf("read stdout log: %v", readErr)
	case isAttested && attested.err != "":
		rec.Status = "failed"
		rec.Error = attested.err
	case exitCode == 0 && mapString(summary["status"]) == "failed":
		rec.Status = "failed"
		rec.Error = mapString(summary["error"])
	case exitCode == 0:
		rec.Status = "completed"
	default:
		rec.Status = "failed"
		rec.Error = fmt.Sprintf("child exited with code %d", exitCode)
	}
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistClerkRecordBestEffort(rec)
}

func (s *Server) handleKillClerkCase(w http.ResponseWriter, caseID string) {
	rec, ok := s.getClerkRecordPtr(caseID)
	if !ok {
		disk, err := s.readClerkRecordByCaseID(caseID)
		if err != nil {
			writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
			return
		}
		if isActiveClerk(&disk) {
			writeJSON(w, http.StatusConflict, map[string]any{
				"ok":      false,
				"case_id": caseID,
				"case":    disk,
				"error":   apiError("case_not_attached", "case record is active, but this service has no process handle for it"),
			})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": disk})
		return
	}
	s.mu.Lock()
	if !isActiveClerk(rec) {
		out := publicClerkRecord(rec)
		s.mu.Unlock()
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": out})
		return
	}
	rec.killing = true
	rec.Status = "killing"
	cmd := rec.cmd
	done := rec.done
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistClerkRecordBestEffort(rec)
	if cmd != nil && cmd.Process != nil {
		if err := cmd.Process.Signal(os.Interrupt); err != nil && !clerkDone(done) {
			writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("kill_failed", err.Error())})
			return
		}
		select {
		case <-done:
		case <-time.After(clerkKillGrace):
			if !clerkDone(done) {
				if err := cmd.Process.Kill(); err != nil && !clerkDone(done) {
					writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("kill_failed", err.Error())})
					return
				}
			}
			select {
			case <-done:
			case <-time.After(clerkKillGrace):
			}
		}
	}
	s.mu.Lock()
	out := publicClerkRecord(rec)
	s.mu.Unlock()
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": out})
}

func (s *Server) handleGetClerkCase(w http.ResponseWriter, caseID string) {
	rec, ok := s.getClerkRecord(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case": rec})
}

func (s *Server) handleClerkCaseResult(w http.ResponseWriter, caseID string) {
	rec, ok := s.getClerkRecord(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	run, err := readRunJSONFromDir(clerkEffectiveOutputDir(rec))
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

func (s *Server) handleClerkArtifact(w http.ResponseWriter, r *http.Request, caseID string, name string) {
	rec, ok := s.getClerkRecord(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if name == "" {
		files, err := listClerkArtifacts(rec)
		if err != nil {
			writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("artifact_list_failed", err.Error())})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "case_id": caseID, "artifacts": files})
		return
	}
	if !listedArtifactName(name) && !listedClerkTopArtifactName(name) {
		writeUnknownArtifact(w, caseID, name)
		return
	}
	path, err := clerkArtifactPath(rec, name)
	if err != nil {
		writeArtifactAccessError(w, caseID, name, err)
		return
	}
	http.ServeFile(w, r, path)
}

func (s *Server) handleClerkEvidence(w http.ResponseWriter, r *http.Request, caseID string, evidenceID string) {
	rec, ok := s.getClerkRecord(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	serveEvidenceFile(w, r, caseID, clerkEffectiveOutputDir(rec), evidenceID, isActiveClerk(&rec))
}

func (s *Server) getClerkRecordPtr(caseID string) (*ClerkRecord, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	rec := s.clerkCases[caseID]
	return rec, rec != nil
}

func (s *Server) getClerkRecord(caseID string) (ClerkRecord, bool) {
	if rec, ok := s.getClerkRecordPtr(caseID); ok {
		return publicClerkRecord(rec), true
	}
	disk, err := s.readClerkRecordByCaseID(caseID)
	if err != nil {
		return ClerkRecord{}, false
	}
	return disk, true
}

func (s *Server) markClerkFailed(rec *ClerkRecord, message string) {
	s.mu.Lock()
	rec.Status = "failed"
	rec.Error = message
	s.cond.Broadcast()
	s.mu.Unlock()
	s.persistClerkRecordBestEffort(rec)
}

func (s *Server) listClerkRecords() ([]ClerkRecord, error) {
	entries, err := os.ReadDir(s.cfg.OutputRoot)
	if err != nil {
		return nil, err
	}
	records := []ClerkRecord{}
	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		rec, err := readClerkRecord(filepath.Join(s.cfg.OutputRoot, entry.Name(), clerkRecordName))
		if errors.Is(err, os.ErrNotExist) {
			continue
		}
		if err != nil {
			return nil, err
		}
		if attached, ok := s.getClerkRecordPtr(rec.CaseID); ok {
			records = append(records, publicClerkRecord(attached))
			continue
		}
		rec, err = s.reconcileDetachedClerkRecord(rec)
		if err != nil {
			return nil, err
		}
		records = append(records, rec)
	}
	sort.Slice(records, func(i, j int) bool {
		return records[i].CreatedAt < records[j].CreatedAt
	})
	return records, nil
}

func (s *Server) reconcileDetachedClerkRecord(rec ClerkRecord) (ClerkRecord, error) {
	updated, changed := reconcileDetachedClerkRecord(rec)
	if !changed {
		return updated, nil
	}
	if err := s.persistClerkRecord(&updated); err != nil {
		return ClerkRecord{}, fmt.Errorf("persist clerk record %s: %w", updated.CaseID, err)
	}
	return updated, nil
}

func reconcileDetachedClerkRecord(rec ClerkRecord) (ClerkRecord, bool) {
	if !isActiveClerk(&rec) && rec.Error != detachedProcessMessage {
		return rec, false
	}
	original := rec
	if run, err := readRunJSONFromDir(clerkEffectiveOutputDir(rec)); err == nil {
		applyRunJSONToClerkRecord(&rec, run)
	} else if isActiveClerk(&rec) {
		rec.Status = "failed"
		rec.PID = 0
		rec.cmd = nil
		rec.killing = false
		rec.done = nil
		if rec.Error == "" {
			rec.Error = detachedProcessMessage
		}
	}
	return rec, clerkRecordChanged(original, rec)
}

func applyRunJSONToClerkRecord(rec *ClerkRecord, run map[string]any) {
	rec.PID = 0
	rec.cmd = nil
	rec.killing = false
	rec.done = nil
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

func clerkRecordChanged(a ClerkRecord, b ClerkRecord) bool {
	return a.Status != b.Status ||
		a.PID != b.PID ||
		a.FinishedAt != b.FinishedAt ||
		a.Error != b.Error ||
		!reflect.DeepEqual(a.Summary, b.Summary)
}

func (s *Server) readClerkRecordByCaseID(caseID string) (ClerkRecord, error) {
	records, err := s.listClerkRecords()
	if err != nil {
		return ClerkRecord{}, err
	}
	for _, rec := range records {
		if rec.CaseID == caseID {
			return rec, nil
		}
	}
	return ClerkRecord{}, os.ErrNotExist
}

func (s *Server) persistClerkRecord(rec *ClerkRecord) error {
	public := publicClerkRecord(rec)
	raw, err := json.MarshalIndent(public, "", "  ")
	if err != nil {
		return err
	}
	tmp := filepath.Join(public.OutDir, clerkRecordName+".tmp")
	final := filepath.Join(public.OutDir, clerkRecordName)
	if err := os.WriteFile(tmp, raw, 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, final)
}

func (s *Server) persistClerkRecordBestEffort(rec *ClerkRecord) {
	_ = s.persistClerkRecord(rec)
}

func publicClerkRecord(rec *ClerkRecord) ClerkRecord {
	out := *rec
	out.killing = false
	out.cmd = nil
	out.done = nil
	return out
}

func readClerkRecord(path string) (ClerkRecord, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return ClerkRecord{}, err
	}
	var rec ClerkRecord
	if err := json.Unmarshal(raw, &rec); err != nil {
		return ClerkRecord{}, err
	}
	return rec, nil
}

func clerkDone(done <-chan struct{}) bool {
	if done == nil {
		return true
	}
	select {
	case <-done:
		return true
	default:
		return false
	}
}

func isActiveClerk(rec *ClerkRecord) bool {
	return rec.Status == "starting" || rec.Status == "running" || rec.Status == "killing"
}

func resolveClerkOutDir(outputRoot string, caseID string, requested string) (string, error) {
	rootAbs, err := filepath.Abs(strings.TrimSpace(outputRoot))
	if err != nil {
		return "", err
	}
	out := strings.TrimSpace(requested)
	if out == "" {
		out = filepath.Join(rootAbs, caseID)
	} else if !filepath.IsAbs(out) {
		out = filepath.Join(rootAbs, out)
	}
	outAbs, err := filepath.Abs(out)
	if err != nil {
		return "", err
	}
	if filepath.Dir(outAbs) != rootAbs {
		return "", fmt.Errorf("out_dir must be an immediate child of the service output root")
	}
	return outAbs, nil
}

func rejectNonemptyClerkDir(outDir string) error {
	entries, err := os.ReadDir(outDir)
	if err != nil {
		return err
	}
	if len(entries) != 0 {
		return fmt.Errorf("out_dir already contains files")
	}
	return nil
}

func validateClerkExample(example string) error {
	if example == "" {
		return nil
	}
	if strings.Contains(example, "/") || strings.HasPrefix(example, ".") || strings.Contains(example, "..") {
		return fmt.Errorf("%w: %s", errInvalidClerkExample, example)
	}
	return nil
}

func validateClerkExampleExists(example string) error {
	if example == "" {
		return nil
	}
	path := filepath.Join("examples", example, "complaint.md")
	st, err := os.Stat(path)
	if err != nil {
		if errors.Is(err, os.ErrNotExist) {
			return fmt.Errorf("%w: %s is missing", errUnknownClerkExample, path)
		}
		return fmt.Errorf("check example %s: %w", example, err)
	}
	if st.IsDir() {
		return fmt.Errorf("%w: %s is a directory", errUnknownClerkExample, path)
	}
	return nil
}

func clerkCreateErrorCode(err error) string {
	if errors.Is(err, errInvalidClerkExample) {
		return "invalid_example"
	}
	if errors.Is(err, errUnknownClerkExample) {
		return "unknown_example"
	}
	return "start_case_failed"
}

func validateClerkNumbers(req ClerkCreateRequest) error {
	ints := map[string]int{
		"council_size":             req.CouncilSize,
		"council_timeout_seconds":  req.CouncilTimeoutSeconds,
		"lawyer_timeout_seconds":   req.LawyerTimeoutSeconds,
		"max_response_bytes":       req.MaxResponseBytes,
		"invalid_attempt_limit":    req.InvalidAttemptLimit,
		"openclaw_timeout_seconds": req.OpenClawTimeoutSeconds,
	}
	for name, value := range ints {
		if value < 0 {
			return fmt.Errorf("%s must be non-negative", name)
		}
	}
	if req.OpenClawStartDelaySeconds != nil && *req.OpenClawStartDelaySeconds < 0 {
		return fmt.Errorf("openclaw_lawyer_start_delay_seconds must be non-negative")
	}
	if req.CouncilOutputLimitBytes < 0 {
		return fmt.Errorf("council_output_limit_bytes must be non-negative")
	}
	return nil
}
