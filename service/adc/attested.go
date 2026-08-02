package service

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

const (
	clerkExecutionLocal    = "local"
	clerkExecutionAttested = "attested"

	defaultAttestedDevHost       = "dev"
	defaultAttestedAWSRegion     = "us-east-2"
	attestedEventsFetchTimeout   = 20 * time.Second
	attestedEventsArtifactName   = "events.ndjson"
	attestedEventsContentType    = "application/x-ndjson"
	attestedEventsMissingMessage = "attestation events are not available yet"

	attestationStatusPending  = "pending"
	attestationStatusVerified = "verified"
	attestationStatusFailed   = "failed"
	attestationStatusPartial  = "partial"
)

type ClerkExecutionRequest struct {
	Mode        string                   `json:"mode,omitempty"`
	Attestation *ClerkAttestationRequest `json:"attestation,omitempty"`
}

type ClerkAttestationRequest struct {
	Verify              *bool  `json:"verify,omitempty"`
	DriverPath          string `json:"driver_path,omitempty"`
	UV                  string `json:"uv,omitempty"`
	ParserPath          string `json:"parser,omitempty"`
	InputPrefix         string `json:"input_prefix,omitempty"`
	OutputPrefix        string `json:"output_prefix,omitempty"`
	OutputRoot          string `json:"output_root,omitempty"`
	ExecAMI             string `json:"exec_ami,omitempty"`
	DevHost             string `json:"dev_host,omitempty"`
	RemoteAttestDir     string `json:"remote_attest_dir,omitempty"`
	AWSRegion           string `json:"aws_region,omitempty"`
	InstanceType        string `json:"instance_type,omitempty"`
	IAMInstanceProfile  string `json:"iam_instance_profile,omitempty"`
	ImageTarS3          string `json:"image_tar_s3,omitempty"`
	RootVolumeSizeGB    int    `json:"root_volume_size_gb,omitempty"`
	ExecPollAttempts    int    `json:"exec_poll_attempts,omitempty"`
	PollIntervalSeconds int    `json:"poll_interval_seconds,omitempty"`
	TimeoutSeconds      int    `json:"timeout_seconds,omitempty"`
	ExpectedPCR4        string `json:"expected_pcr4,omitempty"`
	ExpectedPCR7        string `json:"expected_pcr7,omitempty"`
	ExpectedPCR12       string `json:"expected_pcr12,omitempty"`
}

type AttestedClerkConfig struct {
	Verify              bool   `json:"verify,omitempty"`
	DriverPath          string `json:"driver_path,omitempty"`
	UV                  string `json:"uv,omitempty"`
	ParserPath          string `json:"parser,omitempty"`
	InputPrefix         string `json:"input_prefix,omitempty"`
	OutputPrefix        string `json:"output_prefix,omitempty"`
	OutputRoot          string `json:"output_root,omitempty"`
	ExecAMI             string `json:"exec_ami,omitempty"`
	DevHost             string `json:"dev_host,omitempty"`
	RemoteAttestDir     string `json:"remote_attest_dir,omitempty"`
	AWSRegion           string `json:"aws_region,omitempty"`
	InstanceType        string `json:"instance_type,omitempty"`
	IAMInstanceProfile  string `json:"iam_instance_profile,omitempty"`
	ImageTarS3          string `json:"image_tar_s3,omitempty"`
	RootVolumeSizeGB    int    `json:"root_volume_size_gb,omitempty"`
	ExecPollAttempts    int    `json:"exec_poll_attempts,omitempty"`
	PollIntervalSeconds int    `json:"poll_interval_seconds,omitempty"`
	TimeoutSeconds      int    `json:"timeout_seconds,omitempty"`
	ExpectedPCR4        string `json:"expected_pcr4,omitempty"`
	ExpectedPCR7        string `json:"expected_pcr7,omitempty"`
	ExpectedPCR12       string `json:"expected_pcr12,omitempty"`
}

type ClerkExecutionRecord struct {
	Mode        string                  `json:"mode"`
	Requested   *ClerkExecutionRequest  `json:"requested,omitempty"`
	Resolved    *AttestedClerkConfig    `json:"resolved,omitempty"`
	Attestation *ClerkAttestationRecord `json:"attestation,omitempty"`
}

type ClerkAttestationRecord struct {
	Status          string `json:"status,omitempty"`
	InputPrefix     string `json:"input_prefix,omitempty"`
	OutputPrefix    string `json:"output_prefix,omitempty"`
	ExecAMI         string `json:"exec_ami,omitempty"`
	LocalOutputDir  string `json:"local_output_dir,omitempty"`
	LocalArchive    string `json:"local_archive,omitempty"`
	ManifestPath    string `json:"manifest_path,omitempty"`
	ManifestSHA384  string `json:"manifest_sha384,omitempty"`
	AttestationText string `json:"attestation_text,omitempty"`
	VerificationLog string `json:"verification_log,omitempty"`
	ProgressLog     string `json:"progress_log,omitempty"`
	LauncherLog     string `json:"launcher_log,omitempty"`
	RunEnv          string `json:"run_env,omitempty"`
}

type attestedCaseUpdate struct {
	attestation *ClerkAttestationRecord
	summary     map[string]any
	err         string
}

func (s *Server) resolveCaseExecution(req CaseCreateRequest, mode string, runID string) (*ClerkExecutionRecord, error) {
	if req.Execution == nil {
		return nil, nil
	}
	executionMode := strings.TrimSpace(req.Execution.Mode)
	if executionMode == "" {
		return nil, fmt.Errorf("execution mode is required when execution is set")
	}
	switch executionMode {
	case clerkExecutionLocal:
		if req.Execution.Attestation != nil {
			return nil, fmt.Errorf("local execution does not accept attestation config")
		}
		return nil, nil
	case clerkExecutionAttested:
		if normalizeCreateMode(mode) != "run" {
			return nil, fmt.Errorf("attested execution supports mode=run only")
		}
		return s.resolveAttestedCaseExecution(req, runID)
	default:
		return nil, fmt.Errorf("unsupported execution mode %q", executionMode)
	}
}

func (s *Server) resolveAttestedCaseExecution(req CaseCreateRequest, runID string) (*ClerkExecutionRecord, error) {
	if err := validateAttestedCaseRequest(req); err != nil {
		return nil, err
	}
	if req.Execution.Attestation == nil {
		return nil, fmt.Errorf("attested execution requires attestation config")
	}
	if req.Execution.Attestation.Verify != nil && !*req.Execution.Attestation.Verify {
		return nil, fmt.Errorf("attested execution requires verification")
	}

	cfg := s.cfg.Attested
	mergeAttestedRequest(&cfg, req.Execution.Attestation)
	cfg.Verify = true

	if cfg.DriverPath == "" {
		return nil, fmt.Errorf("attested execution requires driver_path")
	}
	if cfg.InputPrefix == "" {
		return nil, fmt.Errorf("attested execution requires input_prefix")
	}
	if cfg.ExecAMI == "" {
		return nil, fmt.Errorf("attested execution requires exec_ami")
	}
	if cfg.ExpectedPCR4 == "" {
		return nil, fmt.Errorf("attested execution requires expected_pcr4")
	}
	if cfg.ExpectedPCR7 == "" {
		return nil, fmt.Errorf("attested execution requires expected_pcr7")
	}
	if err := validateAttestedNumbers(cfg); err != nil {
		return nil, err
	}
	if err := validateAttestedS3Config(cfg); err != nil {
		return nil, err
	}
	cfg.OutputPrefix = resolvedAttestedOutputPrefix(cfg.OutputPrefix, cfg.OutputRoot, runID)

	requested := *req.Execution
	return &ClerkExecutionRecord{
		Mode:      clerkExecutionAttested,
		Requested: &requested,
		Resolved:  &cfg,
		Attestation: &ClerkAttestationRecord{
			Status:       attestationStatusPending,
			InputPrefix:  cfg.InputPrefix,
			OutputPrefix: cfg.OutputPrefix,
			ExecAMI:      cfg.ExecAMI,
		},
	}, nil
}

func validateAttestedCaseRequest(req CaseCreateRequest) error {
	if strings.TrimSpace(req.ScenarioPath) != "" {
		return fmt.Errorf("attested execution supports complaint_path only")
	}
	var fields []string
	if req.Court != "" {
		fields = append(fields, "court")
	}
	if req.Model != "" {
		fields = append(fields, "model")
	}
	if req.NonJurorModel != "" {
		fields = append(fields, "non_juror_model")
	}
	if req.PlaintiffModel != "" {
		fields = append(fields, "plaintiff_model")
	}
	if req.DefendantModel != "" {
		fields = append(fields, "defendant_model")
	}
	if req.JudgeModel != "" {
		fields = append(fields, "judge_model")
	}
	if req.ClerkModel != "" {
		fields = append(fields, "clerk_model")
	}
	if req.PlannerModel != "" {
		fields = append(fields, "planner_model")
	}
	if req.ReportModel != "" {
		fields = append(fields, "report_model")
	}
	if req.Temperature != "" {
		fields = append(fields, "temperature")
	}
	if req.NonJurorTemperature != "" {
		fields = append(fields, "non_juror_temperature")
	}
	if req.JurorTemperature != "" {
		fields = append(fields, "juror_temperature")
	}
	if req.JurorPersonas != "" {
		fields = append(fields, "juror_personas")
	}
	if req.TrialMode != "" {
		fields = append(fields, "trial_mode")
	}
	if req.SkipVoirDire {
		fields = append(fields, "skip_voir_dire")
	}
	if req.JurorCount != 0 {
		fields = append(fields, "juror_count")
	}
	if req.MinimumConcurring != 0 {
		fields = append(fields, "minimum_concurring")
	}
	if req.UnanimousRequired != nil {
		fields = append(fields, "unanimous_required")
	}
	if req.Online {
		fields = append(fields, "online")
	}
	if req.Offline {
		fields = append(fields, "offline")
	}
	if req.TimeoutSeconds != 0 {
		fields = append(fields, "timeout_seconds")
	}
	if req.RoleAPITimeoutSeconds != 0 {
		fields = append(fields, "roleapi_timeout_seconds")
	}
	if req.LawyerTimeoutSeconds != 0 {
		fields = append(fields, "lawyer_timeout_seconds")
	}
	if req.JurorTimeoutSeconds != 0 {
		fields = append(fields, "juror_timeout_seconds")
	}
	if req.InvalidAttemptLimit != 0 {
		fields = append(fields, "invalid_attempt_limit")
	}
	if req.MaxResponseBytes != 0 {
		fields = append(fields, "max_response_bytes")
	}
	if req.EnginePath != "" {
		fields = append(fields, "engine_path")
	}
	if len(req.ExternalRoles) > 0 {
		fields = append(fields, "external_roles")
	}
	if req.MCPListenAddr != "" {
		fields = append(fields, "mcp_listen")
	}
	if req.MCPPublicBaseURL != "" {
		fields = append(fields, "mcp_public_base_url")
	}
	if req.MCPBearerToken != "" {
		fields = append(fields, "mcp_bearer_token")
	}
	if req.LawyerInstructions != "" {
		fields = append(fields, "lawyer_instructions")
	}
	if req.RemoteLawyerSkill != "" {
		fields = append(fields, "remote_lawyer_skill")
	}
	if req.JurorInstructions != "" {
		fields = append(fields, "juror_instructions")
	}
	if req.AutoLawyers != "" {
		fields = append(fields, "auto_lawyers")
	}
	if req.DockerCommand != "" {
		fields = append(fields, "docker_command")
	}
	if req.PodmanCommand != "" {
		fields = append(fields, "podman_command")
	}
	if req.OpenClawImage != "" {
		fields = append(fields, "openclaw_image")
	}
	if req.OpenClawModel != "" {
		fields = append(fields, "openclaw_model")
	}
	if req.OpenClawThinking != "" {
		fields = append(fields, "openclaw_thinking")
	}
	if req.OpenClawTimeoutSeconds != 0 {
		fields = append(fields, "openclaw_timeout_seconds")
	}
	if req.OpenClawAuth != "" {
		fields = append(fields, "openclaw_auth")
	}
	if req.OpenClawCodexAuthPath != "" {
		fields = append(fields, "openclaw_codex_auth_path")
	}
	if req.OpenClawStartDelaySeconds != nil {
		fields = append(fields, "openclaw_lawyer_start_delay_seconds")
	}
	if req.PiImage != "" {
		fields = append(fields, "pi_image")
	}
	if req.PiMCPAdapter != "" {
		fields = append(fields, "pi_mcp_adapter")
	}
	if req.JurorOutputLimitBytes != 0 {
		fields = append(fields, "juror_output_limit_bytes")
	}
	if req.DockerMCPHost != "" {
		fields = append(fields, "docker_mcp_host")
	}
	if req.PodmanMCPHost != "" {
		fields = append(fields, "podman_mcp_host")
	}
	if len(fields) > 0 {
		return fmt.Errorf("attested execution does not support these local run fields yet: %s", strings.Join(fields, ", "))
	}
	return nil
}

func resolvedAttestedOutputPrefix(outputPrefix string, outputRoot string, runID string) string {
	if outputPrefix != "" {
		return outputPrefix
	}
	if outputRoot == "" {
		return ""
	}
	return strings.TrimRight(outputRoot, "/") + "/" + runID
}

func mergeAttestedRequest(cfg *AttestedClerkConfig, req *ClerkAttestationRequest) {
	cfg.DriverPath = firstNonEmpty(req.DriverPath, cfg.DriverPath)
	cfg.UV = firstNonEmpty(req.UV, cfg.UV)
	cfg.ParserPath = firstNonEmpty(req.ParserPath, cfg.ParserPath)
	cfg.InputPrefix = firstNonEmpty(req.InputPrefix, cfg.InputPrefix)
	cfg.OutputPrefix = firstNonEmpty(req.OutputPrefix, cfg.OutputPrefix)
	cfg.OutputRoot = firstNonEmpty(req.OutputRoot, cfg.OutputRoot)
	cfg.ExecAMI = firstNonEmpty(req.ExecAMI, cfg.ExecAMI)
	cfg.DevHost = firstNonEmpty(req.DevHost, cfg.DevHost)
	cfg.RemoteAttestDir = firstNonEmpty(req.RemoteAttestDir, cfg.RemoteAttestDir)
	cfg.AWSRegion = firstNonEmpty(req.AWSRegion, cfg.AWSRegion)
	cfg.InstanceType = firstNonEmpty(req.InstanceType, cfg.InstanceType)
	cfg.IAMInstanceProfile = firstNonEmpty(req.IAMInstanceProfile, cfg.IAMInstanceProfile)
	cfg.ImageTarS3 = firstNonEmpty(req.ImageTarS3, cfg.ImageTarS3)
	cfg.ExpectedPCR4 = firstNonEmpty(req.ExpectedPCR4, cfg.ExpectedPCR4)
	cfg.ExpectedPCR7 = firstNonEmpty(req.ExpectedPCR7, cfg.ExpectedPCR7)
	cfg.ExpectedPCR12 = firstNonEmpty(req.ExpectedPCR12, cfg.ExpectedPCR12)
	if req.RootVolumeSizeGB != 0 {
		cfg.RootVolumeSizeGB = req.RootVolumeSizeGB
	}
	if req.ExecPollAttempts != 0 {
		cfg.ExecPollAttempts = req.ExecPollAttempts
	}
	if req.PollIntervalSeconds != 0 {
		cfg.PollIntervalSeconds = req.PollIntervalSeconds
	}
	if req.TimeoutSeconds != 0 {
		cfg.TimeoutSeconds = req.TimeoutSeconds
	}
}

func validateAttestedS3Config(cfg AttestedClerkConfig) error {
	for name, value := range map[string]string{
		"input_prefix":  cfg.InputPrefix,
		"output_prefix": cfg.OutputPrefix,
		"output_root":   cfg.OutputRoot,
		"image_tar_s3":  cfg.ImageTarS3,
	} {
		if value == "" {
			continue
		}
		if !strings.HasPrefix(value, "s3://") {
			return fmt.Errorf("%s must use s3://", name)
		}
	}
	return nil
}

func validateAttestedNumbers(cfg AttestedClerkConfig) error {
	for name, value := range map[string]int{
		"root_volume_size_gb":   cfg.RootVolumeSizeGB,
		"exec_poll_attempts":    cfg.ExecPollAttempts,
		"poll_interval_seconds": cfg.PollIntervalSeconds,
		"timeout_seconds":       cfg.TimeoutSeconds,
	} {
		if value < 0 {
			return fmt.Errorf("%s must be non-negative", name)
		}
	}
	return nil
}

func attestedCaseCommand(req CaseCreateRequest, rec *CaseRecord, outDir string) (string, []string, error) {
	if rec.Execution == nil || rec.Execution.Resolved == nil {
		return "", nil, fmt.Errorf("attested execution config is missing")
	}
	cfg := *rec.Execution.Resolved
	args := []string{
		"--input-prefix", cfg.InputPrefix,
		"--exec-ami", cfg.ExecAMI,
		"--case-id", rec.CaseID,
		"--run-id", rec.RunID,
		"--out-dir", outDir,
		"--allow-nonempty-out-dir",
		"--verify",
		"--expected-pcr4", cfg.ExpectedPCR4,
		"--expected-pcr7", cfg.ExpectedPCR7,
		"--complaint", req.ComplaintPath,
	}
	if cfg.OutputPrefix != "" {
		args = append(args, "--output-prefix", cfg.OutputPrefix)
	}
	if cfg.OutputRoot != "" {
		args = append(args, "--output-root", cfg.OutputRoot)
	}
	if cfg.DevHost != "" {
		args = append(args, "--dev-host", cfg.DevHost)
	}
	if cfg.RemoteAttestDir != "" {
		args = append(args, "--remote-attest-dir", cfg.RemoteAttestDir)
	}
	if cfg.AWSRegion != "" {
		args = append(args, "--aws-region", cfg.AWSRegion)
	}
	if cfg.InstanceType != "" {
		args = append(args, "--instance-type", cfg.InstanceType)
	}
	if cfg.IAMInstanceProfile != "" {
		args = append(args, "--iam-instance-profile", cfg.IAMInstanceProfile)
	}
	if cfg.ImageTarS3 != "" {
		args = append(args, "--image-tar-s3", cfg.ImageTarS3)
	}
	if cfg.RootVolumeSizeGB != 0 {
		args = append(args, "--root-volume-size-gb", fmt.Sprint(cfg.RootVolumeSizeGB))
	}
	if cfg.ExecPollAttempts != 0 {
		args = append(args, "--exec-poll-attempts", fmt.Sprint(cfg.ExecPollAttempts))
	}
	if cfg.PollIntervalSeconds != 0 {
		args = append(args, "--poll-interval-seconds", fmt.Sprint(cfg.PollIntervalSeconds))
	}
	if cfg.TimeoutSeconds != 0 {
		args = append(args, "--timeout-seconds", fmt.Sprint(cfg.TimeoutSeconds))
	}
	if cfg.ParserPath != "" {
		args = append(args, "--parser", cfg.ParserPath)
	}
	if cfg.ExpectedPCR12 != "" {
		args = append(args, "--expected-pcr12", cfg.ExpectedPCR12)
	}
	if cfg.UV != "" {
		return cfg.UV, append([]string{"run", cfg.DriverPath}, args...), nil
	}
	return cfg.DriverPath, args, nil
}

func buildAttestedCaseUpdate(rec *CaseRecord, exitCode int) attestedCaseUpdate {
	outDir := rec.OutputDir
	cfg := AttestedClerkConfig{}
	if rec.Execution != nil && rec.Execution.Resolved != nil {
		cfg = *rec.Execution.Resolved
	}
	runEnvPath := filepath.Join(outDir, "run.env")
	env, envErr := readSimpleEnvFile(runEnvPath)
	if envErr != nil {
		return attestedCaseUpdate{err: envErr.Error()}
	}
	att := &ClerkAttestationRecord{
		Status:       attestationStatusFailed,
		InputPrefix:  firstNonEmpty(env["INPUT_PREFIX"], cfg.InputPrefix),
		OutputPrefix: firstNonEmpty(env["OUTPUT_PREFIX"], cfg.OutputPrefix),
		ExecAMI:      firstNonEmpty(env["EXEC_AMI"], cfg.ExecAMI),
		RunEnv:       existingPath(runEnvPath),
		ProgressLog:  existingPath(filepath.Join(outDir, "progress.log")),
		LauncherLog:  existingPath(filepath.Join(outDir, "launcher.log")),
	}
	manifestPath := filepath.Join(outDir, "manifest.json")
	att.ManifestPath = existingPath(manifestPath)
	manifestDigestPath := filepath.Join(outDir, "manifest.sha384")
	if digest, err := readOptionalTrimmedFile(manifestDigestPath); err != nil {
		return attestedCaseUpdate{attestation: att, err: err.Error()}
	} else {
		att.ManifestSHA384 = digest
	}
	att.AttestationText = existingPath(filepath.Join(outDir, "attestation.txt"))
	att.VerificationLog = existingPath(filepath.Join(outDir, "verification.log"))

	successDir := filepath.Join(outDir, "adc-output")
	partialDir := filepath.Join(outDir, "adc-partial")
	successArchive := filepath.Join(outDir, "adc-output.tar.gz")
	partialArchive := filepath.Join(outDir, "adc-partial.tar.gz")
	if isDir(successDir) {
		att.LocalOutputDir = successDir
		att.LocalArchive = existingPath(successArchive)
	}
	if att.LocalOutputDir == "" && isDir(partialDir) {
		att.LocalOutputDir = partialDir
		att.LocalArchive = existingPath(partialArchive)
		att.Status = attestationStatusPartial
	}
	if exitCode != 0 {
		return attestedCaseUpdate{attestation: att}
	}
	if att.VerificationLog == "" {
		return attestedCaseUpdate{attestation: att, err: "attested execution completed without verification.log"}
	}
	if att.LocalOutputDir == "" {
		return attestedCaseUpdate{attestation: att, err: "attested execution completed without extracted adc-output"}
	}
	summary, err := readRunJSONFromDir(att.LocalOutputDir)
	if err != nil {
		return attestedCaseUpdate{attestation: att, err: fmt.Sprintf("attested execution completed without readable run.json: %v", err)}
	}
	att.Status = attestationStatusVerified
	return attestedCaseUpdate{attestation: att, summary: summary}
}

func readSimpleEnvFile(path string) (map[string]string, error) {
	out := map[string]string{}
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return out, nil
		}
		return nil, fmt.Errorf("read %s: %w", path, err)
	}
	lines := strings.Split(string(data), "\n")
	for i, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		name, value, ok := strings.Cut(line, "=")
		if !ok {
			return nil, fmt.Errorf("read %s: line %d has no '='", path, i+1)
		}
		name = strings.TrimSpace(name)
		if name == "" {
			return nil, fmt.Errorf("read %s: line %d has an empty name", path, i+1)
		}
		out[name] = strings.TrimSpace(value)
	}
	return out, nil
}

func readOptionalTrimmedFile(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return "", nil
		}
		return "", fmt.Errorf("read %s: %w", path, err)
	}
	return strings.TrimSpace(string(data)), nil
}

func existingPath(path string) string {
	if path == "" {
		return ""
	}
	if _, err := os.Stat(path); err == nil {
		return path
	}
	return ""
}

func isDir(path string) bool {
	st, err := os.Stat(path)
	return err == nil && st.IsDir()
}

func caseEffectiveOutputDir(rec CaseRecord) string {
	if rec.Execution != nil && rec.Execution.Mode == clerkExecutionAttested {
		if rec.Execution.Attestation != nil && rec.Execution.Attestation.LocalOutputDir != "" {
			return rec.Execution.Attestation.LocalOutputDir
		}
		successDir := filepath.Join(rec.OutputDir, "adc-output")
		if isDir(successDir) {
			return successDir
		}
		partialDir := filepath.Join(rec.OutputDir, "adc-partial")
		if isDir(partialDir) {
			return partialDir
		}
	}
	return rec.OutputDir
}

func listCaseArtifacts(rec CaseRecord) ([]map[string]any, error) {
	outputDir := caseEffectiveOutputDir(rec)
	infos, err := listArtifacts(outputDir)
	if err != nil && outputDir != rec.OutputDir {
		infos = nil
	} else if err != nil {
		return nil, err
	}
	seen := map[string]bool{}
	for _, info := range infos {
		if name, ok := info["name"].(string); ok {
			seen[name] = true
		}
	}
	for _, name := range listedCaseTopArtifactNames() {
		path := filepath.Join(rec.OutputDir, name)
		if _, err := os.Stat(path); err != nil {
			if os.IsNotExist(err) {
				continue
			}
			return nil, err
		}
		if seen[name] {
			continue
		}
		path, err := safeArtifactPath(rec.OutputDir, name)
		if err != nil {
			return nil, err
		}
		st, err := os.Stat(path)
		if err != nil {
			return nil, err
		}
		infos = append(infos, map[string]any{"name": name, "size_bytes": st.Size()})
	}
	return infos, nil
}

func caseArtifactPath(rec CaseRecord, name string) (string, error) {
	if listedCaseTopArtifactName(name) {
		if path, err := safeArtifactPath(rec.OutputDir, name); err == nil {
			if _, statErr := os.Stat(path); statErr == nil {
				return path, nil
			} else if !os.IsNotExist(statErr) {
				return "", statErr
			}
		} else {
			return "", err
		}
	}
	return safeArtifactPath(caseEffectiveOutputDir(rec), name)
}

func listedCaseTopArtifactName(name string) bool {
	for _, candidate := range listedCaseTopArtifactNames() {
		if name == candidate {
			return true
		}
	}
	return false
}

func listedCaseTopArtifactNames() []string {
	return []string{
		"service-logs/adc.stdout",
		"service-logs/adc.stderr",
		"run.env",
		"progress.log",
		"launcher.log",
		"run.log",
		"manifest.json",
		"manifest.sha384",
		"attestation.b64",
		"attestation.txt",
		"verification.log",
		"case.tar.gz",
		"case-packet.json",
		"adc-output.tar.gz",
		"adc-partial.tar.gz",
	}
}

func (s *Server) handleCaseAttestationEvents(w http.ResponseWriter, r *http.Request, caseID string) {
	rec, ok := s.getCasePtr(caseID)
	if !ok {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("unknown_case", "unknown case_id")})
		return
	}
	if rec.Execution == nil || rec.Execution.Mode != clerkExecutionAttested {
		writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("attestation_events_unavailable", "case is not an attested execution")})
		return
	}
	if path := existingPath(filepath.Join(caseEffectiveOutputDir(publicRecord(rec)), attestedEventsArtifactName)); path != "" {
		w.Header().Set("Content-Type", attestedEventsContentType)
		http.ServeFile(w, r, path)
		return
	}
	raw, err := fetchAttestationEventsFromS3(*rec)
	if err != nil {
		if isAttestedEventsMissing(err) {
			writeJSON(w, http.StatusNotFound, map[string]any{"ok": false, "case_id": caseID, "error": apiError("attestation_events_unavailable", err.Error())})
			return
		}
		writeJSON(w, http.StatusInternalServerError, map[string]any{"ok": false, "case_id": caseID, "error": apiError("attestation_events_failed", err.Error())})
		return
	}
	w.Header().Set("Content-Type", attestedEventsContentType)
	http.ServeContent(w, r, attestedEventsArtifactName, time.Time{}, bytes.NewReader(raw))
}

func fetchAttestationEventsFromS3(rec CaseRecord) ([]byte, error) {
	for _, root := range []string{caseEffectiveOutputDir(rec), rec.OutputDir} {
		path := filepath.Join(root, attestedEventsArtifactName)
		raw, err := os.ReadFile(path)
		if err == nil {
			return raw, nil
		}
		if err != nil && !os.IsNotExist(err) {
			return nil, fmt.Errorf("read %s: %w", path, err)
		}
	}
	outputPrefix, err := caseAttestedOutputPrefix(rec)
	if err != nil {
		return nil, err
	}
	if outputPrefix == "" {
		return nil, &attestedEventsMissingError{message: "attested output prefix is unknown"}
	}
	devHost, awsRegion := caseAttestedReaderConfig(rec)
	eventsKey := strings.TrimRight(outputPrefix, "/") + "/" + attestedEventsArtifactName
	ctx, cancel := context.WithTimeout(context.Background(), attestedEventsFetchTimeout)
	defer cancel()
	cmd := exec.CommandContext(
		ctx,
		"ssh",
		devHost,
		fmt.Sprintf("AWS_DEFAULT_REGION=%s aws s3 cp %s -", shellQuote(awsRegion), shellQuote(eventsKey)),
	)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	raw, err := cmd.Output()
	if err != nil {
		message := strings.TrimSpace(stderr.String())
		if message == "" {
			message = err.Error()
		}
		return nil, &attestedEventsMissingError{message: fmt.Sprintf("%s: %s", attestedEventsMissingMessage, message)}
	}
	return raw, nil
}

func caseAttestedOutputPrefix(rec CaseRecord) (string, error) {
	env, err := readSimpleEnvFile(filepath.Join(rec.OutputDir, "run.env"))
	if err != nil {
		return "", err
	}
	cfg := AttestedClerkConfig{}
	if rec.Execution != nil && rec.Execution.Resolved != nil {
		cfg = *rec.Execution.Resolved
	}
	recordPrefix := ""
	if rec.Execution != nil && rec.Execution.Attestation != nil {
		recordPrefix = rec.Execution.Attestation.OutputPrefix
	}
	return firstNonEmpty(env["OUTPUT_PREFIX"], recordPrefix, cfg.OutputPrefix), nil
}

func caseAttestedReaderConfig(rec CaseRecord) (string, string) {
	cfg := AttestedClerkConfig{}
	if rec.Execution != nil && rec.Execution.Resolved != nil {
		cfg = *rec.Execution.Resolved
	}
	return firstNonEmpty(cfg.DevHost, defaultAttestedDevHost), firstNonEmpty(cfg.AWSRegion, defaultAttestedAWSRegion)
}

type attestedEventsMissingError struct {
	message string
}

func (e *attestedEventsMissingError) Error() string {
	return e.message
}

func isAttestedEventsMissing(err error) bool {
	var missing *attestedEventsMissingError
	return errors.As(err, &missing)
}

func shellQuote(value string) string {
	if value == "" {
		return "''"
	}
	return "'" + strings.ReplaceAll(value, "'", "'\\''") + "'"
}
