package service

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

const (
	clerkExecutionLocal    = "local"
	clerkExecutionAttested = "attested"

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

type attestedClerkUpdate struct {
	attestation *ClerkAttestationRecord
	summary     map[string]any
	err         string
}

func (s *Server) resolveClerkExecution(req ClerkCreateRequest) (*ClerkExecutionRecord, error) {
	if req.Execution == nil {
		return nil, nil
	}

	mode := strings.TrimSpace(req.Execution.Mode)
	if mode == "" {
		return nil, fmt.Errorf("execution mode is required when execution is set")
	}

	switch mode {
	case clerkExecutionLocal:
		if req.Execution.Attestation != nil {
			return nil, fmt.Errorf("local execution does not accept attestation config")
		}
		return nil, nil
	case clerkExecutionAttested:
		return s.resolveAttestedClerkExecution(req)
	default:
		return nil, fmt.Errorf("unsupported execution mode %q", mode)
	}
}

func (s *Server) resolveAttestedClerkExecution(req ClerkCreateRequest) (*ClerkExecutionRecord, error) {
	if err := validateAttestedClerkRequest(req); err != nil {
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

func validateAttestedClerkRequest(req ClerkCreateRequest) error {
	var fields []string
	if req.PolicyPath != "" {
		fields = append(fields, "policy_path")
	}
	if req.CouncilSize != 0 {
		fields = append(fields, "council_size")
	}
	if req.EvidenceStandard != "" {
		fields = append(fields, "evidence_standard")
	}
	if req.AttorneyInstructionsPath != "" {
		fields = append(fields, "attorney_instructions")
	}
	if req.PromptDir != "" {
		fields = append(fields, "prompt_dir")
	}
	if req.AttorneyCommonPromptPath != "" {
		fields = append(fields, "attorney_common_prompt")
	}
	if req.AttorneyArgumentPromptPath != "" {
		fields = append(fields, "attorney_arguments_prompt")
	}
	if req.AttorneyRebuttalPromptPath != "" {
		fields = append(fields, "attorney_rebuttals_prompt")
	}
	if req.CommonRoot != "" {
		fields = append(fields, "common_root")
	}
	if req.CouncilPoolPath != "" {
		fields = append(fields, "council_pool")
	}
	if req.CaseAPIAddr != "" {
		fields = append(fields, "caseapi_addr")
	}
	if req.MCPListenAddr != "" {
		fields = append(fields, "mcp_listen")
	}
	if req.MCPBearerToken != "" {
		fields = append(fields, "mcp_bearer_token")
	}
	if req.CouncilTimeoutSeconds != 0 {
		fields = append(fields, "council_timeout_seconds")
	}
	if req.LawyerTimeoutSeconds != 0 {
		fields = append(fields, "lawyer_timeout_seconds")
	}
	if req.MaxResponseBytes != 0 {
		fields = append(fields, "max_response_bytes")
	}
	if req.InvalidAttemptLimit != 0 {
		fields = append(fields, "invalid_attempt_limit")
	}
	if req.EnginePath != "" {
		fields = append(fields, "engine")
	}
	if req.LawyerInstructionsPath != "" {
		fields = append(fields, "lawyer_instructions")
	}
	if req.RemoteLawyerSkillPath != "" {
		fields = append(fields, "remote_lawyer_skill")
	}
	if req.CouncilInstructionsPath != "" {
		fields = append(fields, "council_instructions")
	}
	if req.AutoLawyers != "" {
		fields = append(fields, "auto_lawyers")
	}
	if req.MCPPublicBaseURL != "" {
		fields = append(fields, "mcp_public_base_url")
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
	if req.CouncilOutputLimitBytes != 0 {
		fields = append(fields, "council_output_limit_bytes")
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

func attestedClerkCommand(req ClerkCreateRequest, rec *ClerkRecord, outDir string) (string, []string, error) {
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
	}
	if rec.Example != "" {
		args = append(args, "--example", rec.Example)
	}
	if req.ComplaintPath != "" {
		args = append(args, "--complaint", req.ComplaintPath)
		for _, file := range req.CaseFiles {
			args = append(args, "--file", file)
		}
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

func buildAttestedClerkUpdate(rec *ClerkRecord, exitCode int) attestedClerkUpdate {
	outDir := rec.OutDir
	cfg := AttestedClerkConfig{}
	if rec.Execution != nil && rec.Execution.Resolved != nil {
		cfg = *rec.Execution.Resolved
	}

	runEnvPath := filepath.Join(outDir, "run.env")
	env, envErr := readSimpleEnvFile(runEnvPath)
	if envErr != nil {
		return attestedClerkUpdate{err: envErr.Error()}
	}

	att := &ClerkAttestationRecord{
		Status:       attestationStatusFailed,
		InputPrefix:  firstNonEmpty(env["INPUT_PREFIX"], env["AAR_INPUT_PREFIX"], cfg.InputPrefix),
		OutputPrefix: firstNonEmpty(env["OUTPUT_PREFIX"], env["AAR_OUTPUT_PREFIX"], cfg.OutputPrefix),
		ExecAMI:      firstNonEmpty(env["EXEC_AMI"], cfg.ExecAMI),
		RunEnv:       existingPath(runEnvPath),
		ProgressLog:  existingPath(filepath.Join(outDir, "progress.log")),
		LauncherLog:  existingPath(filepath.Join(outDir, "launcher.log")),
	}

	manifestPath := filepath.Join(outDir, "manifest.json")
	att.ManifestPath = existingPath(manifestPath)
	manifestDigestPath := filepath.Join(outDir, "manifest.sha384")
	if digest, err := readOptionalTrimmedFile(manifestDigestPath); err != nil {
		return attestedClerkUpdate{attestation: att, err: err.Error()}
	} else {
		att.ManifestSHA384 = digest
	}
	att.AttestationText = existingPath(filepath.Join(outDir, "attestation.txt"))
	att.VerificationLog = existingPath(filepath.Join(outDir, "verification.log"))

	successDir := filepath.Join(outDir, "aar-output")
	partialDir := filepath.Join(outDir, "aar-partial")
	successArchive := filepath.Join(outDir, "aar-output.tar.gz")
	partialArchive := filepath.Join(outDir, "aar-partial.tar.gz")
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
		if att.Status == "" {
			att.Status = attestationStatusFailed
		}
		return attestedClerkUpdate{attestation: att}
	}
	if att.VerificationLog == "" {
		return attestedClerkUpdate{attestation: att, err: "attested execution completed without verification.log"}
	}
	if att.LocalOutputDir == "" {
		return attestedClerkUpdate{attestation: att, err: "attested execution completed without extracted aar-output"}
	}

	summary, err := readRunJSONFromDir(att.LocalOutputDir)
	if err != nil {
		return attestedClerkUpdate{attestation: att, err: fmt.Sprintf("attested execution completed without readable run.json: %v", err)}
	}
	att.Status = attestationStatusVerified
	return attestedClerkUpdate{attestation: att, summary: summary}
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

func clerkEffectiveOutputDir(rec ClerkRecord) string {
	if rec.Execution != nil && rec.Execution.Mode == clerkExecutionAttested {
		if rec.Execution.Attestation != nil && rec.Execution.Attestation.LocalOutputDir != "" {
			return rec.Execution.Attestation.LocalOutputDir
		}
		successDir := filepath.Join(rec.OutDir, "aar-output")
		if isDir(successDir) {
			return successDir
		}
		partialDir := filepath.Join(rec.OutDir, "aar-partial")
		if isDir(partialDir) {
			return partialDir
		}
	}
	return rec.OutDir
}

func listClerkArtifacts(rec ClerkRecord) ([]map[string]any, error) {
	outputDir := clerkEffectiveOutputDir(rec)
	infos, err := listArtifacts(outputDir)
	if err != nil && outputDir != rec.OutDir {
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
	for _, name := range listedClerkTopArtifactNames() {
		path := filepath.Join(rec.OutDir, name)
		if _, err := os.Stat(path); err != nil {
			if os.IsNotExist(err) {
				continue
			}
			return nil, err
		}
		if seen[name] {
			continue
		}
		path, err := safeArtifactPath(rec.OutDir, name)
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

func clerkArtifactPath(rec ClerkRecord, name string) (string, error) {
	if listedClerkTopArtifactName(name) {
		if path, err := safeArtifactPath(rec.OutDir, name); err == nil {
			if _, statErr := os.Stat(path); statErr == nil {
				return path, nil
			} else if !os.IsNotExist(statErr) {
				return "", statErr
			}
		} else {
			return "", err
		}
	}
	return safeArtifactPath(clerkEffectiveOutputDir(rec), name)
}

func listedClerkTopArtifactName(name string) bool {
	for _, candidate := range listedClerkTopArtifactNames() {
		if name == candidate {
			return true
		}
	}
	return false
}

func listedClerkTopArtifactNames() []string {
	return []string{
		"clerk.stdout",
		"clerk.stderr",
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
		"aar-output.tar.gz",
		"aar-partial.tar.gz",
	}
}
