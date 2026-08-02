package localrun

import (
	"bytes"
	"context"
	"crypto/rand"
	_ "embed"
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
	"strings"
	"sync"
	"sync/atomic"
	"text/template"
	"time"

	"adjudication/common/modelrequest"
	ardmcp "adjudication/service/mcp/arbd"
)

const (
	defaultOpenClawImage          = "ghcr.io/openclaw/openclaw:latest"
	defaultOpenClawModel          = "gpt-5.5"
	defaultOpenClawThinking       = "low"
	defaultOpenClawTimeoutSeconds = 3600
	defaultOpenClawAuth           = "auto"
	defaultOpenClawStartDelay     = 15
	defaultPiImage                = "agentcourt-pi-sandbox"
	defaultPiMCPAdapter           = "/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter"
	defaultPiMCPServer            = "aard"
	defaultCaseAPIStartupWait     = 10 * time.Minute
	defaultMCPStartupWait         = 30 * time.Second
	defaultCouncilRosterWait      = 2 * time.Minute
	defaultCouncilOutputCheck     = 5 * time.Second
	councilFailureAgentExited     = "agent_exited"
	councilFailureOutputLimit     = "agent_output_limit_exceeded"
	openClawCodexContainerHome    = "/aard-codex"
)

const (
	DefaultRunCouncilTimeoutSeconds = 15 * 60
	DefaultRunLawyerTimeoutSeconds  = DefaultRunCouncilTimeoutSeconds
	DefaultCouncilOutputLimitBytes  = 128 * 1024 * 1024
	DefaultCouncilMaxOutputTokens   = 4096
	DefaultAutoLawyers              = "both"
	DefaultDockerCommand            = "docker"
	DefaultPodmanCommand            = "podman"
	DefaultCoreCommand              = "aard"
)

const (
	defaultLawyerInstructions  = "embedded:arbd/openclaw-lawyer"
	defaultRemoteLawyerSkill   = "embedded:arbd/openclaw-remote-lawyer-skill"
	defaultCouncilInstructions = "embedded:arbd/pi-council"
)

func DefaultLawyerInstructionsPath() string {
	return defaultLawyerInstructions
}

func DefaultRemoteLawyerSkillPath() string {
	return defaultRemoteLawyerSkill
}

func DefaultCouncilInstructionsPath() string {
	return defaultCouncilInstructions
}

//go:embed agent-instructions/openclaw-lawyer.md.tmpl
var embeddedLawyerInstructions string

//go:embed agent-instructions/openclaw-remote-lawyer-skill.md.tmpl
var embeddedRemoteLawyerSkill string

//go:embed agent-instructions/pi-council.md.tmpl
var embeddedCouncilInstructions string

type Options struct {
	CoreCommand                string
	CoreWorkingDir             string
	ComplaintPath              string
	CaseFiles                  []string
	OutputDir                  string
	PolicyPath                 string
	CouncilSize                int
	JudgmentStandard           string
	AttorneyInstructionsPath   string
	PromptDir                  string
	AttorneyCommonPromptPath   string
	AttorneyArgumentPromptPath string
	AttorneyRebuttalPromptPath string
	CommonRoot                 string
	CouncilPoolPath            string
	CaseAPIAddr                string
	MCPListenAddr              string
	MCPBearerToken             string
	CouncilTimeoutSeconds      int
	LawyerTimeoutSeconds       int
	MaxResponseBytes           int
	InvalidAttemptLimit        int
	EnginePath                 string
	RunID                      string
	CaseID                     string
	LawyerInstructionsPath     string
	RemoteLawyerSkillPath      string
	CouncilInstructionsPath    string
	AutoLawyers                string
	MCPPublicBaseURL           string
	DockerCommand              string
	PodmanCommand              string
	OpenClawImage              string
	OpenClawModel              string
	OpenClawThinking           string
	OpenClawTimeoutSeconds     int
	OpenClawAuth               string
	OpenClawCodexAuthPath      string
	OpenClawStartDelaySeconds  int
	OpenClawNetwork            string
	PiImage                    string
	PiMCPAdapter               string
	CouncilOutputLimitBytes    int64
	DockerMCPHost              string
	PodmanMCPHost              string
	Log                        io.Writer
}

type Result struct {
	CaseID  string         `json:"case_id"`
	RunID   string         `json:"run_id"`
	Status  string         `json:"status"`
	Answers map[string]int `json:"answers"`
	Error   string         `json:"error,omitempty"`
	Failure map[string]any `json:"failure,omitempty"`

	raw json.RawMessage
}

func (r Result) MarshalJSON() ([]byte, error) {
	if len(r.raw) > 0 {
		return append([]byte(nil), r.raw...), nil
	}
	type resultAlias Result
	return json.Marshal(resultAlias(r))
}

type instructionData struct {
	CaseID    string
	RoleID    string
	MemberID  string
	MCPServer string
	MCPURL    string
	MCPJSON   string
}

type processRecord struct {
	name     string
	kind     string
	command  *exec.Cmd
	done     chan error
	stopName string

	stdoutPath string
	stderrPath string
	finished   chan struct{}

	stdoutCounter *processOutputCounter

	mu            sync.Mutex
	exited        bool
	forcedReason  string
	forcedMessage string
	forcedDetails map[string]any
}

type councilProcessTarget struct {
	memberID      string
	opportunityID string
}

type councilRosterResponse struct {
	CouncilRoster []councilRosterEntry `json:"council_roster"`
}

type councilStatusResponse struct {
	Status string             `json:"status"`
	Turn   *councilStatusTurn `json:"turn"`
	Error  any                `json:"error"`
}

type councilStatusTurn struct {
	MemberID      string `json:"member_id"`
	OpportunityID string `json:"opportunity_id"`
}

type processOutputSize struct {
	Stdout int64
	Stderr int64
	Total  int64
}

type processOutputCounter struct {
	dst   io.Writer
	count atomic.Int64
}

func newProcessOutputCounter(dst io.Writer) *processOutputCounter {
	return &processOutputCounter{dst: dst}
}

func (w *processOutputCounter) Write(p []byte) (int, error) {
	n, err := w.dst.Write(p)
	if n > 0 {
		w.count.Add(int64(n))
	}
	return n, err
}

func (w *processOutputCounter) Size() int64 {
	return w.count.Load()
}

type councilRosterEntry struct {
	MemberID    string             `json:"member_id"`
	Model       string             `json:"model"`
	RequestSpec *modelrequest.Spec `json:"request_spec"`
}

type runState struct {
	opts          Options
	logDir        string
	caseBase      string
	mcpBase       string
	mcpPublicBase string
	token         string
	openClawAuth  openClawAuthConfig
	processes     []*processRecord
	secretDirs    []string
	councilStarts map[string]bool
	agentErrs     chan error

	mu sync.Mutex
}

type openClawAuthConfig struct {
	Mode          string
	CodexAuthPath string
}

func Run(ctx context.Context, opts Options) (result Result, err error) {
	if ctx == nil {
		ctx = context.Background()
	}
	opts = applyDefaults(opts)
	if err := validateOptions(opts); err != nil {
		return Result{}, err
	}
	openClawAuth, err := resolveOpenClawAuth(opts)
	if err != nil {
		return Result{}, err
	}
	if err := os.MkdirAll(filepath.Join(opts.OutputDir, "logs"), 0o755); err != nil {
		return Result{}, fmt.Errorf("create output logs: %w", err)
	}
	state := &runState{
		opts:          opts,
		logDir:        filepath.Join(opts.OutputDir, "logs"),
		token:         strings.TrimSpace(opts.MCPBearerToken),
		openClawAuth:  openClawAuth,
		councilStarts: map[string]bool{},
		agentErrs:     make(chan error, 32),
	}
	if state.token == "" {
		token, err := randomToken()
		if err != nil {
			return Result{}, err
		}
		state.token = token
	}
	runCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	defer func() {
		err = errors.Join(err, state.stopAgents(), state.cleanupSecrets())
	}()

	caseAPIAddr, err := resolveListenAddr(opts.CaseAPIAddr, "127.0.0.1")
	if err != nil {
		return Result{}, fmt.Errorf("resolve case API address: %w", err)
	}
	state.caseBase = "http://" + caseAPIAddr
	mcpListenAddr, err := resolveListenAddr(opts.MCPListenAddr, "0.0.0.0")
	if err != nil {
		return Result{}, fmt.Errorf("resolve MCP listen address: %w", err)
	}
	state.mcpPublicBase, err = publicMCPBase(opts.MCPPublicBaseURL, mcpListenAddr)
	if err != nil {
		return Result{}, err
	}
	if len(manualLawyerRoles(opts.AutoLawyers)) > 0 {
		if err := validateManualLawyerAddress(opts.MCPPublicBaseURL, mcpListenAddr); err != nil {
			return Result{}, err
		}
	}
	_, mcpPort, err := net.SplitHostPort(mcpListenAddr)
	if err != nil {
		return Result{}, fmt.Errorf("parse MCP listen address %q: %w", mcpListenAddr, err)
	}
	state.mcpBase = "http://" + net.JoinHostPort("127.0.0.1", mcpPort)

	caseDone, err := startCoreCase(runCtx, opts, caseAPIAddr, state.logDir)
	if err != nil {
		return Result{}, err
	}
	if err := state.waitForCaseAPI(runCtx, caseDone); err != nil {
		cancel()
		return Result{}, err
	}

	mcpDone := make(chan error, 1)
	go func() {
		logFile, err := os.Create(filepath.Join(state.logDir, "mcp.stderr"))
		if err != nil {
			mcpDone <- fmt.Errorf("create MCP log: %w", err)
			return
		}
		defer logFile.Close()
		mcpDone <- ardmcp.Run(runCtx, ardmcp.Options{
			ListenAddr:           mcpListenAddr,
			CaseAPIBase:          state.caseBase,
			BearerToken:          state.token,
			APIBearerToken:       "",
			DisableSessionExpiry: true,
			Log:                  logFile,
		})
	}()
	if err := state.waitForMCP(runCtx, caseDone, mcpDone); err != nil {
		cancel()
		return Result{}, err
	}

	for _, role := range manualLawyerRoles(opts.AutoLawyers) {
		if err := state.writeRemoteLawyerSkill(role); err != nil {
			cancel()
			return Result{}, err
		}
	}
	startedPlaintiff := false
	if autoLawyerEnabled(opts.AutoLawyers, "plaintiff") {
		if err := state.startOpenClawLawyer(runCtx, "plaintiff", mcpPort); err != nil {
			cancel()
			return Result{}, err
		}
		startedPlaintiff = true
	}
	if autoLawyerEnabled(opts.AutoLawyers, "defendant") {
		if startedPlaintiff {
			if err := state.waitOpenClawStartDelay(runCtx); err != nil {
				cancel()
				return Result{}, err
			}
		}
		if err := state.startOpenClawLawyer(runCtx, "defendant", mcpPort); err != nil {
			cancel()
			return Result{}, err
		}
	}
	roster, err := state.waitForCouncilRoster(runCtx, caseDone, mcpDone)
	if err != nil {
		cancel()
		return Result{}, err
	}
	councilTicker := time.NewTicker(time.Second)
	defer councilTicker.Stop()

	for {
		select {
		case outcome := <-caseDone:
			cancel()
			if err := <-mcpDone; err != nil && !errors.Is(err, context.Canceled) {
				return outcome.result, err
			}
			if writeErr := writeRunSummary(opts.OutputDir, outcome.result, opts); writeErr != nil {
				return outcome.result, writeErr
			}
			return outcome.result, outcome.err
		case err := <-mcpDone:
			cancel()
			if err == nil {
				return Result{}, fmt.Errorf("MCP server exited before case completion")
			}
			return Result{}, fmt.Errorf("MCP server failed: %w", err)
		case exit := <-state.agentErrs:
			cancel()
			return Result{}, exit
		case <-councilTicker.C:
			if err := state.startReadyCouncil(runCtx, roster, mcpPort); err != nil {
				cancel()
				return Result{}, err
			}
		case <-ctx.Done():
			cancel()
			return Result{}, ctx.Err()
		}
	}
}

type caseOutcome struct {
	result Result
	err    error
}

func startCoreCase(ctx context.Context, opts Options, caseAPIAddr string, logDir string) (<-chan caseOutcome, error) {
	stdoutPath := filepath.Join(logDir, "aard.stdout")
	stderrPath := filepath.Join(logDir, "aard.stderr")
	stdout, err := os.Create(stdoutPath)
	if err != nil {
		return nil, fmt.Errorf("create core stdout log: %w", err)
	}
	stderr, err := os.Create(stderrPath)
	if err != nil {
		return nil, errors.Join(fmt.Errorf("create core stderr log: %w", err), stdout.Close())
	}
	runPath := filepath.Join(opts.OutputDir, "run.json")
	previousRun, runExisted, err := readOptionalFile(runPath)
	if err != nil {
		return nil, errors.Join(fmt.Errorf("read existing core result: %w", err), stdout.Close(), stderr.Close())
	}

	cmd := exec.CommandContext(ctx, opts.CoreCommand, coreCaseArgs(opts, caseAPIAddr)...)
	if strings.TrimSpace(opts.CoreWorkingDir) != "" {
		cmd.Dir = strings.TrimSpace(opts.CoreWorkingDir)
	}
	cmd.Stdout = stdout
	cmd.Stderr = stderr
	if err := cmd.Start(); err != nil {
		return nil, errors.Join(fmt.Errorf("start core case: %w", err), stdout.Close(), stderr.Close())
	}

	done := make(chan caseOutcome, 1)
	go func() {
		waitErr := cmd.Wait()
		closeErr := errors.Join(stdout.Close(), stderr.Close())
		result, resultErr := readCoreResult(runPath, previousRun, runExisted)
		done <- caseOutcome{
			result: result,
			err: errors.Join(
				coreProcessError(waitErr, stderrPath),
				closeErr,
				resultErr,
			),
		}
	}()
	return done, nil
}

func coreCaseArgs(opts Options, caseAPIAddr string) []string {
	args := []string{
		"case",
		"--complaint", opts.ComplaintPath,
		"--out-dir", opts.OutputDir,
		"--case-id", opts.CaseID,
		"--caseapi-addr", caseAPIAddr,
		"--council-backend", "councilapi",
	}
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
	for _, path := range opts.CaseFiles {
		addString("--file", path)
	}
	addString("--run-id", opts.RunID)
	addString("--policy", opts.PolicyPath)
	addInt("--council-size", opts.CouncilSize)
	addString("--judgment-standard", opts.JudgmentStandard)
	addString("--attorney-instructions", opts.AttorneyInstructionsPath)
	addString("--prompt-dir", opts.PromptDir)
	addString("--attorney-common-prompt", opts.AttorneyCommonPromptPath)
	addString("--attorney-arguments-prompt", opts.AttorneyArgumentPromptPath)
	addString("--attorney-rebuttals-prompt", opts.AttorneyRebuttalPromptPath)
	addString("--common-root", opts.CommonRoot)
	addString("--council-pool", opts.CouncilPoolPath)
	addInt("--timeout-seconds", opts.CouncilTimeoutSeconds)
	addInt("--lawyer-timeout-seconds", opts.LawyerTimeoutSeconds)
	addInt("--max-response-bytes", opts.MaxResponseBytes)
	addInt("--invalid-attempt-limit", opts.InvalidAttemptLimit)
	addString("--engine", opts.EnginePath)
	return args
}

func readOptionalFile(path string) ([]byte, bool, error) {
	raw, err := os.ReadFile(path)
	if errors.Is(err, os.ErrNotExist) {
		return nil, false, nil
	}
	if err != nil {
		return nil, false, err
	}
	return raw, true, nil
}

func readCoreResult(path string, previous []byte, existed bool) (Result, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return Result{}, fmt.Errorf("read core result %s: %w", path, err)
	}
	if existed && bytes.Equal(raw, previous) {
		return Result{}, fmt.Errorf("core process did not replace existing result %s", path)
	}
	var result Result
	if err := json.Unmarshal(raw, &result); err != nil {
		return Result{}, fmt.Errorf("decode core result %s: %w", path, err)
	}
	result.raw = append(json.RawMessage(nil), bytes.TrimSpace(raw)...)
	return result, nil
}

func coreProcessError(waitErr error, stderrPath string) error {
	if waitErr == nil {
		return nil
	}
	raw, readErr := readFileTail(stderrPath, 64*1024)
	message := strings.TrimSpace(string(raw))
	if message == "" {
		return errors.Join(fmt.Errorf("core case process: %w", waitErr), readErr)
	}
	return errors.Join(fmt.Errorf("core case process: %w: %s", waitErr, message), readErr)
}

func readFileTail(path string, limit int64) ([]byte, error) {
	if limit <= 0 {
		return nil, nil
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	info, err := f.Stat()
	if err != nil {
		return nil, err
	}
	offset := info.Size() - limit
	if offset < 0 {
		offset = 0
	}
	if _, err := f.Seek(offset, io.SeekStart); err != nil {
		return nil, err
	}
	raw, err := io.ReadAll(io.LimitReader(f, limit))
	if err != nil {
		return nil, err
	}
	if offset > 0 {
		if index := bytes.IndexByte(raw, '\n'); index >= 0 {
			raw = raw[index+1:]
		}
	}
	return raw, nil
}

type rosterOutcome struct {
	roster []councilRosterEntry
	err    error
}

func applyDefaults(opts Options) Options {
	if strings.TrimSpace(opts.CoreCommand) == "" {
		opts.CoreCommand = DefaultCoreCommand
	}
	if strings.TrimSpace(opts.DockerCommand) == "" {
		opts.DockerCommand = DefaultDockerCommand
	}
	if strings.TrimSpace(opts.PodmanCommand) == "" {
		opts.PodmanCommand = DefaultPodmanCommand
	}
	if strings.TrimSpace(opts.OpenClawImage) == "" {
		opts.OpenClawImage = defaultOpenClawImage
	}
	if strings.TrimSpace(opts.OpenClawModel) == "" {
		opts.OpenClawModel = defaultOpenClawModel
	}
	if strings.TrimSpace(opts.OpenClawThinking) == "" {
		opts.OpenClawThinking = defaultOpenClawThinking
	}
	if opts.OpenClawTimeoutSeconds <= 0 {
		opts.OpenClawTimeoutSeconds = defaultOpenClawTimeoutSeconds
	}
	if strings.TrimSpace(opts.OpenClawAuth) == "" {
		opts.OpenClawAuth = defaultOpenClawAuth
	}
	if opts.OpenClawStartDelaySeconds < 0 {
		opts.OpenClawStartDelaySeconds = defaultOpenClawStartDelay
	}
	if strings.TrimSpace(opts.OpenClawCodexAuthPath) == "" {
		opts.OpenClawCodexAuthPath = defaultCodexAuthPath()
	}
	if opts.CouncilTimeoutSeconds <= 0 {
		opts.CouncilTimeoutSeconds = DefaultRunCouncilTimeoutSeconds
	}
	if opts.LawyerTimeoutSeconds <= 0 {
		opts.LawyerTimeoutSeconds = DefaultRunLawyerTimeoutSeconds
	}
	if strings.TrimSpace(opts.PiImage) == "" {
		if image := strings.TrimSpace(os.Getenv("PI_CONTAINER_IMAGE")); image != "" {
			opts.PiImage = image
		} else {
			opts.PiImage = defaultPiImage
		}
	}
	if strings.TrimSpace(opts.PiMCPAdapter) == "" {
		opts.PiMCPAdapter = defaultPiMCPAdapter
	}
	if opts.CouncilOutputLimitBytes == 0 {
		opts.CouncilOutputLimitBytes = DefaultCouncilOutputLimitBytes
	}
	opts.OpenClawNetwork = strings.TrimSpace(opts.OpenClawNetwork)
	if strings.TrimSpace(opts.DockerMCPHost) == "" && opts.OpenClawNetwork == "host" {
		opts.DockerMCPHost = "127.0.0.1"
	}
	if strings.TrimSpace(opts.DockerMCPHost) == "" {
		opts.DockerMCPHost = "host.docker.internal"
	}
	if strings.TrimSpace(opts.PodmanMCPHost) == "" {
		opts.PodmanMCPHost = "127.0.0.1"
	}
	if strings.TrimSpace(opts.LawyerInstructionsPath) == "" {
		opts.LawyerInstructionsPath = DefaultLawyerInstructionsPath()
	}
	if strings.TrimSpace(opts.RemoteLawyerSkillPath) == "" {
		opts.RemoteLawyerSkillPath = DefaultRemoteLawyerSkillPath()
	}
	if strings.TrimSpace(opts.CouncilInstructionsPath) == "" {
		opts.CouncilInstructionsPath = DefaultCouncilInstructionsPath()
	}
	if strings.TrimSpace(opts.AutoLawyers) == "" {
		opts.AutoLawyers = DefaultAutoLawyers
	}
	return opts
}

func validateOptions(opts Options) error {
	if strings.TrimSpace(opts.ComplaintPath) == "" {
		return fmt.Errorf("complaint path is required")
	}
	if strings.TrimSpace(opts.OutputDir) == "" {
		return fmt.Errorf("output dir is required")
	}
	if strings.TrimSpace(opts.CaseID) == "" {
		return fmt.Errorf("case id is required")
	}
	if strings.TrimSpace(os.Getenv("OPENROUTER_API_KEY")) == "" {
		return fmt.Errorf("OPENROUTER_API_KEY is required for Pi council")
	}
	if _, err := autoLawyerRoles(opts.AutoLawyers); err != nil {
		return err
	}
	if opts.OpenClawNetwork != "" && opts.OpenClawNetwork != "host" {
		return fmt.Errorf("invalid OpenClaw network %q; expected host or empty", opts.OpenClawNetwork)
	}
	if opts.CouncilOutputLimitBytes < 0 {
		return fmt.Errorf("council output limit bytes must be non-negative")
	}
	for _, path := range []string{opts.LawyerInstructionsPath, opts.RemoteLawyerSkillPath, opts.CouncilInstructionsPath} {
		if _, ok := embeddedInstruction(path); ok {
			continue
		}
		if _, err := os.Stat(path); err != nil {
			return fmt.Errorf("stat instruction template %s: %w", path, err)
		}
	}
	return nil
}

func autoLawyerRoles(mode string) ([]string, error) {
	switch strings.ToLower(strings.TrimSpace(mode)) {
	case "both":
		return []string{"plaintiff", "defendant"}, nil
	case "plaintiff":
		return []string{"plaintiff"}, nil
	case "defendant":
		return []string{"defendant"}, nil
	default:
		return nil, fmt.Errorf("invalid auto lawyer mode %q; expected both, plaintiff, or defendant", mode)
	}
}

func autoLawyerEnabled(mode string, role string) bool {
	roles, err := autoLawyerRoles(mode)
	if err != nil {
		return false
	}
	for _, current := range roles {
		if current == role {
			return true
		}
	}
	return false
}

func manualLawyerRoles(mode string) []string {
	manual := []string{}
	for _, role := range []string{"plaintiff", "defendant"} {
		if !autoLawyerEnabled(mode, role) {
			manual = append(manual, role)
		}
	}
	return manual
}

func defaultCodexAuthPath() string {
	if codexHome := strings.TrimSpace(os.Getenv("CODEX_HOME")); codexHome != "" {
		return filepath.Join(codexHome, "auth.json")
	}
	home, err := os.UserHomeDir()
	if err != nil || strings.TrimSpace(home) == "" {
		return filepath.Join(".codex", "auth.json")
	}
	return filepath.Join(home, ".codex", "auth.json")
}

func resolveOpenClawAuth(opts Options) (openClawAuthConfig, error) {
	mode := strings.ToLower(strings.TrimSpace(opts.OpenClawAuth))
	if mode == "" {
		mode = defaultOpenClawAuth
	}
	switch mode {
	case "auto":
		path, err := validateCodexAuthPath(opts.OpenClawCodexAuthPath)
		if err == nil {
			return openClawAuthConfig{Mode: "codex", CodexAuthPath: path}, nil
		}
		if strings.TrimSpace(os.Getenv("OPENAI_API_KEY")) != "" {
			return openClawAuthConfig{Mode: "api-key"}, nil
		}
		return openClawAuthConfig{}, fmt.Errorf("OpenClaw auth requires a readable Codex auth file at %s or OPENAI_API_KEY", opts.OpenClawCodexAuthPath)
	case "codex":
		path, err := validateCodexAuthPath(opts.OpenClawCodexAuthPath)
		if err != nil {
			return openClawAuthConfig{}, err
		}
		return openClawAuthConfig{Mode: "codex", CodexAuthPath: path}, nil
	case "api-key":
		if strings.TrimSpace(os.Getenv("OPENAI_API_KEY")) == "" {
			return openClawAuthConfig{}, fmt.Errorf("OPENAI_API_KEY is required when --openclaw-auth=api-key")
		}
		return openClawAuthConfig{Mode: "api-key"}, nil
	default:
		return openClawAuthConfig{}, fmt.Errorf("invalid OpenClaw auth mode %q; expected auto, codex, or api-key", mode)
	}
}

func validateCodexAuthPath(path string) (string, error) {
	path = expandUserPath(strings.TrimSpace(path))
	if path == "" {
		return "", fmt.Errorf("Codex auth path is required")
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		return "", fmt.Errorf("read Codex auth file %s: %w", path, err)
	}
	var decoded map[string]any
	if err := json.Unmarshal(raw, &decoded); err != nil {
		return "", fmt.Errorf("decode Codex auth file %s: %w", path, err)
	}
	if len(decoded) == 0 {
		return "", fmt.Errorf("Codex auth file %s is empty", path)
	}
	return path, nil
}

func expandUserPath(path string) string {
	if path == "~" {
		home, err := os.UserHomeDir()
		if err == nil && strings.TrimSpace(home) != "" {
			return home
		}
		return path
	}
	if strings.HasPrefix(path, "~/") {
		home, err := os.UserHomeDir()
		if err == nil && strings.TrimSpace(home) != "" {
			return filepath.Join(home, path[2:])
		}
	}
	return path
}

func resolveListenAddr(value string, defaultHost string) (string, error) {
	value = strings.TrimSpace(value)
	if value != "" && !strings.HasSuffix(value, ":0") {
		return value, nil
	}
	host := defaultHost
	if value != "" {
		parsedHost, _, err := net.SplitHostPort(value)
		if err == nil && parsedHost != "" {
			host = parsedHost
		}
	}
	probeHost := host
	if probeHost == "0.0.0.0" || probeHost == "::" || probeHost == "" {
		probeHost = "127.0.0.1"
	}
	ln, err := net.Listen("tcp", net.JoinHostPort(probeHost, "0"))
	if err != nil {
		return "", err
	}
	_, port, err := net.SplitHostPort(ln.Addr().String())
	closeErr := ln.Close()
	if err != nil {
		return "", err
	}
	if closeErr != nil {
		return "", closeErr
	}
	return net.JoinHostPort(host, port), nil
}

func publicMCPBase(value string, listenAddr string) (string, error) {
	value = strings.TrimRight(strings.TrimSpace(value), "/")
	if value == "" {
		return "http://" + listenAddr, nil
	}
	parsed, err := url.Parse(value)
	if err != nil {
		return "", fmt.Errorf("parse MCP public base URL: %w", err)
	}
	if parsed.Scheme != "http" && parsed.Scheme != "https" {
		return "", fmt.Errorf("MCP public base URL must use http or https")
	}
	if strings.TrimSpace(parsed.Host) == "" {
		return "", fmt.Errorf("MCP public base URL requires a host")
	}
	if parsed.RawQuery != "" || parsed.Fragment != "" {
		return "", fmt.Errorf("MCP public base URL must not contain a query or fragment")
	}
	return value, nil
}

func validateManualLawyerAddress(publicBase string, listenAddr string) error {
	if strings.TrimSpace(publicBase) != "" {
		return nil
	}
	host, _, err := net.SplitHostPort(listenAddr)
	if err != nil {
		return fmt.Errorf("parse MCP listen address %q: %w", listenAddr, err)
	}
	switch host {
	case "", "0.0.0.0", "::":
		return fmt.Errorf("manual lawyer mode requires --mcp-public-base-url when --mcp-listen uses a wildcard host")
	default:
		return nil
	}
}

func appendMCPAssignment(baseURL string, caseID string, key string, value string) string {
	baseURL = strings.TrimRight(baseURL, "/")
	return baseURL + "/mcp?case_id=" + url.QueryEscape(caseID) + "&" + key + "=" + url.QueryEscape(value)
}

func waitForHealth(ctx context.Context, rawURL string, timeout time.Duration) error {
	deadlineCtx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	ticker := time.NewTicker(50 * time.Millisecond)
	defer ticker.Stop()
	for {
		req, err := http.NewRequestWithContext(deadlineCtx, http.MethodGet, rawURL, nil)
		if err != nil {
			return err
		}
		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			closeErr := resp.Body.Close()
			if closeErr != nil {
				return closeErr
			}
			if resp.StatusCode == http.StatusNoContent {
				return nil
			}
		}
		select {
		case <-deadlineCtx.Done():
			return fmt.Errorf("%s did not become healthy within %s", rawURL, timeout)
		case <-ticker.C:
		}
	}
}

func (s *runState) waitForCaseAPI(ctx context.Context, caseDone <-chan caseOutcome) error {
	healthDone := make(chan error, 1)
	go func() {
		healthDone <- waitForHealth(ctx, s.caseBase+"/health", defaultCaseAPIStartupWait)
	}()
	select {
	case err := <-healthDone:
		return err
	case outcome := <-caseDone:
		if outcome.err != nil {
			return outcome.err
		}
		return fmt.Errorf("case finished before case API became healthy")
	case <-ctx.Done():
		return ctx.Err()
	}
}

func (s *runState) waitForMCP(ctx context.Context, caseDone <-chan caseOutcome, mcpDone <-chan error) error {
	healthDone := make(chan error, 1)
	go func() {
		healthDone <- waitForHealth(ctx, s.mcpBase+"/health", defaultMCPStartupWait)
	}()
	select {
	case err := <-healthDone:
		return err
	case outcome := <-caseDone:
		if outcome.err != nil {
			return outcome.err
		}
		return fmt.Errorf("case finished before MCP became healthy")
	case err := <-mcpDone:
		if err == nil {
			return fmt.Errorf("MCP server exited before health check")
		}
		return fmt.Errorf("MCP server failed before health check: %w", err)
	case <-ctx.Done():
		return ctx.Err()
	}
}

func (s *runState) startOpenClawLawyer(ctx context.Context, role string, mcpPort string) error {
	server := "aard-" + s.opts.CaseID + "-" + role
	mcpURL := appendMCPAssignment("http://"+net.JoinHostPort(s.opts.DockerMCPHost, mcpPort), s.opts.CaseID, "role_id", role)
	instructions, err := renderInstructions(s.opts.LawyerInstructionsPath, instructionData{
		CaseID:    s.opts.CaseID,
		RoleID:    role,
		MCPServer: server,
		MCPURL:    mcpURL,
	})
	if err != nil {
		return err
	}
	mcpJSON, err := json.Marshal(map[string]any{
		"url":       mcpURL,
		"transport": "streamable-http",
		"headers":   map[string]string{"Authorization": "Bearer " + s.token},
	})
	if err != nil {
		return err
	}
	name := containerName("aard-" + s.opts.CaseID + "-" + role)
	authArgs, commandPrefix, err := s.openClawAuthArgs(role)
	if err != nil {
		return err
	}
	configPrefix, err := openClawConfigPatchCommand(effectiveLawyerTurnTimeoutSeconds(s.opts))
	if err != nil {
		return err
	}
	args := openClawDockerRunArgs(s.opts, name)
	args = append(args, authArgs...)
	args = append(args,
		"-e", "AARD_MCP_NAME="+server,
		"-e", "AARD_MCP_JSON="+string(mcpJSON),
		"-e", "AARD_SESSION_KEY=agent:aard:"+s.opts.CaseID+":"+role,
		"-e", "AARD_ASSIGNMENT="+instructions,
		"-e", "AARD_PRINCIPAL="+role,
		s.opts.OpenClawImage,
		"sh", "-lc",
		fmt.Sprintf("set -eu\n%s%sopenclaw mcp set \"$AARD_MCP_NAME\" \"$AARD_MCP_JSON\"\nexec openclaw agent --local --model %q --thinking %q --timeout %d --session-key \"$AARD_SESSION_KEY\" --message \"$AARD_ASSIGNMENT\" --json", commandPrefix, configPrefix, s.opts.OpenClawModel, s.opts.OpenClawThinking, s.opts.OpenClawTimeoutSeconds),
	)
	proc, err := s.startProcess(ctx, "openclaw-"+role, "docker", s.opts.DockerCommand, args, name, nil)
	if err != nil {
		return err
	}
	s.mu.Lock()
	s.processes = append(s.processes, proc)
	s.mu.Unlock()
	return nil
}

func openClawDockerRunArgs(opts Options, name string) []string {
	args := []string{"run", "--rm", "--name", name}
	if opts.OpenClawNetwork != "" {
		args = append(args, "--network", opts.OpenClawNetwork)
	}
	if opts.OpenClawNetwork != "host" {
		args = append(args, "--add-host=host.docker.internal:host-gateway")
	}
	return args
}

func (s *runState) writeRemoteLawyerSkill(role string) error {
	server := "aard-" + s.opts.CaseID + "-" + role
	mcpURL := appendMCPAssignment(s.mcpPublicBase, s.opts.CaseID, "role_id", role)
	mcpJSON, err := json.Marshal(map[string]any{
		"url":       mcpURL,
		"transport": "streamable-http",
		"headers":   map[string]string{"Authorization": "Bearer " + s.token},
	})
	if err != nil {
		return err
	}
	instructions, err := renderInstructions(s.opts.RemoteLawyerSkillPath, instructionData{
		CaseID:    s.opts.CaseID,
		RoleID:    role,
		MCPServer: server,
		MCPURL:    mcpURL,
		MCPJSON:   string(mcpJSON),
	})
	if err != nil {
		return err
	}
	name := "openclaw-" + role + "-lawyer-skill.md"
	path := filepath.Join(s.opts.OutputDir, name)
	if err := os.WriteFile(path, []byte(instructions), 0o600); err != nil {
		return fmt.Errorf("write remote lawyer skill %s: %w", path, err)
	}
	if s.opts.Log != nil {
		fmt.Fprintf(s.opts.Log, "remote %s lawyer skill written to %s\n", role, path)
	}
	return nil
}

func effectiveLawyerTurnTimeoutSeconds(opts Options) int {
	if opts.LawyerTimeoutSeconds > 0 {
		return opts.LawyerTimeoutSeconds
	}
	return DefaultRunLawyerTimeoutSeconds
}

func openClawConfigPatchCommand(lawyerTimeoutSeconds int) (string, error) {
	if lawyerTimeoutSeconds <= 0 {
		return "", fmt.Errorf("lawyer timeout must be positive")
	}
	timeoutMS := lawyerTimeoutSeconds * 1000
	patch := map[string]any{
		"plugins": map[string]any{
			"entries": map[string]any{
				"codex": map[string]any{
					"enabled": true,
					"config": map[string]any{
						"appServer": map[string]any{
							"turnCompletionIdleTimeoutMs":                 timeoutMS,
							"postToolRawAssistantCompletionIdleTimeoutMs": timeoutMS,
						},
					},
				},
			},
		},
	}
	raw, err := json.Marshal(patch)
	if err != nil {
		return "", fmt.Errorf("marshal OpenClaw config patch: %w", err)
	}
	return fmt.Sprintf("cat > /tmp/aard-openclaw-config.json <<'JSON'\n%s\nJSON\nopenclaw config patch --file /tmp/aard-openclaw-config.json\n", raw), nil
}

func (s *runState) waitOpenClawStartDelay(ctx context.Context) error {
	delay := time.Duration(s.opts.OpenClawStartDelaySeconds) * time.Second
	if delay <= 0 {
		return nil
	}
	timer := time.NewTimer(delay)
	defer timer.Stop()
	select {
	case <-timer.C:
		return nil
	case err := <-s.agentErrs:
		return err
	case <-ctx.Done():
		return ctx.Err()
	}
}

func (s *runState) openClawAuthArgs(role string) ([]string, string, error) {
	switch s.openClawAuth.Mode {
	case "api-key":
		return []string{"-e", "OPENAI_API_KEY"}, "", nil
	case "codex":
		home, err := s.stageOpenClawCodexAuth(role)
		if err != nil {
			return nil, "", err
		}
		args := []string{
			"-v", home + ":" + openClawCodexContainerHome + ":rw",
			"-e", "CODEX_HOME=" + openClawCodexContainerHome,
		}
		return args, openClawCodexAuthCommand(), nil
	default:
		return nil, "", fmt.Errorf("unsupported OpenClaw auth mode %q", s.openClawAuth.Mode)
	}
}

func openClawCodexAuthCommand() string {
	return `unset OPENAI_API_KEY
codex_token="$(node -e 'const fs=require("fs"); const home=process.env.CODEX_HOME; if (!home) process.exit(2); const d=JSON.parse(fs.readFileSync(home + "/auth.json", "utf8")); const t=d.tokens && d.tokens.access_token; if (!t) process.exit(3); process.stdout.write(t);')"
printf '%s\n' "$codex_token" | openclaw models auth paste-token --provider openai --profile-id openai:codex >/dev/null
unset codex_token
`
}

func (s *runState) stageOpenClawCodexAuth(role string) (string, error) {
	home, err := outputSubdir(s.opts.OutputDir, "openclaw-"+role+"-codex")
	if err != nil {
		return "", fmt.Errorf("resolve OpenClaw Codex home path: %w", err)
	}
	if err := os.MkdirAll(home, 0o777); err != nil {
		return "", fmt.Errorf("create OpenClaw Codex home: %w", err)
	}
	if err := os.Chmod(home, 0o777); err != nil {
		return "", fmt.Errorf("chmod OpenClaw Codex home: %w", err)
	}
	raw, err := os.ReadFile(s.openClawAuth.CodexAuthPath)
	if err != nil {
		return "", fmt.Errorf("read Codex auth file %s: %w", s.openClawAuth.CodexAuthPath, err)
	}
	target := filepath.Join(home, "auth.json")
	tmp := target + ".tmp"
	if err := os.WriteFile(tmp, raw, 0o666); err != nil {
		return "", fmt.Errorf("write staged Codex auth file: %w", err)
	}
	if err := os.Rename(tmp, target); err != nil {
		return "", errors.Join(fmt.Errorf("install staged Codex auth file: %w", err), os.Remove(tmp))
	}
	if err := os.Chmod(target, 0o666); err != nil {
		return "", fmt.Errorf("chmod staged Codex auth file: %w", err)
	}
	s.mu.Lock()
	s.secretDirs = append(s.secretDirs, home)
	s.mu.Unlock()
	return home, nil
}

func (s *runState) waitForCouncilRoster(ctx context.Context, caseDone <-chan caseOutcome, mcpDone <-chan error) ([]councilRosterEntry, error) {
	rosterDone := make(chan rosterOutcome, 1)
	go func() {
		roster, err := s.pollCouncilRoster(ctx)
		rosterDone <- rosterOutcome{roster: roster, err: err}
	}()
	select {
	case outcome := <-rosterDone:
		return outcome.roster, outcome.err
	case outcome := <-caseDone:
		if outcome.err != nil {
			return nil, outcome.err
		}
		return nil, fmt.Errorf("case finished before council roster became available")
	case err := <-mcpDone:
		if err == nil {
			return nil, fmt.Errorf("MCP server exited before council roster became available")
		}
		return nil, fmt.Errorf("MCP server failed before council roster became available: %w", err)
	case err := <-s.agentErrs:
		return nil, err
	case <-ctx.Done():
		return nil, ctx.Err()
	}
}

func (s *runState) pollCouncilRoster(ctx context.Context) ([]councilRosterEntry, error) {
	deadlineCtx, cancel := context.WithTimeout(ctx, defaultCouncilRosterWait)
	defer cancel()
	ticker := time.NewTicker(time.Second)
	defer ticker.Stop()
	statusURL := s.caseBase + "/lawyerapi/v1/status?case_id=" + url.QueryEscape(s.opts.CaseID) + "&role_id=observer"
	for {
		req, err := http.NewRequestWithContext(deadlineCtx, http.MethodGet, statusURL, nil)
		if err != nil {
			return nil, err
		}
		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			body, readErr := io.ReadAll(resp.Body)
			closeErr := resp.Body.Close()
			if readErr != nil {
				return nil, readErr
			}
			if closeErr != nil {
				return nil, closeErr
			}
			if resp.StatusCode >= 200 && resp.StatusCode < 300 {
				var status councilRosterResponse
				dec := json.NewDecoder(bytes.NewReader(body))
				dec.UseNumber()
				if err := dec.Decode(&status); err != nil {
					return nil, err
				}
				if len(status.CouncilRoster) > 0 {
					if err := os.WriteFile(filepath.Join(s.logDir, "observer-status.json"), body, 0o644); err != nil {
						return nil, err
					}
					return status.CouncilRoster, nil
				}
			}
		}
		select {
		case <-deadlineCtx.Done():
			return nil, fmt.Errorf("council roster did not become available within %s", defaultCouncilRosterWait)
		case <-ticker.C:
		}
	}
}

func (s *runState) startReadyCouncil(ctx context.Context, roster []councilRosterEntry, mcpPort string) error {
	for _, entry := range roster {
		status, err := s.councilStatus(ctx, entry.MemberID)
		if err != nil {
			return err
		}
		if strings.TrimSpace(status.Status) != "ready" || status.Turn == nil {
			continue
		}
		if strings.TrimSpace(status.Turn.MemberID) != strings.TrimSpace(entry.MemberID) {
			continue
		}
		opportunityID := strings.TrimSpace(status.Turn.OpportunityID)
		if opportunityID == "" {
			return fmt.Errorf("council status for %s is ready without opportunity_id", entry.MemberID)
		}
		s.mu.Lock()
		started := s.councilStarts[opportunityID]
		if !started {
			s.councilStarts[opportunityID] = true
		}
		s.mu.Unlock()
		if started {
			continue
		}
		if err := s.startPiCouncil(ctx, entry, mcpPort, opportunityID); err != nil {
			return err
		}
	}
	return nil
}

func (s *runState) councilStatus(ctx context.Context, memberID string) (councilStatusResponse, error) {
	statusURL := s.caseBase + "/councilapi/v1/get?case_id=" + url.QueryEscape(s.opts.CaseID) + "&member_id=" + url.QueryEscape(memberID)
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, statusURL, nil)
	if err != nil {
		return councilStatusResponse{}, err
	}
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return councilStatusResponse{}, err
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return councilStatusResponse{}, err
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		return councilStatusResponse{}, fmt.Errorf("council status for %s returned HTTP %d: %s", memberID, resp.StatusCode, strings.TrimSpace(string(body)))
	}
	var status councilStatusResponse
	dec := json.NewDecoder(bytes.NewReader(body))
	dec.UseNumber()
	if err := dec.Decode(&status); err != nil {
		return councilStatusResponse{}, err
	}
	return status, nil
}

func (s *runState) startPiCouncil(ctx context.Context, entry councilRosterEntry, mcpPort string, opportunityID string) error {
	if strings.TrimSpace(entry.MemberID) == "" {
		return fmt.Errorf("council roster entry has empty member_id")
	}
	opportunityID = strings.TrimSpace(opportunityID)
	if opportunityID == "" {
		return fmt.Errorf("council opportunity id is required for %s", entry.MemberID)
	}
	server := defaultPiMCPServer
	mcpURL := appendMCPAssignment("http://"+net.JoinHostPort(s.opts.PodmanMCPHost, mcpPort), s.opts.CaseID, "member_id", entry.MemberID)
	instructions, err := renderInstructions(s.opts.CouncilInstructionsPath, instructionData{
		CaseID:    s.opts.CaseID,
		MemberID:  entry.MemberID,
		MCPServer: server,
		MCPURL:    mcpURL,
	})
	if err != nil {
		return err
	}
	home, err := outputSubdir(s.opts.OutputDir, "pi-"+entry.MemberID)
	if err != nil {
		return fmt.Errorf("resolve Pi home path: %w", err)
	}
	if err := os.MkdirAll(home, 0o755); err != nil {
		return fmt.Errorf("create Pi home: %w", err)
	}
	model, err := writePiConfig(home, entry, server, mcpURL, s.token)
	if err != nil {
		return err
	}
	args := []string{
		"run", "--rm",
		"--network", "host",
		"--user", "0:0",
		"-e", "HOME=/home/user",
		"-e", "TMPDIR=/home/user",
		"-e", "PI_CODING_AGENT_DIR=/home/user/.pi/agent",
		"-e", "OPENROUTER_API_KEY",
		"-e", "NODE_OPTIONS",
		"-v", home + ":/home/user",
		"-w", "/home/user",
		s.opts.PiImage,
		"--provider", "openrouter",
		"--model", model,
		"-e", s.opts.PiMCPAdapter,
		"--mode", "json",
		"-p", instructions,
	}
	proc, err := s.startProcess(ctx, "pi-"+entry.MemberID, "podman", s.opts.PodmanCommand, args, "", &councilProcessTarget{
		memberID:      entry.MemberID,
		opportunityID: opportunityID,
	})
	if err != nil {
		return err
	}
	s.mu.Lock()
	s.processes = append(s.processes, proc)
	s.mu.Unlock()
	return nil
}

func outputSubdir(outputDir string, name string) (string, error) {
	return filepath.Abs(filepath.Join(outputDir, name))
}

func renderInstructions(path string, data instructionData) (string, error) {
	raw, ok := embeddedInstruction(path)
	if !ok {
		fileRaw, err := os.ReadFile(path)
		if err != nil {
			return "", fmt.Errorf("read instruction template %s: %w", path, err)
		}
		raw = string(fileRaw)
	}
	tmpl, err := template.New(filepath.Base(path)).Option("missingkey=error").Parse(raw)
	if err != nil {
		return "", fmt.Errorf("parse instruction template %s: %w", path, err)
	}
	var out bytes.Buffer
	if err := tmpl.Execute(&out, data); err != nil {
		return "", fmt.Errorf("render instruction template %s: %w", path, err)
	}
	return out.String(), nil
}

func embeddedInstruction(path string) (string, bool) {
	switch strings.TrimSpace(path) {
	case defaultLawyerInstructions:
		return embeddedLawyerInstructions, true
	case defaultRemoteLawyerSkill:
		return embeddedRemoteLawyerSkill, true
	case defaultCouncilInstructions:
		return embeddedCouncilInstructions, true
	default:
		return "", false
	}
}

func writePiConfig(home string, entry councilRosterEntry, server string, mcpURL string, token string) (string, error) {
	spec, err := piRequestSpec(entry)
	if err != nil {
		return "", err
	}
	if spec.Endpoint != "openrouter" {
		return "", fmt.Errorf("Pi council requires openrouter endpoint for %s; got %s", entry.MemberID, spec.Endpoint)
	}
	unsupported := []string{}
	if spec.Request.Temperature != nil {
		unsupported = append(unsupported, "temperature")
	}
	if spec.Request.TopP != nil {
		unsupported = append(unsupported, "top_p")
	}
	if len(unsupported) > 0 {
		return "", fmt.Errorf("Pi council cannot enforce request fields for %s: %s", entry.MemberID, strings.Join(unsupported, " "))
	}
	model := spec.UpstreamModel()
	settingsDir := filepath.Join(home, ".pi", "agent")
	if err := os.MkdirAll(settingsDir, 0o755); err != nil {
		return "", fmt.Errorf("create Pi settings dir: %w", err)
	}
	settings := map[string]any{
		"defaultProvider": "openrouter",
		"defaultModel":    model,
		"quietStartup":    true,
	}
	if err := writeJSONFile(filepath.Join(settingsDir, "settings.json"), settings); err != nil {
		return "", err
	}
	modelEntry := map[string]any{
		"id":   model,
		"name": "AARD " + entry.MemberID + " " + model,
	}
	spec = spec.WithFallbackMaxOutputTokens(DefaultCouncilMaxOutputTokens)
	if maxTokens := spec.MaxOutputTokens(); maxTokens != nil {
		modelEntry["maxTokens"] = *maxTokens
	}
	if routing := spec.ProviderBody(); len(routing) > 0 {
		modelEntry["compat"] = map[string]any{"openRouterRouting": routing}
	}
	models := map[string]any{
		"providers": map[string]any{
			"openrouter": map[string]any{
				"baseUrl": "https://openrouter.ai/api/v1",
				"apiKey":  "$OPENROUTER_API_KEY",
				"api":     "openai-completions",
				"models":  []map[string]any{modelEntry},
			},
		},
	}
	if err := writeJSONFile(filepath.Join(settingsDir, "models.json"), models); err != nil {
		return "", err
	}
	mcpConfig := map[string]any{
		"mcpServers": map[string]any{
			server: map[string]any{
				"url":       mcpURL,
				"transport": "streamable-http",
				"lifecycle": "keep-alive",
				"headers":   map[string]string{"Authorization": "Bearer " + token},
			},
		},
	}
	if err := writeJSONFile(filepath.Join(home, ".mcp.json"), mcpConfig); err != nil {
		return "", err
	}
	return model, nil
}

func piRequestSpec(entry councilRosterEntry) (modelrequest.Spec, error) {
	if entry.RequestSpec != nil {
		return *entry.RequestSpec, nil
	}
	return modelrequest.Spec{}, fmt.Errorf("council roster entry %s has no request_spec; JSONL council pool records are required", entry.MemberID)
}

func writeJSONFile(path string, value any) error {
	raw, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return fmt.Errorf("marshal %s: %w", path, err)
	}
	raw = append(raw, '\n')
	if err := os.WriteFile(path, raw, 0o644); err != nil {
		return fmt.Errorf("write %s: %w", path, err)
	}
	return nil
}

func (s *runState) startProcess(ctx context.Context, name string, kind string, command string, args []string, stopName string, councilTarget *councilProcessTarget) (*processRecord, error) {
	stdoutPath := filepath.Join(s.logDir, name+".stdout")
	stderrPath := filepath.Join(s.logDir, name+".stderr")
	stdout, err := os.Create(stdoutPath)
	if err != nil {
		return nil, fmt.Errorf("create %s stdout log: %w", name, err)
	}
	stderr, err := os.Create(stderrPath)
	if err != nil {
		_ = stdout.Close()
		return nil, fmt.Errorf("create %s stderr log: %w", name, err)
	}
	stdoutWriter := io.Writer(stdout)
	var stdoutFilter *piTailLogWriter
	if councilTarget != nil && strings.HasPrefix(name, "pi-") {
		stdoutFilter = newPiTailLogWriter(stdout)
		stdoutWriter = stdoutFilter
	}
	stdoutCounter := newProcessOutputCounter(stdoutWriter)
	closeStdout := func() error {
		if stdoutFilter == nil {
			return stdout.Close()
		}
		return errors.Join(stdoutFilter.Flush(), stdout.Close())
	}
	cmd := exec.CommandContext(ctx, command, args...)
	cmd.Stdout = stdoutCounter
	cmd.Stderr = stderr
	if err := cmd.Start(); err != nil {
		return nil, errors.Join(fmt.Errorf("start %s: %w", name, err), closeStdout(), stderr.Close())
	}
	if err := os.WriteFile(filepath.Join(s.opts.OutputDir, name+".pid"), []byte(fmt.Sprintf("%d\n", cmd.Process.Pid)), 0o644); err != nil {
		return nil, errors.Join(err, cmd.Process.Kill(), cmd.Wait(), closeStdout(), stderr.Close())
	}
	record := &processRecord{
		name:       name,
		kind:       kind,
		command:    cmd,
		done:       make(chan error, 1),
		stopName:   stopName,
		stdoutPath: stdoutPath,
		stderrPath: stderrPath,
		finished:   make(chan struct{}),

		stdoutCounter: stdoutCounter,
	}
	go func() {
		err := cmd.Wait()
		closeOut := closeStdout()
		closeErr := stderr.Close()
		waitErr := errors.Join(err, closeOut, closeErr)
		record.markExited()
		record.done <- waitErr
		if ctx.Err() != nil {
			return
		}
		if councilTarget != nil {
			if err := s.handleCouncilProcessExit(ctx, record, *councilTarget, waitErr); err != nil {
				s.agentErrs <- err
			}
			return
		}
		if waitErr != nil {
			s.agentErrs <- fmt.Errorf("%s process %s failed: %w", kind, name, waitErr)
			return
		}
		s.agentErrs <- fmt.Errorf("%s process %s exited before case completion", kind, name)
	}()
	if councilTarget != nil {
		go s.monitorCouncilOutput(ctx, record, *councilTarget, defaultCouncilOutputCheck)
	}
	return record, nil
}

func (p *processRecord) markExited() {
	p.mu.Lock()
	p.exited = true
	close(p.finished)
	p.mu.Unlock()
}

func (p *processRecord) isExited() bool {
	p.mu.Lock()
	defer p.mu.Unlock()
	return p.exited
}

func (p *processRecord) setForcedFailure(reason string, message string, details map[string]any) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.forcedReason != "" {
		return
	}
	p.forcedReason = strings.TrimSpace(reason)
	p.forcedMessage = strings.TrimSpace(message)
	p.forcedDetails = cloneLocalMap(details)
}

func (p *processRecord) forcedFailure() (string, string, map[string]any) {
	p.mu.Lock()
	defer p.mu.Unlock()
	return p.forcedReason, p.forcedMessage, cloneLocalMap(p.forcedDetails)
}

func (s *runState) monitorCouncilOutput(ctx context.Context, proc *processRecord, target councilProcessTarget, interval time.Duration) {
	if s.opts.CouncilOutputLimitBytes <= 0 {
		return
	}
	ticker := time.NewTicker(interval)
	defer ticker.Stop()
	for {
		select {
		case <-ticker.C:
			if proc.isExited() {
				return
			}
			size, err := councilProcessOutputSize(proc)
			if err != nil {
				s.agentErrs <- fmt.Errorf("check council output for %s: %w", proc.name, err)
				return
			}
			if size.Total <= s.opts.CouncilOutputLimitBytes {
				continue
			}
			message, details := councilOutputLimitFailure(proc.name, target, size, s.opts.CouncilOutputLimitBytes)
			proc.setForcedFailure(councilFailureOutputLimit, message, details)
			if err := proc.command.Process.Kill(); err != nil {
				if proc.isExited() {
					return
				}
				s.agentErrs <- fmt.Errorf("kill %s after council output limit exceeded: %w", proc.name, err)
			}
			return
		case <-proc.finished:
			return
		case <-ctx.Done():
			return
		}
	}
}

func councilProcessOutputSize(proc *processRecord) (processOutputSize, error) {
	stdoutInfo, err := os.Stat(proc.stdoutPath)
	if err != nil {
		return processOutputSize{}, fmt.Errorf("stat stdout log %s: %w", proc.stdoutPath, err)
	}
	stderrInfo, err := os.Stat(proc.stderrPath)
	if err != nil {
		return processOutputSize{}, fmt.Errorf("stat stderr log %s: %w", proc.stderrPath, err)
	}
	stdoutBytes := stdoutInfo.Size()
	stderrBytes := stderrInfo.Size()
	if proc.stdoutCounter != nil {
		stdoutBytes = proc.stdoutCounter.Size()
	}
	if stdoutBytes > int64(^uint64(0)>>1)-stderrBytes {
		return processOutputSize{}, fmt.Errorf("process output size overflow for %s", proc.name)
	}
	return processOutputSize{
		Stdout: stdoutBytes,
		Stderr: stderrBytes,
		Total:  stdoutBytes + stderrBytes,
	}, nil
}

func councilOutputLimitFailure(procName string, target councilProcessTarget, size processOutputSize, limit int64) (string, map[string]any) {
	message := fmt.Sprintf(
		"Council member %s agent process exceeded the output limit before completing opportunity %s: %d bytes written, limit %d bytes.",
		target.memberID,
		target.opportunityID,
		size.Total,
		limit,
	)
	return message, map[string]any{
		"process_name":       procName,
		"output_bytes":       size.Total,
		"stdout_bytes":       size.Stdout,
		"stderr_bytes":       size.Stderr,
		"output_limit_bytes": limit,
	}
}

func cloneLocalMap(in map[string]any) map[string]any {
	out := map[string]any{}
	for key, value := range in {
		if strings.TrimSpace(key) != "" && value != nil {
			out[key] = value
		}
	}
	return out
}

func (s *runState) handleCouncilProcessExit(ctx context.Context, proc *processRecord, target councilProcessTarget, waitErr error) error {
	status, err := s.councilStatus(ctx, target.memberID)
	if err != nil {
		return fmt.Errorf("check council status after %s exit: %w", proc.name, err)
	}
	if strings.TrimSpace(status.Status) != "ready" || status.Turn == nil {
		return nil
	}
	if strings.TrimSpace(status.Turn.MemberID) != strings.TrimSpace(target.memberID) {
		return nil
	}
	if strings.TrimSpace(status.Turn.OpportunityID) != strings.TrimSpace(target.opportunityID) {
		return nil
	}
	reason, forcedMessage, forcedDetails := proc.forcedFailure()
	if reason == "" {
		reason = councilFailureAgentExited
	}
	message := fmt.Sprintf("Council member %s agent process exited before completing opportunity %s.", target.memberID, target.opportunityID)
	details := map[string]any{
		"process_name": proc.name,
	}
	for key, value := range forcedDetails {
		details[key] = value
	}
	if forcedMessage != "" {
		message = forcedMessage
	}
	if waitErr != nil {
		if forcedMessage == "" {
			message = fmt.Sprintf("Council member %s agent process failed before completing opportunity %s: %s.", target.memberID, target.opportunityID, waitErr.Error())
		}
		details["process_error"] = waitErr.Error()
	}
	return s.reportCouncilFailure(ctx, target.memberID, target.opportunityID, reason, message, details)
}

func (s *runState) reportCouncilFailure(ctx context.Context, memberID string, opportunityID string, reason string, message string, details map[string]any) error {
	payload := map[string]any{
		"case_id":        s.opts.CaseID,
		"member_id":      memberID,
		"opportunity_id": opportunityID,
		"reason":         reason,
		"message":        message,
		"details":        details,
	}
	raw, err := json.Marshal(payload)
	if err != nil {
		return err
	}
	failURL := s.caseBase + "/councilapi/v1/fail"
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, failURL, bytes.NewReader(raw))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/json")
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return fmt.Errorf("report council failure for %s: %w", memberID, err)
	}
	defer resp.Body.Close()
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return err
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		return fmt.Errorf("report council failure for %s returned HTTP %d: %s", memberID, resp.StatusCode, strings.TrimSpace(string(body)))
	}
	var response map[string]any
	dec := json.NewDecoder(bytes.NewReader(body))
	dec.UseNumber()
	if err := dec.Decode(&response); err != nil {
		return fmt.Errorf("decode council failure response for %s: %w", memberID, err)
	}
	if ok, _ := response["ok"].(bool); !ok {
		message := ""
		if errObj, ok := response["error"].(map[string]any); ok {
			message = fmt.Sprint(errObj["message"])
		}
		if strings.TrimSpace(message) == "" {
			message = strings.TrimSpace(string(body))
		}
		return fmt.Errorf("report council failure for %s was rejected: %s", memberID, message)
	}
	return nil
}

func (s *runState) stopAgents() error {
	s.mu.Lock()
	processes := append([]*processRecord{}, s.processes...)
	s.mu.Unlock()
	var errs []error
	for _, proc := range processes {
		proc.mu.Lock()
		exited := proc.exited
		proc.mu.Unlock()
		if exited || proc.command.Process == nil {
			continue
		}
		if proc.kind == "docker" && strings.TrimSpace(proc.stopName) != "" {
			if err := exec.Command(s.opts.DockerCommand, "stop", proc.stopName).Run(); err != nil {
				errs = append(errs, fmt.Errorf("docker stop %s: %w", proc.stopName, err))
			}
			continue
		}
		if err := proc.command.Process.Kill(); err != nil {
			errs = append(errs, fmt.Errorf("kill %s: %w", proc.name, err))
		}
	}
	return errors.Join(errs...)
}

func (s *runState) cleanupSecrets() error {
	s.mu.Lock()
	dirs := append([]string{}, s.secretDirs...)
	s.mu.Unlock()
	var errs []error
	for _, dir := range dirs {
		if strings.TrimSpace(dir) == "" {
			continue
		}
		if err := os.RemoveAll(dir); err != nil {
			errs = append(errs, fmt.Errorf("remove staged secret directory %s: %w", dir, err))
		}
	}
	return errors.Join(errs...)
}

func writeRunSummary(outDir string, result Result, opts Options) error {
	return writeJSONFile(filepath.Join(outDir, "local-run.json"), map[string]any{
		"case_id":                             result.CaseID,
		"run_id":                              result.RunID,
		"status":                              result.Status,
		"answers":                             result.Answers,
		"error":                               result.Error,
		"failure":                             result.Failure,
		"auto_lawyers":                        opts.AutoLawyers,
		"mcp_public_base_url":                 opts.MCPPublicBaseURL,
		"openclaw_lawyer_start_delay_seconds": opts.OpenClawStartDelaySeconds,
		"council_output_limit_bytes":          opts.CouncilOutputLimitBytes,
	})
}

func randomToken() (string, error) {
	var buf [16]byte
	if _, err := rand.Read(buf[:]); err != nil {
		return "", err
	}
	return "aard-" + hex.EncodeToString(buf[:]), nil
}

func containerName(value string) string {
	value = strings.ToLower(value)
	var b strings.Builder
	for _, r := range value {
		if (r >= 'a' && r <= 'z') || (r >= '0' && r <= '9') || r == '-' || r == '_' || r == '.' {
			b.WriteRune(r)
		} else {
			b.WriteByte('-')
		}
	}
	out := strings.Trim(b.String(), "-_.")
	if len(out) > 63 {
		out = out[:63]
		out = strings.Trim(out, "-_.")
	}
	if out == "" {
		return "aard"
	}
	return out
}
