package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"adjudication/service/localrun/arbd"
)

type explicitFileList struct {
	values []string
}

func (f *explicitFileList) String() string {
	return strings.Join(f.values, ",")
}

func (f *explicitFileList) Set(value string) error {
	value = strings.TrimSpace(value)
	if value == "" {
		return fmt.Errorf("--file must not be empty")
	}
	f.values = append(f.values, value)
	return nil
}

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := runLocal(ctx, os.Args[1:], os.Stdout, os.Stderr); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

func runLocal(ctx context.Context, args []string, stdout io.Writer, stderr io.Writer) error {
	fs := flag.NewFlagSet("aard-run", flag.ContinueOnError)
	fs.SetOutput(stderr)
	var caseFiles explicitFileList
	coreCommand := fs.String("aard-bin", localrun.DefaultCoreCommand, "Core aard executable")
	coreWorkingDir := fs.String("aard-working-dir", "", "Optional working directory for the core aard process")
	complaintPath := fs.String("complaint", "", "Complaint markdown file")
	fs.Var(&caseFiles, "file", "Explicit case file path or glob. May be repeated")
	outDir := fs.String("out-dir", "", "Output directory")
	policyPath := fs.String("policy", "", "Policy JSON file")
	councilSize := fs.Int("council-size", 0, "Override policy council_size")
	judgmentStandard := fs.String("judgment-standard", "", "Override policy judgment_standard")
	attorneyInstructionsPath := fs.String("attorney-instructions", "", "Attorney instructions markdown file")
	promptDir := fs.String("prompt-dir", "", "Prompt directory override")
	attorneyCommonPrompt := fs.String("attorney-common-prompt", "", "Attorney common prompt file override")
	attorneyArgumentPrompt := fs.String("attorney-arguments-prompt", "", "Attorney arguments prompt file override")
	attorneyRebuttalPrompt := fs.String("attorney-rebuttals-prompt", "", "Attorney rebuttals prompt file override")
	commonRoot := fs.String("common-root", "", "Optional common directory passed to the core case")
	councilPool := fs.String("council-pool", "", "Council JSONL request-spec pool file")
	caseAPIAddr := fs.String("caseapi-addr", "127.0.0.1:0", "Private case API listen address")
	mcpListenAddr := fs.String("mcp-listen", "0.0.0.0:0", "MCP listen address")
	mcpBearerToken := fs.String("mcp-bearer-token", "", "MCP bearer token. Default: generated")
	councilTimeoutSeconds := fs.Int("council-timeout-seconds", localrun.DefaultRunCouncilTimeoutSeconds, "Council turn timeout seconds")
	lawyerTimeoutSeconds := fs.Int("lawyer-timeout-seconds", localrun.DefaultRunLawyerTimeoutSeconds, "Lawyer turn timeout seconds")
	maxResponseBytes := fs.Int("max-response-bytes", 0, "Override runtime max parsed response bytes")
	invalidAttemptLimit := fs.Int("invalid-attempt-limit", 0, "Override runtime invalid-attempt limit")
	enginePath := fs.String("engine", "", "Optional Lean engine binary passed to the core case")
	runID := fs.String("run-id", "", "Run ID override")
	caseID := fs.String("case-id", "", "Case ID")
	lawyerInstructions := fs.String("lawyer-instructions", localrun.DefaultLawyerInstructionsPath(), "OpenClaw lawyer instruction template")
	remoteLawyerSkill := fs.String("remote-lawyer-skill", localrun.DefaultRemoteLawyerSkillPath(), "OpenClaw remote lawyer skill template")
	councilInstructions := fs.String("council-instructions", localrun.DefaultCouncilInstructionsPath(), "Pi council instruction template")
	autoLawyers := fs.String("auto-lawyers", localrun.DefaultAutoLawyers, "OpenClaw lawyers started by aard-run: both, plaintiff, or defendant")
	mcpPublicBaseURL := fs.String("mcp-public-base-url", "", "Public MCP base URL for remote lawyers, for example http://aard-host.example:8001")
	dockerCommand := fs.String("docker", localrun.DefaultDockerCommand, "Docker command")
	podmanCommand := fs.String("podman", localrun.DefaultPodmanCommand, "Podman command")
	openClawImage := fs.String("openclaw-image", "", "OpenClaw container image")
	openClawModel := fs.String("openclaw-model", "", "OpenClaw model")
	openClawThinking := fs.String("openclaw-thinking", "", "OpenClaw thinking setting")
	openClawTimeoutSeconds := fs.Int("openclaw-timeout-seconds", 0, "OpenClaw agent timeout seconds")
	openClawAuth := fs.String("openclaw-auth", "", "OpenClaw auth mode: auto, codex, or api-key")
	openClawCodexAuth := fs.String("openclaw-codex-auth", "", "Codex auth.json path for OpenClaw")
	openClawStartDelaySeconds := fs.Int("openclaw-lawyer-start-delay-seconds", -1, "Delay between plaintiff and defendant OpenClaw startup; 0 disables")
	openClawNetwork := fs.String("openclaw-network", "", "Docker network for OpenClaw lawyer containers: host or empty")
	piImage := fs.String("pi-image", "", "Pi container image")
	piMCPAdapter := fs.String("pi-mcp-adapter", "", "Pi MCP adapter path or package source")
	councilOutputLimitBytes := fs.Int64("council-output-limit-bytes", localrun.DefaultCouncilOutputLimitBytes, "Total stdout plus stderr byte limit per Pi council agent")
	dockerMCPHost := fs.String("docker-mcp-host", "", "Host name used by Docker containers to reach MCP")
	podmanMCPHost := fs.String("podman-mcp-host", "", "Host name used by Podman containers to reach MCP")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aard-run [EXAMPLE] [options]\n\n")
		fs.PrintDefaults()
	}
	flagArgs, example, err := splitRunArgs(fs, args)
	if err != nil {
		return err
	}
	if err := fs.Parse(flagArgs); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	if fs.NArg() != 0 {
		return fmt.Errorf("aard-run accepts at most one example name")
	}
	if example != "" {
		if example == "" || strings.Contains(example, "/") || strings.HasPrefix(example, ".") || strings.Contains(example, "..") {
			return fmt.Errorf("invalid example name: %s", example)
		}
	}
	now := time.Now().UTC().Format("20060102150405")
	if example != "" {
		if strings.TrimSpace(*complaintPath) == "" {
			*complaintPath = filepath.Join("examples", example, "complaint.md")
		}
		if strings.TrimSpace(*caseID) == "" {
			*caseID = "arbd-" + example + "-" + now
		}
		if strings.TrimSpace(*outDir) == "" {
			*outDir = filepath.Join("out", example+"-openclaw-pi-"+now)
		}
	} else if strings.TrimSpace(*caseID) == "" {
		*caseID = "arbd-" + now
	}
	if strings.TrimSpace(*runID) == "" {
		*runID = "run-" + strings.TrimSpace(*caseID)
	}
	if strings.TrimSpace(*outDir) == "" {
		*outDir = filepath.Join("out", strings.TrimSpace(*caseID))
	}
	opts := localrun.Options{
		CoreCommand:                strings.TrimSpace(*coreCommand),
		CoreWorkingDir:             strings.TrimSpace(*coreWorkingDir),
		ComplaintPath:              *complaintPath,
		CaseFiles:                  caseFiles.values,
		OutputDir:                  *outDir,
		PolicyPath:                 *policyPath,
		CouncilSize:                *councilSize,
		JudgmentStandard:           *judgmentStandard,
		AttorneyInstructionsPath:   *attorneyInstructionsPath,
		PromptDir:                  *promptDir,
		AttorneyCommonPromptPath:   *attorneyCommonPrompt,
		AttorneyArgumentPromptPath: *attorneyArgumentPrompt,
		AttorneyRebuttalPromptPath: *attorneyRebuttalPrompt,
		CommonRoot:                 *commonRoot,
		CouncilPoolPath:            *councilPool,
		CaseAPIAddr:                *caseAPIAddr,
		MCPListenAddr:              *mcpListenAddr,
		MCPBearerToken:             *mcpBearerToken,
		CouncilTimeoutSeconds:      *councilTimeoutSeconds,
		LawyerTimeoutSeconds:       *lawyerTimeoutSeconds,
		MaxResponseBytes:           *maxResponseBytes,
		InvalidAttemptLimit:        *invalidAttemptLimit,
		EnginePath:                 *enginePath,
		RunID:                      *runID,
		CaseID:                     *caseID,
		LawyerInstructionsPath:     *lawyerInstructions,
		RemoteLawyerSkillPath:      *remoteLawyerSkill,
		CouncilInstructionsPath:    *councilInstructions,
		AutoLawyers:                *autoLawyers,
		MCPPublicBaseURL:           *mcpPublicBaseURL,
		DockerCommand:              *dockerCommand,
		PodmanCommand:              *podmanCommand,
		OpenClawImage:              *openClawImage,
		OpenClawModel:              *openClawModel,
		OpenClawThinking:           *openClawThinking,
		OpenClawTimeoutSeconds:     *openClawTimeoutSeconds,
		OpenClawAuth:               *openClawAuth,
		OpenClawCodexAuthPath:      *openClawCodexAuth,
		OpenClawStartDelaySeconds:  *openClawStartDelaySeconds,
		OpenClawNetwork:            *openClawNetwork,
		PiImage:                    *piImage,
		PiMCPAdapter:               *piMCPAdapter,
		CouncilOutputLimitBytes:    *councilOutputLimitBytes,
		DockerMCPHost:              *dockerMCPHost,
		PodmanMCPHost:              *podmanMCPHost,
		Log:                        stderr,
	}
	result, err := localrun.Run(ctx, opts)
	if err != nil {
		return err
	}
	raw, err := json.Marshal(result)
	if err != nil {
		return fmt.Errorf("marshal run result: %w", err)
	}
	if _, err := fmt.Fprintln(stdout, string(raw)); err != nil {
		return fmt.Errorf("write run result: %w", err)
	}
	return nil
}

func splitRunArgs(fs *flag.FlagSet, args []string) ([]string, string, error) {
	flagArgs := make([]string, 0, len(args))
	example := ""
	for i := 0; i < len(args); i++ {
		arg := args[i]
		if arg == "--" {
			for _, rest := range args[i+1:] {
				rest = strings.TrimSpace(rest)
				if rest == "" {
					continue
				}
				if example != "" {
					return nil, "", fmt.Errorf("aard-run accepts at most one example name")
				}
				example = rest
			}
			break
		}
		if strings.HasPrefix(arg, "-") && arg != "-" {
			flagArgs = append(flagArgs, arg)
			name, hasInlineValue := flagArgName(arg)
			if hasInlineValue {
				continue
			}
			if f := fs.Lookup(name); f != nil && !flagIsBool(f) {
				if i+1 < len(args) {
					i++
					flagArgs = append(flagArgs, args[i])
				}
			}
			continue
		}
		arg = strings.TrimSpace(arg)
		if arg == "" {
			continue
		}
		if example != "" {
			return nil, "", fmt.Errorf("aard-run accepts at most one example name")
		}
		example = arg
	}
	return flagArgs, example, nil
}

func flagArgName(arg string) (string, bool) {
	arg = strings.TrimLeft(arg, "-")
	if name, value, ok := strings.Cut(arg, "="); ok {
		_ = value
		return name, true
	}
	return arg, false
}

type boolFlag interface {
	IsBoolFlag() bool
}

func flagIsBool(f *flag.Flag) bool {
	bf, ok := f.Value.(boolFlag)
	return ok && bf.IsBoolFlag()
}
