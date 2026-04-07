package cli

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"time"

	"adjudication/arb/runtime/lean"
	"adjudication/arb/runtime/runner"
	"adjudication/arb/runtime/spec"
)

type caseRunSummary struct {
	Status       string `json:"status"`
	Result       string `json:"result,omitempty"`
	VotesFor     *int   `json:"votes_for,omitempty"`
	VotesAgainst *int   `json:"votes_against,omitempty"`
	RunID        string `json:"run_id,omitempty"`
	OutputDir    string `json:"out_dir,omitempty"`
	Error        string `json:"error,omitempty"`
}

func RunCase(args []string, stdout io.Writer, stderr io.Writer) error {
	var fs *flag.FlagSet
	fs = flag.NewFlagSet("case", flag.ContinueOnError)
	fs.SetOutput(stderr)
	var caseFiles explicitFileList
	complaintPath := fs.String("complaint", "", "Complaint markdown file")
	fs.Var(&caseFiles, "file", "Explicit case file path or glob. May be repeated. Overrides automatic complaint-directory scanning")
	outDir := fs.String("out-dir", "", "Output directory")
	policyPath := fs.String("policy", "", "Policy JSON file. Default: ./etc/policy.json when present")
	councilSize := fs.Int("council-size", 0, "Override policy council_size")
	evidenceStandard := fs.String("evidence-standard", "", "Override policy evidence_standard")
	commonRoot := fs.String("common-root", defaultCommonRoot(), "Path to the sibling shared common directory")
	legacyCommonRoot := fs.String("agentcourt-root", "", "Deprecated alias for --common-root")
	councilPool := fs.String("council-pool", "", "Council model/persona pool file. Default: <common-root>/data/personas/pool.csv")
	attorneyModel := fs.String("attorney-model", runner.DefaultAttorneyModel, "Attorney ACP model id. Use an explicit xproxy model such as openai://gpt-5 or openai://gpt-5?tools=search")
	plaintiffAttorneyModel := fs.String("plaintiff-attorney-model", "", "Plaintiff attorney model override")
	defendantAttorneyModel := fs.String("defendant-attorney-model", "", "Defendant attorney model override")
	acpCommand := fs.String("acp-command", "", "ACP command. Default: <common-root>/pi-container/acp-podman.sh")
	plaintiffACPCommand := fs.String("plaintiff-acp-command", "", "Plaintiff ACP command override")
	defendantACPCommand := fs.String("defendant-acp-command", "", "Defendant ACP command override")
	plaintiffACPEndpoint := fs.String("plaintiff-acp-endpoint", "", "Plaintiff ACP endpoint override. Supported transport: tcp://host:port")
	defendantACPEndpoint := fs.String("defendant-acp-endpoint", "", "Defendant ACP endpoint override. Supported transport: tcp://host:port")
	plaintiffACPSessionCwd := fs.String("plaintiff-acp-session-cwd", "", "Plaintiff ACP session cwd override")
	defendantACPSessionCwd := fs.String("defendant-acp-session-cwd", "", "Defendant ACP session cwd override")
	xproxyConfig := fs.String("xproxy-config", "", "xproxy config path. Default: <common-root>/etc/xproxy.json")
	xproxyPort := fs.Int("xproxy-port", 18459, "xproxy port")
	timeoutSeconds := fs.Int("timeout-seconds", 0, "Override runtime council LLM timeout in seconds")
	acpTimeoutSeconds := fs.Int("acp-timeout-seconds", 0, "Override runtime attorney ACP timeout in seconds")
	maxResponseBytes := fs.Int("max-response-bytes", 0, "Override runtime max parsed response bytes")
	invalidAttemptLimit := fs.Int("invalid-attempt-limit", 0, "Override runtime invalid-attempt limit")
	enginePath := fs.String("engine", defaultEnginePath(), "Lean engine binary")
	runID := fs.String("run-id", "", "Run ID override")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aar case --complaint FILE --out-dir DIR\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return reportCaseError(stdout, err)
	}
	if *complaintPath == "" || *outDir == "" {
		return reportCaseError(stdout, fmt.Errorf("--complaint and --out-dir are required"))
	}
	raw, err := os.ReadFile(*complaintPath)
	if err != nil {
		return reportCaseError(stdout, fmt.Errorf("read complaint: %w", err))
	}
	complaint, err := spec.ParseComplaintMarkdown(string(raw))
	if err != nil {
		return reportCaseError(stdout, err)
	}
	commonRootValue := strings.TrimSpace(*commonRoot)
	if strings.TrimSpace(*legacyCommonRoot) != "" {
		commonRootValue = strings.TrimSpace(*legacyCommonRoot)
	}
	commonRootResolved, err := filepath.Abs(commonRootValue)
	if err != nil {
		return reportCaseError(stdout, fmt.Errorf("resolve --common-root: %w", err))
	}
	policy, err := loadCasePolicy(*policyPath)
	if err != nil {
		return reportCaseError(stdout, err)
	}
	if *councilSize > 0 {
		policy.CouncilSize = *councilSize
	}
	if strings.TrimSpace(*evidenceStandard) != "" {
		policy.EvidenceStandard = strings.TrimSpace(*evidenceStandard)
	}
	if err := runner.ValidatePolicy(policy); err != nil {
		return reportCaseError(stdout, err)
	}
	runtimeLimits := runner.DefaultRuntimeLimits()
	if *timeoutSeconds > 0 {
		runtimeLimits.CouncilLLMTimeoutSeconds = *timeoutSeconds
	}
	if *acpTimeoutSeconds > 0 {
		runtimeLimits.AttorneyACPTimeoutSeconds = *acpTimeoutSeconds
	}
	if *maxResponseBytes > 0 {
		runtimeLimits.MaxResponseBytes = *maxResponseBytes
	}
	if *invalidAttemptLimit > 0 {
		runtimeLimits.InvalidAttemptLimit = *invalidAttemptLimit
	}
	if err := runner.ValidateRuntimeLimits(runtimeLimits); err != nil {
		return reportCaseError(stdout, err)
	}
	effectiveAttorneyModel := strings.TrimSpace(*attorneyModel)
	if _, err := runner.ParseAttorneyModelForCLI(effectiveAttorneyModel); err != nil {
		return reportCaseError(stdout, err)
	}
	if strings.TrimSpace(*plaintiffAttorneyModel) != "" {
		if _, err := runner.ParseAttorneyModelForCLI(strings.TrimSpace(*plaintiffAttorneyModel)); err != nil {
			return reportCaseError(stdout, err)
		}
	}
	if strings.TrimSpace(*defendantAttorneyModel) != "" {
		if _, err := runner.ParseAttorneyModelForCLI(strings.TrimSpace(*defendantAttorneyModel)); err != nil {
			return reportCaseError(stdout, err)
		}
	}
	if strings.TrimSpace(*plaintiffACPCommand) != "" && strings.TrimSpace(*plaintiffACPEndpoint) != "" {
		return reportCaseError(stdout, fmt.Errorf("plaintiff ACP config cannot set both --plaintiff-acp-command and --plaintiff-acp-endpoint"))
	}
	if strings.TrimSpace(*defendantACPCommand) != "" && strings.TrimSpace(*defendantACPEndpoint) != "" {
		return reportCaseError(stdout, fmt.Errorf("defendant ACP config cannot set both --defendant-acp-command and --defendant-acp-endpoint"))
	}
	councilPoolPath := strings.TrimSpace(*councilPool)
	if councilPoolPath == "" {
		councilPoolPath = filepath.Join(commonRootResolved, "data", "personas", "pool.csv")
	}
	xproxyConfigPath := strings.TrimSpace(*xproxyConfig)
	if xproxyConfigPath == "" {
		xproxyConfigPath = filepath.Join(commonRootResolved, "etc", "xproxy.json")
	}
	acpCommandPath := strings.TrimSpace(*acpCommand)
	if acpCommandPath == "" {
		acpCommandPath = filepath.Join(commonRootResolved, "pi-container", "acp-podman.sh")
	}
	effectiveRunID := strings.TrimSpace(*runID)
	if effectiveRunID == "" {
		effectiveRunID = fmt.Sprintf("run-%d", time.Now().UTC().UnixNano())
	}
	explicitCaseFiles, err := resolveExplicitCaseFiles(caseFiles.values)
	if err != nil {
		return reportCaseError(stdout, err)
	}
	cfg := runner.Config{
		RunID:           effectiveRunID,
		ComplaintPath:   *complaintPath,
		CaseFilePaths:   explicitCaseFiles,
		OutputDir:       *outDir,
		CommonRoot:      commonRootResolved,
		CouncilPoolPath: councilPoolPath,
		AttorneyModel:   effectiveAttorneyModel,
		PlaintiffAttorney: runner.AttorneyRoleConfig{
			Model:       strings.TrimSpace(*plaintiffAttorneyModel),
			ACPCommand:  strings.TrimSpace(*plaintiffACPCommand),
			ACPEndpoint: strings.TrimSpace(*plaintiffACPEndpoint),
			SessionCwd:  strings.TrimSpace(*plaintiffACPSessionCwd),
		},
		DefendantAttorney: runner.AttorneyRoleConfig{
			Model:       strings.TrimSpace(*defendantAttorneyModel),
			ACPCommand:  strings.TrimSpace(*defendantACPCommand),
			ACPEndpoint: strings.TrimSpace(*defendantACPEndpoint),
			SessionCwd:  strings.TrimSpace(*defendantACPSessionCwd),
		},
		Policy:           policy,
		Runtime:          runtimeLimits,
		XProxyConfigPath: xproxyConfigPath,
		XProxyPort:       *xproxyPort,
		ACPCommand:       acpCommandPath,
		Engine:           lean.New([]string{*enginePath}),
	}
	result, err := runner.Run(context.Background(), cfg, complaint)
	if err != nil {
		return reportCaseError(stdout, err)
	}
	if err := writeCaseSummary(stdout, buildCaseSuccessSummary(result, *outDir)); err != nil {
		return err
	}
	return nil
}

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

func resolveExplicitCaseFiles(patterns []string) ([]string, error) {
	if len(patterns) == 0 {
		return nil, nil
	}
	out := make([]string, 0, len(patterns))
	seen := map[string]struct{}{}
	for _, pattern := range patterns {
		matches, err := expandExplicitCaseFilePattern(pattern)
		if err != nil {
			return nil, err
		}
		for _, match := range matches {
			if err := validateExplicitCaseFilePath(match); err != nil {
				return nil, err
			}
			absMatch, err := filepath.Abs(match)
			if err != nil {
				return nil, fmt.Errorf("resolve case file %s: %w", match, err)
			}
			if _, ok := seen[absMatch]; ok {
				continue
			}
			seen[absMatch] = struct{}{}
			out = append(out, absMatch)
		}
	}
	return out, nil
}

func expandExplicitCaseFilePattern(pattern string) ([]string, error) {
	matches, err := filepath.Glob(pattern)
	if err != nil {
		return nil, fmt.Errorf("expand --file %q: %w", pattern, err)
	}
	if len(matches) != 0 {
		slices.Sort(matches)
		return matches, nil
	}
	if strings.ContainsAny(pattern, "*?[") {
		return nil, fmt.Errorf("--file pattern %q matched no files", pattern)
	}
	return []string{pattern}, nil
}

func validateExplicitCaseFilePath(path string) error {
	ext := strings.ToLower(filepath.Ext(path))
	switch ext {
	case ".gitignore", ".sh", ".sig":
		return fmt.Errorf("explicit case file %s uses prohibited extension %q", path, ext)
	default:
		return nil
	}
}

func buildCaseSuccessSummary(result runner.Result, outDir string) caseRunSummary {
	votesFor, votesAgainst := finalVoteCounts(result.FinalState)
	return caseRunSummary{
		Status:       "ok",
		Result:       strings.TrimSpace(result.Resolution),
		VotesFor:     &votesFor,
		VotesAgainst: &votesAgainst,
		RunID:        strings.TrimSpace(result.RunID),
		OutputDir:    strings.TrimSpace(outDir),
	}
}

func buildCaseErrorSummary(err error) caseRunSummary {
	return caseRunSummary{
		Status: "error",
		Error:  strings.TrimSpace(err.Error()),
	}
}

func reportCaseError(stdout io.Writer, err error) error {
	if writeErr := writeCaseSummary(stdout, buildCaseErrorSummary(err)); writeErr != nil {
		return writeErr
	}
	return &ReportedError{Err: err}
}

func writeCaseSummary(w io.Writer, summary caseRunSummary) error {
	wire, err := json.Marshal(summary)
	if err != nil {
		return fmt.Errorf("marshal case summary: %w", err)
	}
	if _, err := fmt.Fprintln(w, string(wire)); err != nil {
		return fmt.Errorf("write case summary: %w", err)
	}
	return nil
}

func finalVoteCounts(state map[string]any) (int, int) {
	caseObj := mapStringAny(state["case"])
	if len(caseObj) == 0 {
		return 0, 0
	}
	targetRound := intValue(caseObj["deliberation_round"])
	votes := mapListAny(caseObj["council_votes"])
	if targetRound <= 0 {
		for _, vote := range votes {
			if round := intValue(vote["round"]); round > targetRound {
				targetRound = round
			}
		}
	}
	var votesFor int
	var votesAgainst int
	for _, vote := range votes {
		if targetRound > 0 && intValue(vote["round"]) != targetRound {
			continue
		}
		switch strings.TrimSpace(fmt.Sprintf("%v", vote["vote"])) {
		case "demonstrated":
			votesFor++
		case "not_demonstrated":
			votesAgainst++
		}
	}
	return votesFor, votesAgainst
}

func mapStringAny(value any) map[string]any {
	out, _ := value.(map[string]any)
	if out == nil {
		return map[string]any{}
	}
	return out
}

func mapListAny(value any) []map[string]any {
	switch v := value.(type) {
	case []map[string]any:
		return v
	case []any:
		out := make([]map[string]any, 0, len(v))
		for _, raw := range v {
			entry, _ := raw.(map[string]any)
			if entry != nil {
				out = append(out, entry)
			}
		}
		return out
	default:
		return nil
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
	default:
		return 0
	}
}

func defaultEnginePath() string {
	exe, err := os.Executable()
	if err == nil {
		return filepath.Join(filepath.Dir(exe), "aarengine")
	}
	return filepath.FromSlash(".bin/aarengine")
}

func loadCasePolicy(flagValue string) (runner.Policy, error) {
	path := strings.TrimSpace(flagValue)
	if path == "" {
		cwd, err := os.Getwd()
		if err != nil {
			return runner.Policy{}, fmt.Errorf("resolve current working directory: %w", err)
		}
		path = filepath.Join(cwd, "etc", "policy.json")
		if _, err := os.Stat(path); err != nil {
			if os.IsNotExist(err) {
				return runner.DefaultPolicy(), nil
			}
			return runner.Policy{}, fmt.Errorf("stat default policy: %w", err)
		}
	}
	policy, err := runner.LoadPolicyFile(path)
	if err != nil {
		return runner.Policy{}, fmt.Errorf("load policy %s: %w", path, err)
	}
	return policy, nil
}

func defaultCommonRoot() string {
	cwd, err := os.Getwd()
	if err == nil {
		return locateCommonRootFrom(cwd)
	}
	return filepath.FromSlash("../common")
}

func locateCommonRootFrom(start string) string {
	base := filepath.Clean(strings.TrimSpace(start))
	if base == "" {
		return filepath.FromSlash("../common")
	}
	if !filepath.IsAbs(base) {
		if absBase, err := filepath.Abs(base); err == nil {
			base = absBase
		}
	}
	for {
		candidate := filepath.Join(base, "common")
		if fileExists(filepath.Join(candidate, "etc", "xproxy.json")) || fileExists(filepath.Join(candidate, "etc", "personas.csv")) {
			return candidate
		}
		if filepath.Base(base) == "common" && (fileExists(filepath.Join(base, "etc", "xproxy.json")) || fileExists(filepath.Join(base, "etc", "personas.csv"))) {
			return base
		}
		next := filepath.Dir(base)
		if next == base {
			break
		}
		base = next
	}
	return filepath.Clean(filepath.Join(start, filepath.FromSlash("../common")))
}

func fileExists(path string) bool {
	info, err := os.Stat(path)
	return err == nil && !info.IsDir()
}
