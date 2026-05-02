package runner

import (
	"context"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"adjudication/arbd/runtime/lean"
	"adjudication/arbd/runtime/spec"
)

func Run(ctx context.Context, cfg Config, complaint spec.Complaint) (result Result, err error) {
	if cfg.OutputDir == "" {
		return Result{}, fmt.Errorf("output dir is required")
	}
	if cfg.ComplaintPath == "" {
		return Result{}, fmt.Errorf("complaint path is required")
	}
	if cfg.Engine.Command == nil {
		return Result{}, fmt.Errorf("lean engine command is required")
	}
	if err := ValidatePolicy(cfg.Policy); err != nil {
		return Result{}, err
	}
	if err := ValidateRuntimeLimits(cfg.Runtime); err != nil {
		return Result{}, err
	}
	if err := os.MkdirAll(cfg.OutputDir, 0o755); err != nil {
		return Result{}, fmt.Errorf("create out dir: %w", err)
	}
	attorneys, err := attorneyRunInfos(cfg, cfg.ComplaintPath)
	if err != nil {
		return Result{}, err
	}
	attorneyMap := make(map[string]AttorneyRunInfo, len(attorneys))
	for _, attorney := range attorneys {
		attorneyMap[attorney.Role] = attorney
	}
	startedAt := time.Now().UTC()
	server, err := maybeStartXProxy(cfg.XProxyConfigPath, cfg.XProxyPort)
	if err != nil {
		return Result{}, err
	}
	if server != nil {
		defer server.Close()
	}
	llmClient, err := newXProxyClient(cfg.XProxyPort, cfg.Runtime.CouncilRequestTimeout())
	if err != nil {
		return Result{}, err
	}
	var caseFiles []CaseFile
	if len(cfg.CaseFilePaths) != 0 {
		caseFiles, err = loadCaseFilesFromPaths(cfg.CaseFilePaths)
		if err != nil {
			return Result{}, err
		}
	} else {
		caseDir := filepath.Dir(cfg.ComplaintPath)
		caseFiles, err = loadCaseFiles(caseDir)
		if err != nil {
			return Result{}, err
		}
	}
	fileByID := make(map[string]CaseFile, len(caseFiles))
	for _, file := range caseFiles {
		fileByID[file.FileID] = file
	}
	council, err := sampleCouncil(cfg.CouncilPoolPath, cfg.CommonRoot, cfg.Policy.CouncilSize)
	if err != nil {
		return Result{}, err
	}
	initialState := initialState(cfg.Policy)
	initResp, err := cfg.Engine.InitializeCase(initialState, complaint.Question, councilSeatMaps(council))
	if err != nil {
		return Result{}, err
	}
	if ok, _ := initResp["ok"].(bool); !ok {
		return Result{}, fmt.Errorf("initialize_case rejected: %s", mapString(initResp["error"]))
	}
	rc := &runContext{
		cfg:             cfg,
		complaint:       complaint,
		state:           mapAny(initResp["state"]),
		caseFiles:       caseFiles,
		fileByID:        fileByID,
		council:         council,
		attorneys:       attorneyMap,
		acpSessions:     map[string]*acpPersistentSession{},
		workProductDirs: map[string]string{},
	}
	defer func() {
		if closeErr := rc.closeACPSessions(); closeErr != nil {
			err = errors.Join(err, closeErr)
		}
	}()
	if err := rc.recordEvent("run_initialized", "system", currentPhase(rc.state), map[string]any{
		"complaint":         complaint,
		"judgment_standard": cfg.Policy.JudgmentStandard,
		"attorneys":         attorneys,
		"council":           council,
	}); err != nil {
		return Result{}, err
	}
	for {
		opportunity, terminal, reason, err := nextOpportunity(cfg.Engine, rc.state)
		if err != nil {
			return Result{}, err
		}
		if terminal {
			finishedAt := time.Now().UTC()
			result := Result{
				RunID:            cfg.RunID,
				StartedAt:        startedAt.Format(time.RFC3339),
				FinishedAt:       finishedAt.Format(time.RFC3339),
				Status:           "ok",
				Phase:            currentPhase(rc.state),
				Complaint:        complaint,
				JudgmentStandard: currentJudgmentStandard(rc.state, cfg.Policy),
				Answers:          currentAnswers(rc.state),
				Attorneys:        attorneys,
				CaseFiles:        caseFileMetas(caseFiles),
				Council:          council,
				Events:           rc.events,
				FinalState:       rc.state,
				FinalReason:      reason,
			}
			if err := writeArtifacts(cfg, result, rc); err != nil {
				return Result{}, err
			}
			return result, nil
		}
		rc.turn++
		switch opportunity.Role {
		case "plaintiff", "defendant":
			if err := rc.executeAttorneyOpportunity(ctx, llmClient, opportunity); err != nil {
				return Result{}, err
			}
		case "council":
			if err := rc.executeCouncilOpportunity(ctx, llmClient, opportunity); err != nil {
				return Result{}, err
			}
		default:
			return Result{}, fmt.Errorf("unsupported opportunity role %q", opportunity.Role)
		}
	}
}

func initialState(policy Policy) map[string]any {
	return map[string]any{
		"schema_version": "v1",
		"forum_name":     "Agent Arbitration Degree",
		"case": map[string]any{
			"case_id":            "arbd-1",
			"caption":            "Claimant v. Respondent",
			"question":           "",
			"status":             "draft",
			"phase":              "draft",
			"council_members":    []map[string]any{},
			"openings":           []map[string]any{},
			"arguments":          []map[string]any{},
			"rebuttals":          []map[string]any{},
			"surrebuttals":       []map[string]any{},
			"closings":           []map[string]any{},
			"offered_files":      []map[string]any{},
			"technical_reports":  []map[string]any{},
			"deliberation_round": 1,
			"council_answers":    []map[string]any{},
		},
		"policy":        policy.StateMap(),
		"state_version": 0,
	}
}

func nextOpportunity(engine lean.Engine, state map[string]any) (Opportunity, bool, string, error) {
	resp, err := engine.NextOpportunity(state)
	if err != nil {
		return Opportunity{}, false, "", err
	}
	if ok, _ := resp["ok"].(bool); !ok {
		return Opportunity{}, false, "", fmt.Errorf("next_opportunity rejected: %s", mapString(resp["error"]))
	}
	if terminal, _ := resp["terminal"].(bool); terminal {
		return Opportunity{}, true, mapString(resp["reason"]), nil
	}
	raw := mapAny(resp["opportunity"])
	if len(raw) == 0 {
		return Opportunity{}, false, "", fmt.Errorf("next_opportunity returned empty opportunity")
	}
	return Opportunity{
		ID:           mapString(raw["opportunity_id"]),
		Role:         mapString(raw["role"]),
		Phase:        mapString(raw["phase"]),
		MayPass:      raw["may_pass"] == true,
		Objective:    mapString(raw["objective"]),
		AllowedTools: stringList(raw["allowed_tools"]),
	}, false, "", nil
}

func currentPhase(state map[string]any) string {
	return mapString(mapAny(state["case"])["phase"])
}

func currentJudgmentStandard(state map[string]any, policy Policy) string {
	value := mapString(mapAny(state["policy"])["judgment_standard"])
	if value != "" {
		return value
	}
	return strings.TrimSpace(policy.JudgmentStandard)
}

func currentAnswers(state map[string]any) map[string]int {
	caseObj := mapAny(state["case"])
	rawAnswers := mapList(caseObj["council_answers"])
	answers := make(map[string]int, len(rawAnswers))
	for _, raw := range rawAnswers {
		memberID := mapString(raw["member_id"])
		if memberID == "" {
			continue
		}
		answers[memberID] = intNumber(raw["answer"])
	}
	return answers
}

func stringList(value any) []string {
	switch v := value.(type) {
	case []string:
		return v
	case []any:
		out := make([]string, 0, len(v))
		for _, raw := range v {
			s := mapString(raw)
			if s != "" {
				out = append(out, s)
			}
		}
		return out
	default:
		return nil
	}
}
