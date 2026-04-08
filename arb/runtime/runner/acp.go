package runner

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"strings"
	"sync"

	"adjudication/common/acp"
)

type acpPersistentSession struct {
	client         *acp.Client
	sessionPath    string
	workspaceDir   string
	workProductDir string
	cleanup        func() error
}

func (s *acpPersistentSession) Close() error {
	if s == nil {
		return nil
	}
	var err error
	if s.client != nil {
		err = errors.Join(err, s.client.Close())
	}
	if s.cleanup != nil {
		err = errors.Join(err, s.cleanup())
	}
	return err
}

func (rc *runContext) executeAttorneyOpportunity(ctx context.Context, _ any, opportunity Opportunity) error {
	turn := rc.turn
	ctx, cancel := withTimeout(ctx, rc.cfg.Runtime.AttorneyACPTimeout())
	defer cancel()

	session, err := rc.ensureACPSession(ctx, opportunity.Role)
	if err != nil {
		return err
	}
	client := session.client

	transcript := make([]map[string]any, 0)
	var mu sync.Mutex
	appendTranscript := func(entry map[string]any) {
		mu.Lock()
		transcript = append(transcript, entry)
		mu.Unlock()
	}
	decisionSubmitted := false
	invalidDecisionAttempts := 0
	responseBytes := 0
	lastAgentToolStatus := map[string]string{}
	pendingAgentToolInput := map[string]any{}
	countedToolInput := map[string]bool{}
	var notifyErr error
	setNotifyErr := func(err error) {
		if err == nil {
			return
		}
		mu.Lock()
		defer mu.Unlock()
		if notifyErr != nil {
			return
		}
		notifyErr = err
		cancel()
	}
	accumulateResponseBytes := func(value any) {
		size, err := jsonPayloadSize(value)
		if err != nil {
			setNotifyErr(err)
			return
		}
		mu.Lock()
		defer mu.Unlock()
		if notifyErr != nil {
			return
		}
		responseBytes += size
		if responseBytes > rc.cfg.Runtime.MaxResponseBytes {
			notifyErr = fmt.Errorf("attorney response exceeded byte limit of %d", rc.cfg.Runtime.MaxResponseBytes)
			cancel()
		}
	}

	unsub := client.OnNotification(func(note acp.Notification) {
		if note.Method != "session/update" {
			return
		}
		update := mapAny(note.Params["update"])
		switch mapString(update["sessionUpdate"]) {
		case "agent_message_chunk", "agent_thought_chunk":
			content := mapAny(update["content"])
			text := mapString(content["text"])
			if text != "" {
				accumulateResponseBytes(text)
				appendTranscript(map[string]any{"assistant_text": text})
				_ = rc.recordEventAtTurn(turn, "assistant_text", opportunity.Role, opportunity.Phase, map[string]any{"text": text})
			}
		case "tool_call":
			toolCallID := mapString(update["toolCallId"])
			rawInput := update["rawInput"]
			if toolCallID != "" && rawInput != nil && !countedToolInput[toolCallID] {
				accumulateResponseBytes(rawInput)
				countedToolInput[toolCallID] = true
			}
			entry := map[string]any{
				"tool_call_id": toolCallID,
				"title":        mapString(update["title"]),
				"status":       mapString(update["status"]),
				"raw_input":    rawInput,
			}
			if toolCallID != "" {
				lastAgentToolStatus[toolCallID] = mapString(update["status"])
			}
			appendTranscript(map[string]any{"agent_tool_call": entry})
			_ = rc.recordEventAtTurn(turn, "agent_tool_call", opportunity.Role, opportunity.Phase, entry)
		case "tool_call_update":
			toolCallID := mapString(update["toolCallId"])
			status := mapString(update["status"])
			rawInput := update["rawInput"]
			rawOutput := update["rawOutput"]
			if toolCallID != "" && rawInput != nil && !countedToolInput[toolCallID] {
				accumulateResponseBytes(rawInput)
				countedToolInput[toolCallID] = true
			}
			if toolCallID != "" && status == "pending" && rawInput != nil && rawOutput == nil {
				pendingAgentToolInput[toolCallID] = rawInput
				if lastAgentToolStatus[toolCallID] == status {
					return
				}
				lastAgentToolStatus[toolCallID] = status
				return
			}
			entry := map[string]any{
				"tool_call_id": toolCallID,
				"status":       status,
			}
			if rawInput != nil {
				entry["raw_input"] = rawInput
			} else if buffered := pendingAgentToolInput[toolCallID]; buffered != nil {
				entry["raw_input"] = buffered
			}
			if rawOutput != nil {
				entry["raw_output"] = rawOutput
			}
			if toolCallID != "" &&
				entry["raw_input"] == nil &&
				entry["raw_output"] == nil &&
				status != "" &&
				lastAgentToolStatus[toolCallID] == status {
				return
			}
			if toolCallID != "" {
				if status != "" {
					lastAgentToolStatus[toolCallID] = status
				}
				if status != "pending" {
					delete(pendingAgentToolInput, toolCallID)
				}
			}
			appendTranscript(map[string]any{"agent_tool_update": entry})
			_ = rc.recordEventAtTurn(turn, "agent_tool_update", opportunity.Role, opportunity.Phase, entry)
		}
	})
	defer unsub()

	client.HandleMethod(acpCustomMethod("get_case"), func(_ context.Context, _ map[string]any) (map[string]any, error) {
		view := rc.attorneyView(opportunity)
		appendTranscript(map[string]any{"custom_method": acpCustomMethod("get_case"), "result": view})
		return map[string]any{
			"text": marshalInline(view),
			"case": view,
		}, nil
	})
	client.HandleMethod(acpCustomMethod("list_case_files"), func(_ context.Context, _ map[string]any) (map[string]any, error) {
		files := caseFileMetas(rc.caseFiles)
		appendTranscript(map[string]any{"custom_method": acpCustomMethod("list_case_files"), "result": files})
		return map[string]any{
			"text":  marshalInline(map[string]any{"files": files}),
			"files": files,
		}, nil
	})
	client.HandleMethod(acpCustomMethod("read_case_text_file"), func(_ context.Context, params map[string]any) (map[string]any, error) {
		fileID := mapString(params["file_id"])
		file, ok := rc.fileByID[fileID]
		if !ok {
			return nil, fmt.Errorf("unknown case file %q", fileID)
		}
		if !file.TextReadable {
			return nil, fmt.Errorf("case file %q is not text-readable", fileID)
		}
		appendTranscript(map[string]any{"custom_method": acpCustomMethod("read_case_text_file"), "file_id": fileID})
		return map[string]any{
			"text":    file.Text,
			"file_id": fileID,
		}, nil
	})
	client.HandleMethod(acpCustomMethod("write_case_file"), func(_ context.Context, params map[string]any) (map[string]any, error) {
		fileID := mapString(params["file_id"])
		file, ok := rc.fileByID[fileID]
		if !ok {
			return nil, fmt.Errorf("unknown case file %q", fileID)
		}
		path, err := writeCaseFileToWorkspace(session.workspaceDir, file)
		if err != nil {
			return nil, err
		}
		appendTranscript(map[string]any{"custom_method": acpCustomMethod("write_case_file"), "file_id": fileID, "workspace_path": path})
		return map[string]any{
			"text":           fmt.Sprintf("Wrote %s to %s", fileID, path),
			"file_id":        fileID,
			"workspace_path": path,
		}, nil
	})
	client.HandleMethod(acpCustomMethod("submit_decision"), func(_ context.Context, params map[string]any) (map[string]any, error) {
		if decisionSubmitted {
			return nil, fmt.Errorf("decision already submitted for this opportunity")
		}
		actionType, payload, err := attorneyDecision(opportunity, params, rc.fileByID, rc.cfg.Policy)
		if err != nil {
			invalidDecisionAttempts++
			if invalidDecisionAttempts >= rc.cfg.Runtime.InvalidAttemptLimit {
				setNotifyErr(fmt.Errorf("%s exceeded invalid-attempt limit", opportunity.Role))
			}
			return nil, err
		}
		if err := rc.validateAttorneyPayloadAgainstState(opportunity, actionType, payload); err != nil {
			invalidDecisionAttempts++
			if invalidDecisionAttempts >= rc.cfg.Runtime.InvalidAttemptLimit {
				setNotifyErr(fmt.Errorf("%s exceeded invalid-attempt limit", opportunity.Role))
			}
			return nil, err
		}
		stepResp, err := rc.cfg.Engine.Step(rc.state, actionType, opportunity.Role, payload)
		if err != nil {
			invalidDecisionAttempts++
			if invalidDecisionAttempts >= rc.cfg.Runtime.InvalidAttemptLimit {
				setNotifyErr(fmt.Errorf("%s exceeded invalid-attempt limit", opportunity.Role))
			}
			return nil, err
		}
		if ok, _ := stepResp["ok"].(bool); !ok {
			invalidDecisionAttempts++
			if invalidDecisionAttempts >= rc.cfg.Runtime.InvalidAttemptLimit {
				setNotifyErr(fmt.Errorf("%s exceeded invalid-attempt limit", opportunity.Role))
			}
			return nil, fmt.Errorf("%s", mapString(stepResp["error"]))
		}
		rc.state = mapAny(stepResp["state"])
		decisionSubmitted = true
		appendTranscript(map[string]any{
			"decision":    params,
			"action":      actionType,
			"payload":     payload,
			"step_result": stepResp,
		})
		if err := rc.recordEventAtTurn(turn, "attorney_action", opportunity.Role, opportunity.Phase, map[string]any{
			"opportunity_id": opportunity.ID,
			"action_type":    actionType,
			"payload":        payload,
		}); err != nil {
			setNotifyErr(err)
		}
		return map[string]any{
			"text": "Decision accepted.",
		}, nil
	})

	sessionResp, err := client.NewSession(ctx, session.sessionPath)
	if err != nil {
		return err
	}
	prompt, err := rc.buildAttorneyPrompt(opportunity)
	if err != nil {
		return err
	}
	if _, err := client.Prompt(ctx, acp.PromptRequest{
		SessionID: sessionResp.SessionID,
		Prompt:    []acp.TextBlock{{Type: "text", Text: prompt}},
	}); err != nil {
		mu.Lock()
		defer mu.Unlock()
		if notifyErr != nil {
			return notifyErr
		}
		if decisionSubmitted {
			return nil
		}
		return err
	}
	mu.Lock()
	defer mu.Unlock()
	if notifyErr != nil {
		return notifyErr
	}
	if !decisionSubmitted {
		return fmt.Errorf("acp attorney did not submit a decision")
	}
	return nil
}

func (rc *runContext) ensureACPSession(ctx context.Context, role string) (*acpPersistentSession, error) {
	if session, ok := rc.acpSessions[role]; ok {
		return session, nil
	}
	attorney, err := rc.attorneyInfo(role)
	if err != nil {
		return nil, err
	}
	sessionCwd := attorney.SessionCwd
	sessionACPPath := sessionCwd
	env := append([]string{}, rc.cfg.ACPEnv...)
	cleanup := func() error { return nil }
	workspaceDir := ""
	workProductDir := ""
	instructionsPath := strings.TrimSpace(rc.cfg.AttorneyInstructionsPath)
	if usesPIContainerWrapper(attorney.ACPCommand) {
		containerHomeDir, closeHome, err := prepareEphemeralPIHome(rc.cfg.CommonRoot, attorney.Model, instructionsPath)
		if err != nil {
			return nil, err
		}
		cleanup = closeHome
		env = append(env, "PI_CONTAINER_HOME_DIR="+containerHomeDir)
		if instructionsPath != "" {
			env = append(env, "PI_ACP_INSTRUCTIONS_FILE="+stagedAttorneyInstructionsACPPath)
		}
		sessionACPPath = "/home/user"
		workspaceDir = containerHomeDir
		workProductDir = filepath.Join(containerHomeDir, "work-product")
		if err := os.MkdirAll(workProductDir, 0o755); err != nil {
			return nil, errors.Join(fmt.Errorf("create work-product dir: %w", err), cleanup())
		}
	} else if attorney.ACPTransport == "stdio" && instructionsPath != "" {
		env = append(env, "PI_ACP_INSTRUCTIONS_FILE="+instructionsPath)
	}
	env = append(env, "PI_ACP_CLIENT_TOOLS="+marshalInline(acpClientToolSpecs(workspaceDir != "")))
	client, err := acp.NewClient(acp.Config{
		Command:  attorney.ACPCommand,
		Endpoint: attorney.ACPEndpoint,
		Args:     rc.cfg.ACPArgs,
		Cwd:      sessionCwd,
		Env:      env,
	})
	if err != nil {
		return nil, errors.Join(err, cleanup())
	}
	session := &acpPersistentSession{
		client:         client,
		sessionPath:    sessionACPPath,
		workspaceDir:   workspaceDir,
		workProductDir: workProductDir,
		cleanup:        cleanup,
	}
	if _, err := client.Initialize(ctx, 1); err != nil {
		return nil, errors.Join(err, session.Close())
	}
	rc.acpSessions[role] = session
	if strings.TrimSpace(workProductDir) != "" {
		rc.workProductDirs[role] = workProductDir
	}
	return session, nil
}

func (rc *runContext) closeACPSessions() error {
	if len(rc.acpSessions) == 0 {
		return nil
	}
	roleNames := make([]string, 0, len(rc.acpSessions))
	for role := range rc.acpSessions {
		roleNames = append(roleNames, role)
	}
	sort.Strings(roleNames)
	var err error
	for _, role := range roleNames {
		session := rc.acpSessions[role]
		delete(rc.acpSessions, role)
		if closeErr := session.Close(); closeErr != nil {
			err = errors.Join(err, fmt.Errorf("close ACP session role=%s: %w", role, closeErr))
		}
	}
	return err
}

func attorneyDecision(opportunity Opportunity, params map[string]any, fileByID map[string]CaseFile, policy Policy) (string, map[string]any, error) {
	kind := mapString(params["kind"])
	switch kind {
	case "pass":
		if !opportunity.MayPass {
			return "", nil, fmt.Errorf("passing is not allowed in this opportunity")
		}
		switch opportunity.Phase {
		case "rebuttals", "surrebuttals":
			return "pass_phase_opportunity", map[string]any{}, nil
		default:
			return "", nil, fmt.Errorf("passing is not allowed in phase %q", opportunity.Phase)
		}
	case "tool":
		toolName := mapString(params["tool_name"])
		if !slices.Contains(opportunity.AllowedTools, toolName) {
			return "", nil, fmt.Errorf("tool %q is not allowed in this opportunity", toolName)
		}
		payload := normalizePayload(params["payload"])
		if err := validateAttorneyPayload(toolName, payload, fileByID, policy); err != nil {
			return "", nil, err
		}
		return toolName, payload, nil
	default:
		return "", nil, fmt.Errorf("submit_decision kind must be tool or pass")
	}
}

func validateAttorneyPayload(actionType string, payload map[string]any, fileByID map[string]CaseFile, policy Policy) error {
	switch actionType {
	case "record_opening_statement", "deliver_closing_statement":
		if mapString(payload["text"]) == "" {
			return fmt.Errorf("payload.text is required")
		}
	case "submit_argument":
		if mapString(payload["text"]) == "" {
			return fmt.Errorf("payload.text is required")
		}
		if err := validateOfferedFiles(payload["offered_files"], fileByID, policy); err != nil {
			return err
		}
		if err := validateReports(payload["technical_reports"], policy); err != nil {
			return err
		}
	case "submit_rebuttal":
		if mapString(payload["text"]) == "" {
			return fmt.Errorf("payload.text is required")
		}
		if err := validateOfferedFiles(payload["offered_files"], fileByID, policy); err != nil {
			return err
		}
		if err := validateReports(payload["technical_reports"], policy); err != nil {
			return err
		}
	case "submit_surrebuttal":
		if mapString(payload["text"]) == "" {
			return fmt.Errorf("payload.text is required")
		}
		if len(listOfMaps(payload["offered_files"])) != 0 {
			return fmt.Errorf("offered_files are allowed only in arguments and rebuttals")
		}
		if len(listOfMaps(payload["technical_reports"])) != 0 {
			return fmt.Errorf("technical_reports are allowed only in arguments and rebuttals")
		}
	case "pass_phase_opportunity":
	default:
		return fmt.Errorf("unsupported action type %q", actionType)
	}
	return nil
}

func validateOfferedFiles(value any, fileByID map[string]CaseFile, policy Policy) error {
	entries := listOfMaps(value)
	if len(entries) > policy.MaxExhibitsPerFiling {
		return fmt.Errorf("offered_files exceed per-filing limit of %d (attempted %d)", policy.MaxExhibitsPerFiling, len(entries))
	}
	for _, entry := range entries {
		fileID := mapString(entry["file_id"])
		if fileID == "" {
			return fmt.Errorf("offered_files entry requires file_id")
		}
		file, ok := fileByID[fileID]
		if !ok {
			return fmt.Errorf("unknown offered file %q; offered_files must use visible case file_id values, not workspace paths or downloaded filenames", fileID)
		}
		if file.SizeBytes > policy.MaxExhibitBytes {
			return fmt.Errorf("offered file %q exceeds byte limit of %d", fileID, policy.MaxExhibitBytes)
		}
	}
	return nil
}

func validateReports(value any, policy Policy) error {
	entries := listOfMaps(value)
	if len(entries) > policy.MaxReportsPerFiling {
		return fmt.Errorf("technical_reports exceed per-filing limit of %d (attempted %d)", policy.MaxReportsPerFiling, len(entries))
	}
	for _, entry := range entries {
		title := mapString(entry["title"])
		summary := mapString(entry["summary"])
		if title == "" {
			return fmt.Errorf("technical_reports entry requires title")
		}
		if summary == "" {
			return fmt.Errorf("technical_reports entry requires summary")
		}
		if len([]byte(title)) > policy.MaxReportTitleBytes {
			return fmt.Errorf("technical_reports title exceeds byte limit of %d", policy.MaxReportTitleBytes)
		}
		if len([]byte(summary)) > policy.MaxReportSummaryBytes {
			return fmt.Errorf("technical_reports summary exceeds byte limit of %d", policy.MaxReportSummaryBytes)
		}
	}
	return nil
}

func normalizePayload(value any) map[string]any {
	payload := mapAny(value)
	if len(payload) == 0 {
		return map[string]any{}
	}
	return cloneMap(payload)
}

func jsonPayloadSize(value any) (int, error) {
	wire, err := json.Marshal(value)
	if err != nil {
		return 0, fmt.Errorf("marshal response payload size: %w", err)
	}
	return len(wire), nil
}

func listOfMaps(value any) []map[string]any {
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

func ACPClientToolSpecs(includeWorkspaceWriter bool) []map[string]any {
	return acpClientToolSpecs(includeWorkspaceWriter)
}

func acpClientToolSpecs(includeWorkspaceWriter bool) []map[string]any {
	specs := []map[string]any{
		{
			"method":      acpCustomMethod("get_case"),
			"toolName":    "aar_get_case",
			"description": "Return the current visible arbitration record.",
			"parameters":  map[string]any{"type": "object", "properties": map[string]any{}, "additionalProperties": false},
		},
		{
			"method":      acpCustomMethod("list_case_files"),
			"toolName":    "aar_list_case_files",
			"description": "List visible case files.",
			"parameters":  map[string]any{"type": "object", "properties": map[string]any{}, "additionalProperties": false},
		},
		{
			"method":      acpCustomMethod("read_case_text_file"),
			"toolName":    "aar_read_case_text_file",
			"description": "Read one visible text case file by file_id.",
			"parameters": map[string]any{
				"type": "object",
				"properties": map[string]any{
					"file_id": map[string]any{"type": "string"},
				},
				"required":             []string{"file_id"},
				"additionalProperties": false,
			},
		},
	}
	if includeWorkspaceWriter {
		specs = append(specs, map[string]any{
			"method":      acpCustomMethod("write_case_file"),
			"toolName":    "aar_write_case_file",
			"description": "Write one visible case file into the local workspace with exact bytes.",
			"parameters": map[string]any{
				"type": "object",
				"properties": map[string]any{
					"file_id": map[string]any{"type": "string"},
				},
				"required":             []string{"file_id"},
				"additionalProperties": false,
			},
		})
	}
	specs = append(specs, map[string]any{
		"method":      acpCustomMethod("submit_decision"),
		"toolName":    "aar_submit_decision",
		"description": "Submit the legal act for the current opportunity.",
		"parameters": map[string]any{
			"type": "object",
			"properties": map[string]any{
				"kind": map[string]any{"type": "string", "enum": []string{"tool", "pass"}},
				"tool_name": map[string]any{
					"type": "string",
					"enum": []string{
						"record_opening_statement",
						"submit_argument",
						"submit_rebuttal",
						"submit_surrebuttal",
						"deliver_closing_statement",
						"pass_phase_opportunity",
					},
				},
				"payload": attorneyPayloadSchema(),
			},
			"required":             []string{"kind"},
			"additionalProperties": false,
		},
	})
	return specs
}

func attorneyPayloadSchema() map[string]any {
	return map[string]any{
		"type": "object",
		"properties": map[string]any{
			"text":              map[string]any{"type": "string"},
			"offered_files":     offeredFilesSchema(),
			"technical_reports": technicalReportsSchema(),
		},
		"additionalProperties": false,
	}
}

func offeredFilesSchema() map[string]any {
	return map[string]any{
		"type": "array",
		"items": map[string]any{
			"type": "object",
			"properties": map[string]any{
				"file_id": map[string]any{"type": "string"},
				"label":   map[string]any{"type": "string"},
			},
			"required":             []string{"file_id", "label"},
			"additionalProperties": false,
		},
	}
}

func technicalReportsSchema() map[string]any {
	return map[string]any{
		"type": "array",
		"items": map[string]any{
			"type": "object",
			"properties": map[string]any{
				"title":   map[string]any{"type": "string"},
				"summary": map[string]any{"type": "string"},
			},
			"required":             []string{"title", "summary"},
			"additionalProperties": false,
		},
	}
}

func acpToolSpecs(opportunity Opportunity, includeWorkspaceWriter bool) []map[string]any {
	all := acpClientToolSpecs(includeWorkspaceWriter)
	specs := []map[string]any{all[0]}
	if opportunity.Phase == "arguments" || opportunity.Phase == "rebuttals" {
		specs = append(specs, all[1], all[2])
		next := 3
		if includeWorkspaceWriter {
			specs = append(specs, all[next])
			next++
		}
		specs = append(specs, all[next])
		return specs
	}
	specs = append(specs, all[len(all)-1])
	return specs
}

func acpCustomMethod(name string) string {
	return "_aar/" + strings.TrimSpace(name)
}

func (rc *runContext) attorneyInfo(role string) (AttorneyRunInfo, error) {
	if attorney, ok := rc.attorneys[role]; ok {
		return attorney, nil
	}
	model := strings.TrimSpace(rc.cfg.AttorneyModel)
	if model == "" {
		model = DefaultAttorneyModel
	}
	spec, err := parseAttorneyModel(model)
	if err != nil {
		return AttorneyRunInfo{}, err
	}
	sessionCwd := ""
	if strings.TrimSpace(rc.cfg.ComplaintPath) != "" {
		sessionCwd, err = filepath.Abs(filepath.Dir(rc.cfg.ComplaintPath))
		if err != nil {
			return AttorneyRunInfo{}, fmt.Errorf("resolve attorney session cwd: %w", err)
		}
	}
	return AttorneyRunInfo{
		Role:          role,
		Model:         model,
		SearchEnabled: spec.SearchRequested,
		ACPTransport:  "stdio",
		ACPCommand:    rc.cfg.ACPCommand,
		SessionCwd:    sessionCwd,
	}, nil
}

func (rc *runContext) attorneyView(opportunity Opportunity) map[string]any {
	limits := rc.attorneyLimits(opportunity)
	attorneyModel := ""
	if attorney, err := rc.attorneyInfo(opportunity.Role); err == nil {
		attorneyModel = attorney.Model
	}
	return map[string]any{
		"proposition":       rc.complaint.Proposition,
		"evidence_standard": currentEvidenceStandard(rc.state, rc.cfg.Policy),
		"attorney_model":    attorneyModel,
		"phase":             currentPhase(rc.state),
		"opportunity": map[string]any{
			"id":            opportunity.ID,
			"role":          opportunity.Role,
			"phase":         opportunity.Phase,
			"objective":     opportunity.Objective,
			"allowed_tools": opportunity.AllowedTools,
			"may_pass":      opportunity.MayPass,
		},
		"record": map[string]any{
			"openings":          mapList(mapAny(rc.state["case"])["openings"]),
			"arguments":         mapList(mapAny(rc.state["case"])["arguments"]),
			"rebuttals":         mapList(mapAny(rc.state["case"])["rebuttals"]),
			"surrebuttals":      mapList(mapAny(rc.state["case"])["surrebuttals"]),
			"closings":          mapList(mapAny(rc.state["case"])["closings"]),
			"exhibits":          rc.attorneyExhibits(),
			"technical_reports": mapList(mapAny(rc.state["case"])["technical_reports"]),
		},
		"limits":  limits,
		"council": rc.council,
	}
}

func (rc *runContext) attorneyCapabilitySection(role string) (string, error) {
	attorney, err := rc.attorneyInfo(role)
	if err != nil {
		return "", err
	}
	if attorney.SearchEnabled {
		return "Model capabilities for this run:\nNative web search through the model is available.", nil
	}
	return "Model capabilities for this run:\nNative web search through the model is not available.", nil
}

func (rc *runContext) buildAttorneyPrompt(opportunity Opportunity) (string, error) {
	view := rc.attorneyView(opportunity)
	visibleFilesSection := ""
	workspaceSection := ""
	workProductSection := ""
	if opportunity.Phase == "arguments" || opportunity.Phase == "rebuttals" {
		visibleFilesSection = "Visible case files:\n" + marshalIndented(caseFileMetas(rc.caseFiles)) + "\n"
		workspaceSection = "If local tools need exact file bytes, write the visible file into the workspace first. Do not reconstruct byte-sensitive files by hand.\n"
	}
	if attorney, err := rc.attorneyInfo(opportunity.Role); err == nil && usesPIContainerWrapper(attorney.ACPCommand) {
		workProductSection = "Private work product: Use `/home/user/work-product/` for internal notes, timelines, source leads, adverse facts, unresolved questions, and draft analyses. This directory is not part of the record unless you later turn material from it into an exhibit or technical report. Its contents may be exported after the proceeding for review.\n"
	}
	capabilitySection, err := rc.attorneyCapabilitySection(opportunity.Role)
	if err != nil {
		return "", err
	}
	common, err := renderPromptFile("attorney-common.md", map[string]string{
		"ROLE":                       opportunity.Role,
		"PHASE":                      opportunity.Phase,
		"OBJECTIVE":                  opportunity.Objective,
		"PROPOSITION":                rc.complaint.Proposition,
		"EVIDENCE_STANDARD":          currentEvidenceStandard(rc.state, rc.cfg.Policy),
		"MODEL_CAPABILITIES_SECTION": capabilitySection,
		"CURRENT_RECORD":             marshalIndented(view["record"]),
		"LIMITS_SECTION":             rc.attorneyLimitsSection(opportunity),
		"COUNCIL":                    marshalIndented(view["council"]),
		"VISIBLE_CASE_FILES_SECTION": visibleFilesSection,
		"WORKSPACE_SECTION":          workspaceSection,
		"WORK_PRODUCT_SECTION":       workProductSection,
		"ALLOWED_TOOLS":              strings.Join(opportunity.AllowedTools, ", "),
	})
	if err != nil {
		return "", err
	}
	phaseFile, err := attorneyPromptFile(opportunity.Phase)
	if err != nil {
		return "", err
	}
	phaseText, err := renderPromptFile(phaseFile, nil)
	if err != nil {
		return "", err
	}
	return common + "\n\n" + phaseText + "\n\nWhen you have submitted the legal act for this opportunity, reply exactly: decision-submitted.", nil
}

func writeCaseFileToWorkspace(workspaceDir string, file CaseFile) (string, error) {
	workspaceDir = strings.TrimSpace(workspaceDir)
	if workspaceDir == "" {
		return "", fmt.Errorf("workspace file writing is not available in this session")
	}
	name := filepath.Base(strings.TrimSpace(file.Name))
	if name == "" || name == "." || name == string(filepath.Separator) {
		return "", fmt.Errorf("invalid case file name %q", file.Name)
	}
	raw, err := os.ReadFile(file.Path)
	if err != nil {
		return "", fmt.Errorf("read case file %s: %w", file.FileID, err)
	}
	hostPath := filepath.Join(workspaceDir, name)
	if err := os.WriteFile(hostPath, raw, 0o644); err != nil {
		return "", fmt.Errorf("write workspace file %s: %w", hostPath, err)
	}
	return filepath.ToSlash(filepath.Join("/home/user", name)), nil
}

func (rc *runContext) attorneyExhibits() []map[string]any {
	items := mapList(mapAny(rc.state["case"])["offered_files"])
	out := make([]map[string]any, 0, len(items))
	for _, item := range items {
		fileID := mapString(item["file_id"])
		label := mapString(item["label"])
		entry := map[string]any{
			"phase":   mapString(item["phase"]),
			"role":    mapString(item["role"]),
			"file_id": fileID,
			"label":   label,
		}
		if file, ok := rc.fileByID[fileID]; ok {
			if file.TextReadable {
				entry["text"] = file.Text
			} else {
				entry["text"] = "(binary or non-text file)"
			}
		} else {
			entry["text"] = "(unavailable file)"
		}
		out = append(out, entry)
	}
	return out
}

func (rc *runContext) attorneyLimits(opportunity Opportunity) map[string]any {
	caseObj := mapAny(rc.state["case"])
	usedExhibits := filingCountForRole(mapList(caseObj["offered_files"]), opportunity.Role)
	usedReports := filingCountForRole(mapList(caseObj["technical_reports"]), opportunity.Role)
	limits := map[string]any{
		"text_char_limit": phaseTextCharLimit(rc.cfg.Policy, opportunity.Phase),
	}
	if opportunity.Phase == "arguments" || opportunity.Phase == "rebuttals" {
		limits["max_exhibits_per_filing"] = rc.cfg.Policy.MaxExhibitsPerFiling
		limits["max_exhibits_per_side"] = rc.cfg.Policy.MaxExhibitsPerSide
		limits["used_exhibits_for_side"] = usedExhibits
		limits["remaining_exhibits_for_side"] = remainingCapacity(rc.cfg.Policy.MaxExhibitsPerSide, usedExhibits)
		limits["max_reports_per_filing"] = rc.cfg.Policy.MaxReportsPerFiling
		limits["max_reports_per_side"] = rc.cfg.Policy.MaxReportsPerSide
		limits["used_reports_for_side"] = usedReports
		limits["remaining_reports_for_side"] = remainingCapacity(rc.cfg.Policy.MaxReportsPerSide, usedReports)
		limits["offered_files_rule"] = "Use only visible case file_id values in offered_files."
		limits["outside_material_rule"] = "Outside material that is not already a visible case file belongs in technical_reports."
	}
	if opportunity.Phase == "surrebuttals" {
		limits["outside_material_rule"] = "offered_files and technical_reports are not allowed in this phase."
	}
	return limits
}

func (rc *runContext) attorneyLimitsSection(opportunity Opportunity) string {
	limits := rc.attorneyLimits(opportunity)
	lines := []string{}
	if limit, _ := limits["text_char_limit"].(int); limit > 0 {
		lines = append(lines, fmt.Sprintf("Text limit for this submission: %d characters.", limit))
		lines = append(lines, fmt.Sprintf("Target length for the first submission: %d characters or less.", targetSubmissionCharLimit(limit)))
	}
	switch opportunity.Phase {
	case "arguments", "rebuttals":
		lines = append(lines,
			fmt.Sprintf(
				"Exhibits: at most %d in this filing. This side has used %d of %d total, with %d left.",
				limits["max_exhibits_per_filing"].(int),
				limits["used_exhibits_for_side"].(int),
				limits["max_exhibits_per_side"].(int),
				limits["remaining_exhibits_for_side"].(int),
			),
		)
		lines = append(lines,
			fmt.Sprintf(
				"Technical reports: at most %d in this filing. This side has used %d of %d total, with %d left.",
				limits["max_reports_per_filing"].(int),
				limits["used_reports_for_side"].(int),
				limits["max_reports_per_side"].(int),
				limits["remaining_reports_for_side"].(int),
			),
		)
		lines = append(lines, "Use only visible case file_id values in offered_files. Do not use workspace paths, downloaded filenames, or invented names there.")
		lines = append(lines, "Outside material that is not already a visible case file belongs in technical_reports, not offered_files.")
	case "surrebuttals":
		lines = append(lines, "offered_files and technical_reports are not allowed in this phase.")
	}
	return strings.Join(lines, "\n")
}

func targetSubmissionCharLimit(limit int) int {
	if limit <= 0 {
		return 0
	}
	target := (limit * 3) / 4
	if target <= 0 {
		return limit
	}
	return target
}

func phaseTextCharLimit(policy Policy, phase string) int {
	switch phase {
	case "openings":
		return policy.MaxOpeningChars
	case "arguments":
		return policy.MaxArgumentChars
	case "rebuttals":
		return policy.MaxRebuttalChars
	case "surrebuttals":
		return policy.MaxSurrebuttalChars
	case "closings":
		return policy.MaxClosingChars
	default:
		return 0
	}
}

func filingCountForRole(items []map[string]any, role string) int {
	count := 0
	for _, item := range items {
		if mapString(item["role"]) == role {
			count++
		}
	}
	return count
}

func remainingCapacity(limit int, used int) int {
	if limit-used < 0 {
		return 0
	}
	return limit - used
}

func (rc *runContext) validateAttorneyPayloadAgainstState(opportunity Opportunity, actionType string, payload map[string]any) error {
	text := strings.TrimSpace(mapString(payload["text"]))
	if limit := phaseTextCharLimit(rc.cfg.Policy, opportunity.Phase); limit > 0 {
		charCount := len([]rune(text))
		if charCount > limit {
			return fmt.Errorf("%s exceeds character limit of %d (got %d)", filingLabel(actionType), limit, charCount)
		}
	}
	switch actionType {
	case "submit_argument", "submit_rebuttal":
		caseObj := mapAny(rc.state["case"])
		usedExhibits := filingCountForRole(mapList(caseObj["offered_files"]), opportunity.Role)
		attemptedExhibits := len(listOfMaps(payload["offered_files"]))
		if usedExhibits+attemptedExhibits > rc.cfg.Policy.MaxExhibitsPerSide {
			return fmt.Errorf(
				"offered_files for this side exceed limit of %d (%d already used, %d attempted, %d remaining)",
				rc.cfg.Policy.MaxExhibitsPerSide,
				usedExhibits,
				attemptedExhibits,
				remainingCapacity(rc.cfg.Policy.MaxExhibitsPerSide, usedExhibits),
			)
		}
		usedReports := filingCountForRole(mapList(caseObj["technical_reports"]), opportunity.Role)
		attemptedReports := len(listOfMaps(payload["technical_reports"]))
		if usedReports+attemptedReports > rc.cfg.Policy.MaxReportsPerSide {
			return fmt.Errorf(
				"technical_reports for this side exceed limit of %d (%d already used, %d attempted, %d remaining)",
				rc.cfg.Policy.MaxReportsPerSide,
				usedReports,
				attemptedReports,
				remainingCapacity(rc.cfg.Policy.MaxReportsPerSide, usedReports),
			)
		}
	}
	return nil
}

func filingLabel(actionType string) string {
	switch actionType {
	case "record_opening_statement":
		return "opening statement"
	case "submit_argument":
		return "argument"
	case "submit_rebuttal":
		return "rebuttal"
	case "submit_surrebuttal":
		return "surrebuttal"
	case "deliver_closing_statement":
		return "closing statement"
	default:
		return "submission"
	}
}

func marshalInline(value any) string {
	wire, err := json.Marshal(value)
	if err != nil {
		return fmt.Sprintf("%v", value)
	}
	return string(wire)
}

func marshalIndented(value any) string {
	wire, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		return fmt.Sprintf("%v", value)
	}
	return string(wire)
}

func copyTree(dstRoot string, srcRoot string) error {
	return filepath.WalkDir(srcRoot, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(srcRoot, path)
		if err != nil {
			return fmt.Errorf("relative path for %s: %w", path, err)
		}
		dstPath := dstRoot
		if rel != "." {
			dstPath = filepath.Join(dstRoot, rel)
		}
		if d.IsDir() {
			if err := os.MkdirAll(dstPath, 0o755); err != nil {
				return fmt.Errorf("create dir %s: %w", dstPath, err)
			}
			return nil
		}
		if d.Type()&os.ModeSymlink != 0 {
			return fmt.Errorf("symlink work product is not allowed: %s", path)
		}
		info, err := d.Info()
		if err != nil {
			return fmt.Errorf("stat %s: %w", path, err)
		}
		if !info.Mode().IsRegular() {
			return fmt.Errorf("unsupported work-product entry %s", path)
		}
		raw, err := os.ReadFile(path)
		if err != nil {
			return fmt.Errorf("read %s: %w", path, err)
		}
		if err := os.WriteFile(dstPath, raw, info.Mode().Perm()); err != nil {
			return fmt.Errorf("write %s: %w", dstPath, err)
		}
		return nil
	})
}
