package runner

import (
	"context"
	"errors"
	"fmt"
	"math"
	"net"
	"strconv"
	"strings"

	openaiapi "adjudication/common/openai"
)

func (rc *runContext) executeCouncilOpportunity(ctx context.Context, client *openaiapi.Client, opportunity Opportunity) error {
	memberID := councilMemberIDFromOpportunity(opportunity)
	seat, ok := rc.findCouncilSeat(memberID)
	if !ok {
		return fmt.Errorf("unknown council member %q", memberID)
	}
	ctx, cancel := withTimeout(ctx, rc.cfg.Runtime.CouncilTimeout())
	defer cancel()

	prompt, err := rc.buildCouncilPrompt(seat, opportunity)
	if err != nil {
		return err
	}
	inputItems := []map[string]any{
		{"role": "system", "content": prompt},
		{"role": "user", "content": "Call submit_council_answer exactly once for this opportunity."},
	}
	tools := []map[string]any{
		{
			"type":        "function",
			"name":        "submit_council_answer",
			"description": "Submit one council answer for the current deliberation opportunity.",
			"parameters": map[string]any{
				"type": "object",
				"properties": map[string]any{
					"member_id": map[string]any{"type": "string"},
					"answer":    map[string]any{"type": "string"},
					"rationale": map[string]any{"type": "string"},
				},
				"required":             []string{"member_id", "answer", "rationale"},
				"additionalProperties": false,
			},
		},
	}
	prevID := ""
	invalidAttempts := 0
	invalidAttemptReasons := make([]string, 0)
	recordInvalidAttempt := func(reason string) {
		invalidAttempts++
		invalidAttemptReasons = append(invalidAttemptReasons, strings.TrimSpace(reason))
	}
	maxOutputTokens := rc.cfg.Runtime.CouncilMaxOutputTokens
	for invalidAttempts < rc.cfg.Runtime.InvalidAttemptLimit {
		resp, err := client.CreateResponseWithMaxOutputTokens(
			ctx,
			seat.Model,
			inputItems,
			tools,
			prevID,
			nil,
			&maxOutputTokens,
		)
		if err != nil {
			if isFunctionArgumentParseError(err) {
				recordInvalidAttempt(err.Error())
				inputItems = append(inputItems, map[string]any{
					"role":    "user",
					"content": "The previous tool call arguments were malformed. Call submit_council_answer exactly once with valid JSON arguments and keep the rationale brief.",
				})
				continue
			}
			if isCouncilTimeoutError(err) {
				return rc.removeTimedOutCouncilMember(opportunity, seat, err)
			}
			return err
		}
		if size, err := jsonPayloadSize(resp); err != nil {
			return err
		} else if size > rc.cfg.Runtime.MaxResponseBytes {
			return fmt.Errorf("council response exceeded byte limit of %d", rc.cfg.Runtime.MaxResponseBytes)
		}
		prevID = resp.ResponseID
		if len(resp.ToolCalls) != 1 {
			recordInvalidAttempt("Call submit_council_answer exactly once.")
			inputItems = append(inputItems, map[string]any{
				"role":    "user",
				"content": "Call submit_council_answer exactly once.",
			})
			continue
		}
		call := resp.ToolCalls[0]
		if call.Name != "submit_council_answer" {
			recordInvalidAttempt("The only allowed tool is submit_council_answer.")
			inputItems = append(inputItems, map[string]any{
				"role":    "user",
				"content": "The only allowed tool is submit_council_answer.",
			})
			continue
		}
		payload := cloneMap(call.Arguments)
		payload["member_id"] = memberID
		normalizedPayload, err := normalizeCouncilAnswerPayload(payload)
		if err != nil {
			recordInvalidAttempt(err.Error())
			inputItems = append(inputItems, map[string]any{
				"role":    "user",
				"content": err.Error(),
			})
			continue
		}
		stepResp, err := rc.cfg.Engine.Step(rc.state, "submit_council_answer", "council", normalizedPayload)
		if err != nil {
			return err
		}
		if ok, _ := stepResp["ok"].(bool); !ok {
			reason := mapString(stepResp["error"])
			recordInvalidAttempt(reason)
			inputItems = append(inputItems, map[string]any{
				"role":    "user",
				"content": reason,
			})
			continue
		}
		rc.state = mapAny(stepResp["state"])
		return rc.recordEvent("council_answer", "council", opportunity.Phase, map[string]any{
			"member_id": memberID,
			"model":     seat.Model,
			"payload":   normalizedPayload,
		})
	}
	return formatInvalidAttemptLimitError(fmt.Sprintf("council member %s", memberID), invalidAttemptReasons)
}

func normalizeCouncilAnswerPayload(payload map[string]any) (map[string]any, error) {
	answer, err := normalizeCouncilAnswerValue(payload["answer"])
	if err != nil {
		return nil, err
	}
	if mapString(payload["rationale"]) == "" {
		return nil, fmt.Errorf("submit_council_answer requires a rationale")
	}
	payload["answer"] = answer
	return payload, nil
}

func normalizeCouncilAnswerValue(value any) (int, error) {
	switch v := value.(type) {
	case int:
		return validateCouncilAnswerRange(v)
	case int64:
		return validateCouncilAnswerRange(int(v))
	case float64:
		if math.Trunc(v) != v {
			return 0, fmt.Errorf("submit_council_answer answer must be a whole number from 0 through 100")
		}
		return validateCouncilAnswerRange(int(v))
	case string:
		n, err := strconv.Atoi(strings.TrimSpace(v))
		if err != nil {
			return 0, fmt.Errorf("submit_council_answer answer must be a whole number from 0 through 100")
		}
		return validateCouncilAnswerRange(n)
	default:
		return 0, fmt.Errorf("submit_council_answer answer must be a whole number from 0 through 100")
	}
}

func validateCouncilAnswerRange(answer int) (int, error) {
	if answer < 0 || answer > 100 {
		return 0, fmt.Errorf("submit_council_answer answer must be a whole number from 0 through 100")
	}
	return answer, nil
}

func (rc *runContext) removeTimedOutCouncilMember(opportunity Opportunity, seat CouncilSeat, cause error) error {
	memberID := seat.MemberID
	stepResp, err := rc.cfg.Engine.Step(rc.state, "remove_council_member", "system", map[string]any{
		"member_id": memberID,
		"status":    "timed_out",
	})
	if err != nil {
		return err
	}
	if ok, _ := stepResp["ok"].(bool); !ok {
		return fmt.Errorf("remove_council_member rejected: %s", mapString(stepResp["error"]))
	}
	rc.state = mapAny(stepResp["state"])
	return rc.recordEvent("council_member_removed", "system", opportunity.Phase, map[string]any{
		"member_id": memberID,
		"model":     seat.Model,
		"status":    "timed_out",
		"cause":     cause.Error(),
	})
}

func (rc *runContext) findCouncilSeat(memberID string) (CouncilSeat, bool) {
	for _, seat := range rc.council {
		if seat.MemberID == memberID {
			return seat, true
		}
	}
	return CouncilSeat{}, false
}

func councilMemberIDFromOpportunity(opportunity Opportunity) string {
	parts := strings.Split(opportunity.ID, ":")
	if len(parts) == 3 {
		return strings.TrimSpace(parts[2])
	}
	return ""
}

func (rc *runContext) buildCouncilPrompt(seat CouncilSeat, _ Opportunity) (string, error) {
	personaSection := ""
	if strings.TrimSpace(seat.PersonaText) != "" {
		personaSection = "Persona:\n" + strings.TrimSpace(seat.PersonaText) + "\n"
	}
	return renderPromptFile("council.md", map[string]string{
		"MEMBER_ID":          seat.MemberID,
		"DELIBERATION_ROUND": fmt.Sprintf("%v", mapAny(rc.state["case"])["deliberation_round"]),
		"QUESTION":           rc.complaint.Question,
		"JUDGMENT_STANDARD":  currentJudgmentStandard(rc.state, rc.cfg.Policy),
		"PERSONA_SECTION":    personaSection,
		"RECORD":             rc.renderCouncilRecord(),
	})
}

func isFunctionArgumentParseError(err error) bool {
	return err != nil && strings.Contains(err.Error(), "parse function arguments")
}

func isCouncilTimeoutError(err error) bool {
	if err == nil {
		return false
	}
	if errors.Is(err, context.DeadlineExceeded) {
		return true
	}
	var netErr net.Error
	if errors.As(err, &netErr) && netErr.Timeout() {
		return true
	}
	msg := strings.ToLower(err.Error())
	return strings.Contains(msg, "deadline exceeded") || strings.Contains(msg, "timeout") || strings.Contains(msg, "timed out")
}

func (rc *runContext) renderCouncilRecord() string {
	caseObj := mapAny(rc.state["case"])
	sections := []string{
		"Openings:\n" + renderFilingList(mapList(caseObj["openings"])),
		"Arguments:\n" + renderFilingList(mapList(caseObj["arguments"])),
		"Rebuttals:\n" + renderFilingList(mapList(caseObj["rebuttals"])),
		"Surrebuttals:\n" + renderFilingList(mapList(caseObj["surrebuttals"])),
		"Closings:\n" + renderFilingList(mapList(caseObj["closings"])),
		"Exhibits:\n" + rc.renderExhibits(mapList(caseObj["offered_files"])),
		"Technical reports:\n" + renderReports(mapList(caseObj["technical_reports"])),
	}
	prior := rc.renderPriorAnswers(mapList(caseObj["council_answers"]), intNumber(caseObj["deliberation_round"]))
	if prior != "" {
		sections = append(sections, "Prior rounds:\n"+prior)
	}
	return strings.Join(sections, "\n\n")
}

func renderFilingList(items []map[string]any) string {
	if len(items) == 0 {
		return "(none)"
	}
	lines := make([]string, 0, len(items))
	for _, item := range items {
		lines = append(lines, fmt.Sprintf("[%s] %s", mapString(item["role"]), mapString(item["text"])))
	}
	return strings.Join(lines, "\n\n")
}

func renderReports(items []map[string]any) string {
	if len(items) == 0 {
		return "(none)"
	}
	lines := make([]string, 0, len(items))
	for _, item := range items {
		lines = append(lines, fmt.Sprintf("[%s] %s\n%s", mapString(item["role"]), mapString(item["title"]), mapString(item["summary"])))
	}
	return strings.Join(lines, "\n\n")
}

func (rc *runContext) renderExhibits(items []map[string]any) string {
	return rc.renderExhibitBodies(items)
}

func (rc *runContext) renderExhibitBodies(items []map[string]any) string {
	if len(items) == 0 {
		return "(none)"
	}
	lines := make([]string, 0, len(items))
	for _, item := range items {
		fileID := mapString(item["file_id"])
		label := mapString(item["label"])
		if label == "" {
			label = fileID
		}
		file, ok := rc.fileByID[fileID]
		if !ok {
			lines = append(lines, fmt.Sprintf("[%s] %s\n(unavailable file)", mapString(item["role"]), label))
			continue
		}
		body := "(binary or non-text file)"
		if file.TextReadable {
			body = file.Text
		}
		lines = append(lines, fmt.Sprintf("[%s] %s\n%s", mapString(item["role"]), label, body))
	}
	return strings.Join(lines, "\n\n")
}

func (rc *runContext) renderExhibitIndex(items []map[string]any) string {
	if len(items) == 0 {
		return "(none)"
	}
	lines := make([]string, 0, len(items))
	for _, item := range items {
		fileID := mapString(item["file_id"])
		label := mapString(item["label"])
		phase := mapString(item["phase"])
		role := mapString(item["role"])
		name := fileID
		if file, ok := rc.fileByID[fileID]; ok && strings.TrimSpace(file.Name) != "" {
			name = file.Name
		}
		if label == "" {
			lines = append(lines, fmt.Sprintf("[%s %s] %s", role, phase, name))
			continue
		}
		lines = append(lines, fmt.Sprintf("[%s %s] %s: %s", role, phase, label, name))
	}
	return strings.Join(lines, "\n")
}

func (rc *runContext) renderPriorAnswers(answers []map[string]any, currentRound int) string {
	if currentRound <= 1 {
		return ""
	}
	lines := make([]string, 0)
	for _, answer := range answers {
		round := intNumber(answer["round"])
		if round >= currentRound {
			continue
		}
		lines = append(lines, fmt.Sprintf("Round %d [%s] %d\n%s", round, mapString(answer["member_id"]), intNumber(answer["answer"]), mapString(answer["rationale"])))
	}
	return strings.Join(lines, "\n\n")
}

func intNumber(value any) int {
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
