package runner

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"time"
)

func DefaultPolicy() Policy {
	return Policy{
		CouncilSize:              5,
		EvidenceStandard:         "Preponderance of the evidence.",
		RequiredVotesForDecision: 3,
		MaxDeliberationRounds:    3,
		MaxOpeningChars:          4000,
		MaxArgumentChars:         6000,
		MaxRebuttalChars:         4000,
		MaxSurrebuttalChars:      4000,
		MaxClosingChars:          5000,
		MaxExhibitsPerFiling:     9,
		MaxExhibitsPerSide:       12,
		MaxExhibitBytes:          128 * 1024,
		MaxReportsPerFiling:      3,
		MaxReportsPerSide:        4,
		MaxReportTitleBytes:      256,
		MaxReportSummaryBytes:    8192,
	}
}

func DefaultRuntimeLimits() RuntimeLimits {
	return RuntimeLimits{
		CouncilLLMTimeoutSeconds:  240,
		AttorneyACPTimeoutSeconds: 900,
		MaxResponseBytes:          128 * 1024,
		InvalidAttemptLimit:       3,
		CouncilMaxOutputTokens:    1200,
	}
}

func LoadPolicyFile(path string) (Policy, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return Policy{}, fmt.Errorf("read policy: %w", err)
	}
	policy := DefaultPolicy()
	if err := json.Unmarshal(raw, &policy); err != nil {
		return Policy{}, fmt.Errorf("parse policy: %w", err)
	}
	if err := ValidatePolicy(policy); err != nil {
		return Policy{}, err
	}
	return policy, nil
}

func ValidatePolicy(policy Policy) error {
	switch {
	case policy.CouncilSize <= 0:
		return fmt.Errorf("policy.council_size must be positive")
	case strings.TrimSpace(policy.EvidenceStandard) == "":
		return fmt.Errorf("policy.evidence_standard is required")
	case policy.RequiredVotesForDecision <= 0:
		return fmt.Errorf("policy.required_votes_for_decision must be positive")
	case policy.RequiredVotesForDecision > policy.CouncilSize:
		return fmt.Errorf("policy.required_votes_for_decision %d exceeds council_size %d", policy.RequiredVotesForDecision, policy.CouncilSize)
	case 2*policy.RequiredVotesForDecision <= policy.CouncilSize:
		return fmt.Errorf("policy.required_votes_for_decision must be a strict majority of council_size")
	case policy.MaxDeliberationRounds <= 0:
		return fmt.Errorf("policy.max_deliberation_rounds must be positive")
	case policy.MaxOpeningChars <= 0:
		return fmt.Errorf("policy.max_opening_chars must be positive")
	case policy.MaxArgumentChars <= 0:
		return fmt.Errorf("policy.max_argument_chars must be positive")
	case policy.MaxRebuttalChars <= 0:
		return fmt.Errorf("policy.max_rebuttal_chars must be positive")
	case policy.MaxSurrebuttalChars <= 0:
		return fmt.Errorf("policy.max_surrebuttal_chars must be positive")
	case policy.MaxClosingChars <= 0:
		return fmt.Errorf("policy.max_closing_chars must be positive")
	case policy.MaxExhibitsPerFiling < 0:
		return fmt.Errorf("policy.max_exhibits_per_filing must be non-negative")
	case policy.MaxExhibitsPerSide < 0:
		return fmt.Errorf("policy.max_exhibits_per_side must be non-negative")
	case policy.MaxExhibitsPerFiling > policy.MaxExhibitsPerSide:
		return fmt.Errorf("policy.max_exhibits_per_filing %d exceeds max_exhibits_per_side %d", policy.MaxExhibitsPerFiling, policy.MaxExhibitsPerSide)
	case policy.MaxExhibitBytes <= 0:
		return fmt.Errorf("policy.max_exhibit_bytes must be positive")
	case policy.MaxReportsPerFiling < 0:
		return fmt.Errorf("policy.max_reports_per_filing must be non-negative")
	case policy.MaxReportsPerSide < 0:
		return fmt.Errorf("policy.max_reports_per_side must be non-negative")
	case policy.MaxReportsPerFiling > policy.MaxReportsPerSide:
		return fmt.Errorf("policy.max_reports_per_filing %d exceeds max_reports_per_side %d", policy.MaxReportsPerFiling, policy.MaxReportsPerSide)
	case policy.MaxReportTitleBytes <= 0:
		return fmt.Errorf("policy.max_report_title_bytes must be positive")
	case policy.MaxReportSummaryBytes <= 0:
		return fmt.Errorf("policy.max_report_summary_bytes must be positive")
	default:
		return nil
	}
}

func ValidateRuntimeLimits(limits RuntimeLimits) error {
	switch {
	case limits.CouncilLLMTimeoutSeconds <= 0:
		return fmt.Errorf("runtime.council_llm_timeout_seconds must be positive")
	case limits.AttorneyACPTimeoutSeconds <= 0:
		return fmt.Errorf("runtime.attorney_acp_timeout_seconds must be positive")
	case limits.MaxResponseBytes <= 0:
		return fmt.Errorf("runtime.max_response_bytes must be positive")
	case limits.InvalidAttemptLimit <= 0:
		return fmt.Errorf("runtime.invalid_attempt_limit must be positive")
	case limits.CouncilMaxOutputTokens <= 0:
		return fmt.Errorf("runtime.council_max_output_tokens must be positive")
	default:
		return nil
	}
}

func (limits RuntimeLimits) CouncilTimeout() time.Duration {
	return time.Duration(limits.CouncilLLMTimeoutSeconds) * time.Second
}

func (limits RuntimeLimits) CouncilRequestTimeout() time.Duration {
	total := limits.CouncilTimeout()
	if total <= 90*time.Second {
		return total
	}
	return 90 * time.Second
}

func (limits RuntimeLimits) AttorneyACPTimeout() time.Duration {
	return time.Duration(limits.AttorneyACPTimeoutSeconds) * time.Second
}

func (policy Policy) StateMap() map[string]any {
	return map[string]any{
		"council_size":                policy.CouncilSize,
		"evidence_standard":           strings.TrimSpace(policy.EvidenceStandard),
		"required_votes_for_decision": policy.RequiredVotesForDecision,
		"max_deliberation_rounds":     policy.MaxDeliberationRounds,
		"max_opening_chars":           policy.MaxOpeningChars,
		"max_argument_chars":          policy.MaxArgumentChars,
		"max_rebuttal_chars":          policy.MaxRebuttalChars,
		"max_surrebuttal_chars":       policy.MaxSurrebuttalChars,
		"max_closing_chars":           policy.MaxClosingChars,
		"max_exhibits_per_filing":     policy.MaxExhibitsPerFiling,
		"max_exhibits_per_side":       policy.MaxExhibitsPerSide,
		"max_exhibit_bytes":           policy.MaxExhibitBytes,
		"max_reports_per_filing":      policy.MaxReportsPerFiling,
		"max_reports_per_side":        policy.MaxReportsPerSide,
		"max_report_title_bytes":      policy.MaxReportTitleBytes,
		"max_report_summary_bytes":    policy.MaxReportSummaryBytes,
	}
}
