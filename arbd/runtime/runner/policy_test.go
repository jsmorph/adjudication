package runner

import "testing"

func TestValidatePolicyRejectsBlankJudgmentStandard(t *testing.T) {
	policy := DefaultPolicy()
	policy.JudgmentStandard = ""
	if err := ValidatePolicy(policy); err == nil {
		t.Fatal("ValidatePolicy returned nil error, want failure")
	}
}

func TestCurrentAnswersBuildsMemberMap(t *testing.T) {
	state := map[string]any{
		"case": map[string]any{
			"council_answers": []any{
				map[string]any{"member_id": "C1", "answer": 72},
				map[string]any{"member_id": "C2", "answer": 45},
			},
		},
	}
	answers := currentAnswers(state)
	if len(answers) != 2 || answers["C1"] != 72 || answers["C2"] != 45 {
		t.Fatalf("currentAnswers = %#v", answers)
	}
}
