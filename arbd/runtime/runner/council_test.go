package runner

import "testing"

func TestNormalizeCouncilAnswerValueAcceptsIntegerString(t *testing.T) {
	answer, err := normalizeCouncilAnswerValue("60")
	if err != nil {
		t.Fatalf("normalizeCouncilAnswerValue returned error: %v", err)
	}
	if answer != 60 {
		t.Fatalf("answer = %d, want 60", answer)
	}
}

func TestNormalizeCouncilAnswerValueRejectsFraction(t *testing.T) {
	if _, err := normalizeCouncilAnswerValue(60.5); err == nil {
		t.Fatal("normalizeCouncilAnswerValue returned nil error, want failure")
	}
}
