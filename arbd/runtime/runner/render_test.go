package runner

import (
	"strings"
	"testing"

	"adjudication/arbd/runtime/spec"
)

func TestRenderDigestShowsAnswerMap(t *testing.T) {
	result := Result{
		Complaint:        spec.Complaint{Question: "Q"},
		JudgmentStandard: "Answer with one integer.",
		Answers:          map[string]int{"C1": 72, "C2": 45},
		Council: []CouncilSeat{
			{MemberID: "C1", Model: "m1", PersonaFile: "p1"},
			{MemberID: "C2", Model: "m2", PersonaFile: "p2"},
		},
		FinalState: map[string]any{
			"case": map[string]any{
				"phase": "closed",
				"openings": []any{
					map[string]any{"role": "plaintiff", "text": "opening"},
				},
				"arguments":         []any{},
				"rebuttals":         []any{},
				"surrebuttals":      []any{},
				"closings":          []any{},
				"offered_files":     []any{},
				"technical_reports": []any{},
				"council_answers": []any{
					map[string]any{"round": 1, "member_id": "C1", "answer": 72, "rationale": "R1"},
					map[string]any{"round": 1, "member_id": "C2", "answer": 45, "rationale": "R2"},
				},
			},
		},
	}
	out := renderDigest(result, &runContext{})
	if !strings.Contains(out, "- C1: 72") || !strings.Contains(out, "- C2: 45") {
		t.Fatalf("digest missing answer map:\n%s", out)
	}
	if !strings.Contains(out, "## Council Answers") {
		t.Fatalf("digest missing council answers section:\n%s", out)
	}
}
