package cli

import (
	"bytes"
	"encoding/json"
	"testing"

	"adjudication/arbd/runtime/runner"
)

func TestBuildCaseSuccessSummaryUsesAnswers(t *testing.T) {
	summary := buildCaseSuccessSummary(runner.Result{
		RunID:   "run-1",
		Answers: map[string]int{"C1": 72},
	}, "out/demo")
	if summary.Status != "ok" {
		t.Fatalf("summary status = %q, want ok", summary.Status)
	}
	if summary.Answers["C1"] != 72 {
		t.Fatalf("summary answers = %#v", summary.Answers)
	}
}

func TestWriteCaseSummaryWritesJSON(t *testing.T) {
	var buf bytes.Buffer
	if err := writeCaseSummary(&buf, caseRunSummary{
		Status:  "ok",
		Answers: map[string]int{"C1": 72},
	}); err != nil {
		t.Fatalf("writeCaseSummary returned error: %v", err)
	}
	var decoded caseRunSummary
	if err := json.Unmarshal(buf.Bytes(), &decoded); err != nil {
		t.Fatalf("summary is not valid JSON: %v", err)
	}
	if decoded.Answers["C1"] != 72 {
		t.Fatalf("decoded summary = %#v", decoded)
	}
}
