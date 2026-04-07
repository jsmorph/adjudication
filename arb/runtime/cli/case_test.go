package cli

import (
	"bytes"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestResolveExplicitCaseFilesExpandsGlob(t *testing.T) {
	dir := t.TempDir()
	first := filepath.Join(dir, "a.txt")
	second := filepath.Join(dir, "b.txt")
	if err := os.WriteFile(first, []byte("a"), 0o644); err != nil {
		t.Fatalf("write first: %v", err)
	}
	if err := os.WriteFile(second, []byte("b"), 0o644); err != nil {
		t.Fatalf("write second: %v", err)
	}

	got, err := resolveExplicitCaseFiles([]string{filepath.Join(dir, "*.txt")})
	if err != nil {
		t.Fatalf("resolveExplicitCaseFiles returned error: %v", err)
	}
	if len(got) != 2 {
		t.Fatalf("resolveExplicitCaseFiles returned %d files, want 2", len(got))
	}
	wantFirst, _ := filepath.Abs(first)
	wantSecond, _ := filepath.Abs(second)
	if got[0] != wantFirst || got[1] != wantSecond {
		t.Fatalf("resolveExplicitCaseFiles = %#v, want [%q %q]", got, wantFirst, wantSecond)
	}
}

func TestResolveExplicitCaseFilesRejectsProhibitedExtension(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "sign.sh")
	if err := os.WriteFile(path, []byte("echo hi\n"), 0o644); err != nil {
		t.Fatalf("write sign.sh: %v", err)
	}

	_, err := resolveExplicitCaseFiles([]string{path})
	if err == nil || !strings.Contains(err.Error(), "prohibited extension") {
		t.Fatalf("resolveExplicitCaseFiles error = %v, want prohibited extension error", err)
	}
}

func TestResolveExplicitCaseFilesRejectsUnmatchedGlob(t *testing.T) {
	dir := t.TempDir()
	_, err := resolveExplicitCaseFiles([]string{filepath.Join(dir, "*.txt")})
	if err == nil || !strings.Contains(err.Error(), "matched no files") {
		t.Fatalf("resolveExplicitCaseFiles error = %v, want unmatched glob error", err)
	}
}

func TestFinalVoteCountsUsesFinalRound(t *testing.T) {
	state := map[string]any{
		"case": map[string]any{
			"deliberation_round": 2,
			"council_votes": []any{
				map[string]any{"round": 1, "vote": "demonstrated"},
				map[string]any{"round": 1, "vote": "not_demonstrated"},
				map[string]any{"round": 2, "vote": "demonstrated"},
				map[string]any{"round": 2, "vote": "demonstrated"},
				map[string]any{"round": 2, "vote": "not_demonstrated"},
			},
		},
	}

	votesFor, votesAgainst := finalVoteCounts(state)
	if votesFor != 2 || votesAgainst != 1 {
		t.Fatalf("finalVoteCounts = (%d, %d), want (2, 1)", votesFor, votesAgainst)
	}
}

func TestRunCaseReportsJSONError(t *testing.T) {
	var stdout bytes.Buffer
	var stderr bytes.Buffer

	err := RunCase(nil, &stdout, &stderr)
	if err == nil {
		t.Fatal("RunCase returned nil error, want failure")
	}
	if !IsReportedError(err) {
		t.Fatalf("RunCase error = %T, want reported error", err)
	}

	var summary caseRunSummary
	if decodeErr := json.Unmarshal(stdout.Bytes(), &summary); decodeErr != nil {
		t.Fatalf("stdout is not JSON: %v\n%s", decodeErr, stdout.String())
	}
	if summary.Status != "error" {
		t.Fatalf("summary status = %q, want error", summary.Status)
	}
	if !strings.Contains(summary.Error, "--complaint and --out-dir are required") {
		t.Fatalf("summary error = %q, want missing-args message", summary.Error)
	}
	if stderr.Len() != 0 {
		t.Fatalf("stderr = %q, want empty", stderr.String())
	}
}

func TestRunCaseRejectsInvalidAttorneyModel(t *testing.T) {
	dir := t.TempDir()
	complaintPath := filepath.Join(dir, "complaint.md")
	if err := os.WriteFile(complaintPath, []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write complaint: %v", err)
	}

	var stdout bytes.Buffer
	var stderr bytes.Buffer
	err := RunCase([]string{
		"--complaint", complaintPath,
		"--out-dir", filepath.Join(dir, "out"),
		"--attorney-model", "gpt-5",
	}, &stdout, &stderr)
	if err == nil {
		t.Fatal("RunCase returned nil error, want failure")
	}
	if !IsReportedError(err) {
		t.Fatalf("RunCase error = %T, want reported error", err)
	}
	var summary caseRunSummary
	if decodeErr := json.Unmarshal(stdout.Bytes(), &summary); decodeErr != nil {
		t.Fatalf("stdout is not JSON: %v\n%s", decodeErr, stdout.String())
	}
	if summary.Status != "error" {
		t.Fatalf("summary status = %q, want error", summary.Status)
	}
	if !strings.Contains(summary.Error, "model must match ENDPOINT://MODEL[?ARGS]") {
		t.Fatalf("summary error = %q, want invalid model message", summary.Error)
	}
}

func TestRunCaseRejectsInvalidPlaintiffAttorneyModel(t *testing.T) {
	dir := t.TempDir()
	complaintPath := filepath.Join(dir, "complaint.md")
	if err := os.WriteFile(complaintPath, []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write complaint: %v", err)
	}

	var stdout bytes.Buffer
	var stderr bytes.Buffer
	err := RunCase([]string{
		"--complaint", complaintPath,
		"--out-dir", filepath.Join(dir, "out"),
		"--plaintiff-attorney-model", "gpt-5",
	}, &stdout, &stderr)
	if err == nil {
		t.Fatal("RunCase returned nil error, want failure")
	}
	if !IsReportedError(err) {
		t.Fatalf("RunCase error = %T, want reported error", err)
	}
	var summary caseRunSummary
	if decodeErr := json.Unmarshal(stdout.Bytes(), &summary); decodeErr != nil {
		t.Fatalf("stdout is not JSON: %v\n%s", decodeErr, stdout.String())
	}
	if summary.Status != "error" {
		t.Fatalf("summary status = %q, want error", summary.Status)
	}
	if !strings.Contains(summary.Error, "model must match ENDPOINT://MODEL[?ARGS]") {
		t.Fatalf("summary error = %q, want invalid model message", summary.Error)
	}
}

func TestRunCaseRejectsConflictingPlaintiffACPSettings(t *testing.T) {
	dir := t.TempDir()
	complaintPath := filepath.Join(dir, "complaint.md")
	if err := os.WriteFile(complaintPath, []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write complaint: %v", err)
	}

	var stdout bytes.Buffer
	var stderr bytes.Buffer
	err := RunCase([]string{
		"--complaint", complaintPath,
		"--out-dir", filepath.Join(dir, "out"),
		"--plaintiff-acp-command", "/tmp/acp",
		"--plaintiff-acp-endpoint", "tcp://127.0.0.1:7000",
	}, &stdout, &stderr)
	if err == nil {
		t.Fatal("RunCase returned nil error, want failure")
	}
	if !IsReportedError(err) {
		t.Fatalf("RunCase error = %T, want reported error", err)
	}
	var summary caseRunSummary
	if decodeErr := json.Unmarshal(stdout.Bytes(), &summary); decodeErr != nil {
		t.Fatalf("stdout is not JSON: %v\n%s", decodeErr, stdout.String())
	}
	if summary.Status != "error" {
		t.Fatalf("summary status = %q, want error", summary.Status)
	}
	if !strings.Contains(summary.Error, "cannot set both --plaintiff-acp-command and --plaintiff-acp-endpoint") {
		t.Fatalf("summary error = %q, want conflicting ACP config message", summary.Error)
	}
}

func TestReportedErrorWrapsOriginalError(t *testing.T) {
	base := errors.New("boom")
	err := &ReportedError{Err: base}
	if !errors.Is(err, base) {
		t.Fatal("ReportedError does not unwrap to original error")
	}
}
