package runner

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"adjudication/arb/runtime/lean"
	"adjudication/arb/runtime/spec"
)

func TestLoadCaseFiles(t *testing.T) {
	dir := t.TempDir()
	write := func(name string, body string) {
		t.Helper()
		if err := os.WriteFile(filepath.Join(dir, name), []byte(body), 0o644); err != nil {
			t.Fatalf("write %s: %v", name, err)
		}
	}
	write("situation.md", "# Proposition\n\nP\n")
	write("complaint.md", "# Proposition\n\nP\n")
	write("instructions.txt", "hello")
	write("samantha_public.pem", "pem")

	files, err := loadCaseFiles(dir)
	if err != nil {
		t.Fatalf("loadCaseFiles returned error: %v", err)
	}
	if len(files) != 2 {
		t.Fatalf("loadCaseFiles returned %d files, want 2", len(files))
	}
	if files[0].FileID != "instructions.txt" || files[1].FileID != "samantha_public.pem" {
		t.Fatalf("unexpected files: %#v", files)
	}
}

func TestLoadCaseFilesPreservesTrailingNewline(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "situation.md"), []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write situation: %v", err)
	}
	if err := os.WriteFile(filepath.Join(dir, "complaint.md"), []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write complaint: %v", err)
	}
	body := "line one\nline two\n"
	if err := os.WriteFile(filepath.Join(dir, "confession.txt"), []byte(body), 0o644); err != nil {
		t.Fatalf("write confession: %v", err)
	}

	files, err := loadCaseFiles(dir)
	if err != nil {
		t.Fatalf("loadCaseFiles returned error: %v", err)
	}
	if len(files) != 1 {
		t.Fatalf("loadCaseFiles returned %d files, want 1", len(files))
	}
	if files[0].Text != body {
		t.Fatalf("file text = %q, want %q", files[0].Text, body)
	}
}

func TestLoadCaseFilesAllowsNoUsableFiles(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "situation.md"), []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write situation: %v", err)
	}
	if err := os.WriteFile(filepath.Join(dir, "complaint.md"), []byte("# Proposition\n\nP\n"), 0o644); err != nil {
		t.Fatalf("write complaint: %v", err)
	}
	if err := os.WriteFile(filepath.Join(dir, "README.md"), []byte("note\n"), 0o644); err != nil {
		t.Fatalf("write readme: %v", err)
	}

	files, err := loadCaseFiles(dir)
	if err != nil {
		t.Fatalf("loadCaseFiles returned error: %v", err)
	}
	if len(files) != 0 {
		t.Fatalf("loadCaseFiles returned %d files, want 0", len(files))
	}
}

func TestLoadCaseFilesFromPaths(t *testing.T) {
	dir := t.TempDir()
	txtPath := filepath.Join(dir, "instructions.txt")
	pemPath := filepath.Join(dir, "samantha_public.pem")
	if err := os.WriteFile(txtPath, []byte("hello\n"), 0o644); err != nil {
		t.Fatalf("write instructions: %v", err)
	}
	if err := os.WriteFile(pemPath, []byte("pem"), 0o644); err != nil {
		t.Fatalf("write pem: %v", err)
	}

	files, err := loadCaseFilesFromPaths([]string{pemPath, txtPath})
	if err != nil {
		t.Fatalf("loadCaseFilesFromPaths returned error: %v", err)
	}
	if len(files) != 2 {
		t.Fatalf("loadCaseFilesFromPaths returned %d files, want 2", len(files))
	}
	if files[0].FileID != "instructions.txt" || files[1].FileID != "samantha_public.pem" {
		t.Fatalf("unexpected files: %#v", files)
	}
	if files[0].Text != "hello\n" {
		t.Fatalf("instructions text = %q, want hello\\n", files[0].Text)
	}
}

func TestLoadCaseFilesFromPathsRejectsDuplicateBaseNames(t *testing.T) {
	dir := t.TempDir()
	left := filepath.Join(dir, "a")
	right := filepath.Join(dir, "b")
	if err := os.MkdirAll(left, 0o755); err != nil {
		t.Fatalf("mkdir left: %v", err)
	}
	if err := os.MkdirAll(right, 0o755); err != nil {
		t.Fatalf("mkdir right: %v", err)
	}
	leftPath := filepath.Join(left, "shared.txt")
	rightPath := filepath.Join(right, "shared.txt")
	if err := os.WriteFile(leftPath, []byte("left"), 0o644); err != nil {
		t.Fatalf("write left: %v", err)
	}
	if err := os.WriteFile(rightPath, []byte("right"), 0o644); err != nil {
		t.Fatalf("write right: %v", err)
	}

	_, err := loadCaseFilesFromPaths([]string{leftPath, rightPath})
	if err == nil || !strings.Contains(err.Error(), "duplicate case file name") {
		t.Fatalf("loadCaseFilesFromPaths error = %v, want duplicate name error", err)
	}
}

func TestValidateAttorneyPayload(t *testing.T) {
	policy := DefaultPolicy()
	fileByID := map[string]CaseFile{
		"instructions.txt": {FileID: "instructions.txt", SizeBytes: 128},
	}
	valid := map[string]any{
		"text": "argument",
		"offered_files": []any{
			map[string]any{"file_id": "instructions.txt", "label": "PX-1"},
		},
		"technical_reports": []any{
			map[string]any{"title": "Verification", "summary": "Verified OK."},
		},
	}
	if err := validateAttorneyPayload("submit_argument", valid, fileByID, policy); err != nil {
		t.Fatalf("validateAttorneyPayload returned error: %v", err)
	}
	invalid := map[string]any{
		"text": "",
	}
	if err := validateAttorneyPayload("submit_argument", invalid, fileByID, policy); err == nil {
		t.Fatalf("expected validation error for empty text")
	}
	badFile := map[string]any{
		"text": "argument",
		"offered_files": []any{
			map[string]any{"file_id": "missing.txt"},
		},
	}
	if err := validateAttorneyPayload("submit_argument", badFile, fileByID, policy); err == nil {
		t.Fatalf("expected validation error for missing file")
	}
}

func TestCouncilMemberIDFromOpportunity(t *testing.T) {
	opportunity := Opportunity{ID: "deliberation:2:C4"}
	if got := councilMemberIDFromOpportunity(opportunity); got != "C4" {
		t.Fatalf("councilMemberIDFromOpportunity = %q, want C4", got)
	}
}

func TestValidateAttorneyPayloadAllowsSupplementalMaterialsInRebuttal(t *testing.T) {
	policy := DefaultPolicy()
	fileByID := map[string]CaseFile{
		"instructions.txt": {FileID: "instructions.txt", SizeBytes: 128},
	}
	rebuttal := map[string]any{
		"text": "reply",
		"offered_files": []any{
			map[string]any{"file_id": "instructions.txt"},
		},
		"technical_reports": []any{
			map[string]any{"title": "Check", "summary": "Done."},
		},
	}
	if err := validateAttorneyPayload("submit_rebuttal", rebuttal, fileByID, policy); err != nil {
		t.Fatalf("expected rebuttal supplemental materials to be accepted: %v", err)
	}
}

func TestValidateAttorneyPayloadRejectsSupplementalMaterialsInSurrebuttal(t *testing.T) {
	policy := DefaultPolicy()
	fileByID := map[string]CaseFile{
		"instructions.txt": {FileID: "instructions.txt", SizeBytes: 128},
	}
	surrebuttal := map[string]any{
		"text": "reply",
		"offered_files": []any{
			map[string]any{"file_id": "instructions.txt"},
		},
		"technical_reports": []any{
			map[string]any{"title": "Check", "summary": "Done."},
		},
	}
	if err := validateAttorneyPayload("submit_surrebuttal", surrebuttal, fileByID, policy); err == nil {
		t.Fatalf("expected surrebuttal technical_reports to be rejected")
	}
}

func TestValidateAttorneyPayloadRejectsOversizeExhibit(t *testing.T) {
	policy := DefaultPolicy()
	policy.MaxExhibitBytes = 16
	fileByID := map[string]CaseFile{
		"instructions.txt": {FileID: "instructions.txt", SizeBytes: 32},
	}
	payload := map[string]any{
		"text": "argument",
		"offered_files": []any{
			map[string]any{"file_id": "instructions.txt"},
		},
	}
	if err := validateAttorneyPayload("submit_argument", payload, fileByID, policy); err == nil {
		t.Fatalf("expected oversize exhibit to be rejected")
	}
}

func TestValidateAttorneyPayloadRejectsTooManyReports(t *testing.T) {
	policy := DefaultPolicy()
	policy.MaxReportsPerFiling = 1
	fileByID := map[string]CaseFile{}
	payload := map[string]any{
		"text": "argument",
		"technical_reports": []any{
			map[string]any{"title": "One", "summary": "A"},
			map[string]any{"title": "Two", "summary": "B"},
		},
	}
	if err := validateAttorneyPayload("submit_argument", payload, fileByID, policy); err == nil {
		t.Fatalf("expected per-filing report limit to be enforced")
	}
}

func TestValidateAttorneyPayloadAgainstStateRejectsOverlongRebuttal(t *testing.T) {
	policy := DefaultPolicy()
	rc := &runContext{
		cfg: Config{Policy: policy},
		state: map[string]any{
			"case": map[string]any{
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	payload := map[string]any{
		"text": strings.Repeat("a", policy.MaxRebuttalChars+1),
	}
	err := rc.validateAttorneyPayloadAgainstState(Opportunity{
		Role:  "plaintiff",
		Phase: "rebuttals",
	}, "submit_rebuttal", payload)
	if err == nil {
		t.Fatalf("expected rebuttal length error")
	}
	if !strings.Contains(err.Error(), "rebuttal exceeds character limit") || !strings.Contains(err.Error(), fmt.Sprintf("got %d", policy.MaxRebuttalChars+1)) {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestValidateAttorneyPayloadAgainstStateRejectsSideReportOverflow(t *testing.T) {
	policy := DefaultPolicy()
	existing := []map[string]any{
		{"role": "plaintiff", "title": "One", "summary": "A"},
		{"role": "plaintiff", "title": "Two", "summary": "B"},
		{"role": "plaintiff", "title": "Three", "summary": "C"},
	}
	rc := &runContext{
		cfg: Config{Policy: policy},
		state: map[string]any{
			"case": map[string]any{
				"offered_files":     []map[string]any{},
				"technical_reports": existing,
			},
		},
	}
	payload := map[string]any{
		"text": "reply",
		"technical_reports": []any{
			map[string]any{"title": "Four", "summary": "D"},
			map[string]any{"title": "Five", "summary": "E"},
		},
	}
	err := rc.validateAttorneyPayloadAgainstState(Opportunity{
		Role:  "plaintiff",
		Phase: "rebuttals",
	}, "submit_rebuttal", payload)
	if err == nil {
		t.Fatalf("expected side report overflow error")
	}
	if !strings.Contains(err.Error(), "technical_reports for this side exceed limit of 4 (3 already used, 2 attempted, 1 remaining)") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestValidatePolicyRejectsImpossibleThreshold(t *testing.T) {
	policy := DefaultPolicy()
	policy.RequiredVotesForDecision = 6
	if err := ValidatePolicy(policy); err == nil {
		t.Fatalf("expected policy validation error")
	}
}

func TestValidatePolicyRejectsNonStrictMajorityThreshold(t *testing.T) {
	policy := DefaultPolicy()
	policy.CouncilSize = 4
	policy.RequiredVotesForDecision = 2
	err := ValidatePolicy(policy)
	if err == nil {
		t.Fatalf("expected policy validation error")
	}
	if got := err.Error(); got != "policy.required_votes_for_decision must be a strict majority of council_size" {
		t.Fatalf("unexpected validation error: %s", got)
	}
}

func TestValidateRuntimeLimitsRejectsZeroResponseLimit(t *testing.T) {
	runtime := DefaultRuntimeLimits()
	runtime.MaxResponseBytes = 0
	if err := ValidateRuntimeLimits(runtime); err == nil {
		t.Fatalf("expected runtime validation error")
	}
}

func TestBuildAttorneyPromptStatesCouncilForum(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy: DefaultPolicy(),
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":             "openings",
				"openings":          []map[string]any{},
				"arguments":         []map[string]any{},
				"rebuttals":         []map[string]any{},
				"surrebuttals":      []map[string]any{},
				"closings":          []map[string]any{},
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "openings:plaintiff",
		Role:         "plaintiff",
		Phase:        "openings",
		Objective:    "plaintiff opening statement",
		AllowedTools: []string{"record_opening_statement"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "no judge, no clerk, and no voir dire") {
		t.Fatalf("prompt did not state the forum shape:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Address the council, not a judge.") {
		t.Fatalf("prompt did not direct counsel to address the council:\n%s", prompt)
	}
	if !strings.Contains(prompt, "record contains only the proposition and the standard of evidence") {
		t.Fatalf("prompt did not state the opening record limit:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Do not invent facts, sources, quotations, files, analyses, or results.") {
		t.Fatalf("prompt did not forbid fabrication:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Text limit for this submission: 4000 characters.") {
		t.Fatalf("prompt did not state the opening text limit:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Target length for the first submission: 3000 characters or less.") {
		t.Fatalf("prompt did not state the opening target length:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Native web search through the model is available.") {
		t.Fatalf("prompt did not state search availability:\n%s", prompt)
	}
	if strings.Contains(prompt, "Visible case files:") {
		t.Fatalf("opening prompt should not list visible case files:\n%s", prompt)
	}
}

func TestBuildAttorneyPromptStatesWhenSearchIsUnavailable(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy:        DefaultPolicy(),
			AttorneyModel: "openai://gpt-5",
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":             "openings",
				"openings":          []map[string]any{},
				"arguments":         []map[string]any{},
				"rebuttals":         []map[string]any{},
				"surrebuttals":      []map[string]any{},
				"closings":          []map[string]any{},
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "openings:plaintiff",
		Role:         "plaintiff",
		Phase:        "openings",
		Objective:    "plaintiff opening statement",
		AllowedTools: []string{"record_opening_statement"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Native web search through the model is not available.") {
		t.Fatalf("prompt did not state search unavailability:\n%s", prompt)
	}
}

func TestBuildAttorneyPromptIncludesWorkProductGuidance(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy:     DefaultPolicy(),
			ACPCommand: "/tmp/acp-podman.sh",
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":             "arguments",
				"openings":          []map[string]any{},
				"arguments":         []map[string]any{},
				"rebuttals":         []map[string]any{},
				"surrebuttals":      []map[string]any{},
				"closings":          []map[string]any{},
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "arguments:plaintiff",
		Role:         "plaintiff",
		Phase:        "arguments",
		Objective:    "plaintiff merits argument",
		AllowedTools: []string{"submit_argument"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Private work product: Use `/home/user/work-product/` for internal notes, timelines, source leads, adverse facts, unresolved questions, and draft analyses.") {
		t.Fatalf("prompt did not include work-product guidance:\n%s", prompt)
	}
	if !strings.Contains(prompt, "This directory is not part of the record unless you later turn material from it into an exhibit or technical report.") {
		t.Fatalf("prompt did not distinguish work product from the record:\n%s", prompt)
	}
}

func TestACPToolSpecsArePhaseSpecific(t *testing.T) {
	openingSpecs := acpToolSpecs(Opportunity{Phase: "openings"}, true)
	openingTools := make([]string, 0, len(openingSpecs))
	for _, spec := range openingSpecs {
		openingTools = append(openingTools, mapString(spec["toolName"]))
	}
	if slices.Contains(openingTools, "aar_list_case_files") || slices.Contains(openingTools, "aar_read_case_text_file") || slices.Contains(openingTools, "aar_write_case_file") {
		t.Fatalf("opening tools exposed case-file access: %#v", openingTools)
	}
	argumentSpecs := acpToolSpecs(Opportunity{Phase: "arguments"}, true)
	argumentTools := make([]string, 0, len(argumentSpecs))
	for _, spec := range argumentSpecs {
		argumentTools = append(argumentTools, mapString(spec["toolName"]))
	}
	if !slices.Contains(argumentTools, "aar_list_case_files") || !slices.Contains(argumentTools, "aar_read_case_text_file") || !slices.Contains(argumentTools, "aar_write_case_file") {
		t.Fatalf("argument tools did not expose case-file access: %#v", argumentTools)
	}
	rebuttalSpecs := acpToolSpecs(Opportunity{Phase: "rebuttals"}, true)
	rebuttalTools := make([]string, 0, len(rebuttalSpecs))
	for _, spec := range rebuttalSpecs {
		rebuttalTools = append(rebuttalTools, mapString(spec["toolName"]))
	}
	if !slices.Contains(rebuttalTools, "aar_list_case_files") || !slices.Contains(rebuttalTools, "aar_read_case_text_file") || !slices.Contains(rebuttalTools, "aar_write_case_file") {
		t.Fatalf("rebuttal tools did not expose case-file access: %#v", rebuttalTools)
	}
	var submitSpec map[string]any
	for _, spec := range argumentSpecs {
		if mapString(spec["toolName"]) == "aar_submit_decision" {
			submitSpec = spec
			break
		}
	}
	if submitSpec == nil {
		t.Fatalf("missing aar_submit_decision spec")
	}
	properties := mapAny(mapAny(submitSpec["parameters"])["properties"])
	if _, ok := properties["reason"]; ok {
		t.Fatalf("aar_submit_decision should not advertise a reason field: %#v", properties)
	}
	payload := mapAny(properties["payload"])
	if mapString(payload["type"]) != "object" {
		t.Fatalf("payload schema type = %#v, want object", payload["type"])
	}
	payloadProps := mapAny(payload["properties"])
	offeredFiles := mapAny(payloadProps["offered_files"])
	if mapString(offeredFiles["type"]) != "array" {
		t.Fatalf("offered_files schema type = %#v, want array", offeredFiles["type"])
	}
	offeredItemProps := mapAny(mapAny(offeredFiles["items"])["properties"])
	if _, ok := offeredItemProps["file_id"]; !ok {
		t.Fatalf("offered_files items missing file_id: %#v", offeredItemProps)
	}
	if _, ok := offeredItemProps["label"]; !ok {
		t.Fatalf("offered_files items missing label: %#v", offeredItemProps)
	}
	reports := mapAny(payloadProps["technical_reports"])
	if mapString(reports["type"]) != "array" {
		t.Fatalf("technical_reports schema type = %#v, want array", reports["type"])
	}
	reportItemProps := mapAny(mapAny(reports["items"])["properties"])
	if _, ok := reportItemProps["title"]; !ok {
		t.Fatalf("technical_reports items missing title: %#v", reportItemProps)
	}
	if _, ok := reportItemProps["summary"]; !ok {
		t.Fatalf("technical_reports items missing summary: %#v", reportItemProps)
	}
}

func TestBuildAttorneyPromptConstrainsArgumentExperiments(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy: DefaultPolicy(),
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		caseFiles: []CaseFile{{FileID: "instructions.txt", Name: "instructions.txt", MimeType: "text/plain", TextReadable: true}},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":             "arguments",
				"openings":          []map[string]any{},
				"arguments":         []map[string]any{},
				"rebuttals":         []map[string]any{},
				"surrebuttals":      []map[string]any{},
				"closings":          []map[string]any{},
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "arguments:plaintiff",
		Role:         "plaintiff",
		Phase:        "arguments",
		Objective:    "plaintiff merits argument",
		AllowedTools: []string{"submit_argument"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Use this phase to file the merits submission for your side.") {
		t.Fatalf("argument prompt did not define the court-owned phase objective:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Exhibits: at most 9 in this filing. This side has used 0 of 12 total, with 12 left.") {
		t.Fatalf("argument prompt did not state exhibit limits:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Technical reports: at most 3 in this filing. This side has used 0 of 4 total, with 4 left.") {
		t.Fatalf("argument prompt did not state report limits:\n%s", prompt)
	}
	if !strings.Contains(prompt, "capture it accurately and introduce it through technical_reports") {
		t.Fatalf("argument prompt did not require outside material to enter through technical reports:\n%s", prompt)
	}
	if !strings.Contains(prompt, "write the needed visible case file into the workspace first") {
		t.Fatalf("argument prompt did not instruct counsel to materialize exact file bytes:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Use only visible case file_id values in offered_files. Do not use workspace paths, downloaded filenames, or invented names there.") {
		t.Fatalf("argument prompt did not restrict offered_files to visible file ids:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Outside material that is not already a visible case file belongs in technical_reports, not offered_files.") {
		t.Fatalf("argument prompt did not distinguish technical reports from offered files:\n%s", prompt)
	}
}

func TestBuildAttorneyPromptConstrainsArgumentExperimentsWithoutSearch(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy:        DefaultPolicy(),
			AttorneyModel: "openai://gpt-5",
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		caseFiles: []CaseFile{{FileID: "instructions.txt", Name: "instructions.txt", MimeType: "text/plain", TextReadable: true}},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":             "arguments",
				"openings":          []map[string]any{},
				"arguments":         []map[string]any{},
				"rebuttals":         []map[string]any{},
				"surrebuttals":      []map[string]any{},
				"closings":          []map[string]any{},
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "arguments:plaintiff",
		Role:         "plaintiff",
		Phase:        "arguments",
		Objective:    "plaintiff merits argument",
		AllowedTools: []string{"submit_argument"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Native web search through the model is not available.") {
		t.Fatalf("argument prompt did not state search unavailability:\n%s", prompt)
	}
}

func TestBuildAttorneyPromptAllowsRebuttalSupplementalMaterials(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy: DefaultPolicy(),
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":         "rebuttals",
				"openings":      []map[string]any{},
				"arguments":     []map[string]any{},
				"rebuttals":     []map[string]any{},
				"surrebuttals":  []map[string]any{},
				"closings":      []map[string]any{},
				"offered_files": []map[string]any{},
				"technical_reports": []map[string]any{
					{"role": "plaintiff", "title": "One", "summary": "A"},
					{"role": "plaintiff", "title": "Two", "summary": "B"},
					{"role": "plaintiff", "title": "Three", "summary": "C"},
				},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "rebuttals:plaintiff",
		Role:         "plaintiff",
		Phase:        "rebuttals",
		Objective:    "plaintiff rebuttal",
		AllowedTools: []string{"submit_rebuttal", "pass_phase_opportunity"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Offer exhibits and technical reports only if they directly answer the opposing argument.") {
		t.Fatalf("rebuttal prompt did not allow targeted supplemental materials:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Text limit for this submission: 4000 characters.") {
		t.Fatalf("rebuttal prompt did not state the rebuttal text limit:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Target length for the first submission: 3000 characters or less.") {
		t.Fatalf("rebuttal prompt did not state the rebuttal target length:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Technical reports: at most 3 in this filing. This side has used 3 of 4 total, with 1 left.") {
		t.Fatalf("rebuttal prompt did not state remaining report capacity:\n%s", prompt)
	}
	if !strings.Contains(prompt, "\"offered_files\"") || !strings.Contains(prompt, "\"technical_reports\"") {
		t.Fatalf("rebuttal example payload did not show supplemental materials:\n%s", prompt)
	}
	if !strings.Contains(prompt, "write the needed visible case file into the workspace first") {
		t.Fatalf("rebuttal prompt did not instruct counsel to materialize exact file bytes:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Use offered_files only for visible case files, by file_id.") {
		t.Fatalf("rebuttal prompt did not restrict offered_files to visible file ids:\n%s", prompt)
	}
	if !strings.Contains(prompt, "introduce it through technical_reports") {
		t.Fatalf("rebuttal prompt did not require outside material to enter through technical reports:\n%s", prompt)
	}
}

func TestBuildAttorneyPromptConstrainsRebuttalWithoutSearch(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy:        DefaultPolicy(),
			AttorneyModel: "openai://gpt-5",
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"phase":             "rebuttals",
				"openings":          []map[string]any{},
				"arguments":         []map[string]any{},
				"rebuttals":         []map[string]any{},
				"surrebuttals":      []map[string]any{},
				"closings":          []map[string]any{},
				"offered_files":     []map[string]any{},
				"technical_reports": []map[string]any{},
			},
		},
	}
	prompt, err := rc.buildAttorneyPrompt(Opportunity{
		ID:           "rebuttals:plaintiff",
		Role:         "plaintiff",
		Phase:        "rebuttals",
		Objective:    "plaintiff rebuttal",
		AllowedTools: []string{"submit_rebuttal", "pass_phase_opportunity"},
	})
	if err != nil {
		t.Fatalf("buildAttorneyPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Native web search through the model is not available.") {
		t.Fatalf("rebuttal prompt did not state search unavailability:\n%s", prompt)
	}
}

func TestWriteCaseFileToWorkspace(t *testing.T) {
	t.Parallel()

	dir := t.TempDir()
	src := filepath.Join(dir, "confession.txt")
	body := "line one\nline two\n"
	if err := os.WriteFile(src, []byte(body), 0o644); err != nil {
		t.Fatalf("write source file: %v", err)
	}
	path, err := writeCaseFileToWorkspace(dir, CaseFile{
		FileID: "confession.txt",
		Name:   "confession.txt",
		Path:   src,
	})
	if err != nil {
		t.Fatalf("writeCaseFileToWorkspace returned error: %v", err)
	}
	if path != "/home/user/confession.txt" {
		t.Fatalf("workspace path = %q, want /home/user/confession.txt", path)
	}
	raw, err := os.ReadFile(filepath.Join(dir, "confession.txt"))
	if err != nil {
		t.Fatalf("read workspace file: %v", err)
	}
	if string(raw) != body {
		t.Fatalf("workspace file body = %q, want %q", string(raw), body)
	}
}

func TestBuildCouncilPromptIncludesPersonaAndRecord(t *testing.T) {
	origPromptBaseDir := promptBaseDir
	promptBaseDir = filepath.Join("..", "..", "prompts")
	defer func() { promptBaseDir = origPromptBaseDir }()
	rc := &runContext{
		cfg: Config{
			Policy: DefaultPolicy(),
		},
		complaint: spec.Complaint{
			Proposition: "P",
		},
		state: map[string]any{
			"policy": map[string]any{
				"evidence_standard": "preponderance",
			},
			"case": map[string]any{
				"deliberation_round": 2,
				"openings":           []map[string]any{{"role": "plaintiff", "text": "opening"}},
				"arguments":          []map[string]any{},
				"rebuttals":          []map[string]any{},
				"surrebuttals":       []map[string]any{},
				"closings":           []map[string]any{},
				"offered_files":      []map[string]any{},
				"technical_reports":  []map[string]any{},
				"council_votes":      []map[string]any{{"round": 1, "member_id": "C1", "vote": "demonstrated", "rationale": "r"}},
			},
		},
	}
	prompt, err := rc.buildCouncilPrompt(CouncilSeat{
		MemberID:    "C2",
		PersonaText: "Skeptical but concise.",
	}, Opportunity{ID: "deliberation:2:C2", Role: "council", Phase: "deliberation"})
	if err != nil {
		t.Fatalf("buildCouncilPrompt returned error: %v", err)
	}
	if !strings.Contains(prompt, "Persona:\nSkeptical but concise.") {
		t.Fatalf("prompt did not include persona:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Prior rounds:\nRound 1 [C1] demonstrated") {
		t.Fatalf("prompt did not include prior rounds:\n%s", prompt)
	}
	if !strings.Contains(prompt, "Call submit_council_vote with vote=demonstrated or vote=not_demonstrated.") {
		t.Fatalf("prompt did not include council instruction:\n%s", prompt)
	}
}

func TestEnsureACPSessionReusesExistingSession(t *testing.T) {
	t.Parallel()

	existing := &acpPersistentSession{sessionPath: "/tmp/existing"}
	rc := &runContext{
		acpSessions: map[string]*acpPersistentSession{
			"plaintiff": existing,
		},
	}
	session, err := rc.ensureACPSession(context.Background(), "plaintiff")
	if err != nil {
		t.Fatalf("ensureACPSession returned error: %v", err)
	}
	if session != existing {
		t.Fatalf("ensureACPSession returned %p, want existing %p", session, existing)
	}
}

func TestCloseACPSessionsClosesAndClears(t *testing.T) {
	t.Parallel()

	closed := make([]string, 0, 2)
	rc := &runContext{
		acpSessions: map[string]*acpPersistentSession{
			"defendant": {
				cleanup: func() error {
					closed = append(closed, "defendant")
					return nil
				},
			},
			"plaintiff": {
				cleanup: func() error {
					closed = append(closed, "plaintiff")
					return nil
				},
			},
		},
	}
	if err := rc.closeACPSessions(); err != nil {
		t.Fatalf("closeACPSessions returned error: %v", err)
	}
	if len(rc.acpSessions) != 0 {
		t.Fatalf("closeACPSessions left %d sessions", len(rc.acpSessions))
	}
	if got, want := closed, []string{"defendant", "plaintiff"}; !slices.Equal(got, want) {
		t.Fatalf("close order = %#v, want %#v", got, want)
	}
}

func TestIsFunctionArgumentParseError(t *testing.T) {
	t.Parallel()

	if isFunctionArgumentParseError(os.ErrInvalid) {
		t.Fatalf("unexpected parse-error match for os.ErrInvalid")
	}
	if !isFunctionArgumentParseError(fmt.Errorf("parse function arguments for submit_council_vote: unexpected end of JSON input")) {
		t.Fatalf("expected parse function arguments error to match")
	}
}

func TestIsCouncilTimeoutError(t *testing.T) {
	t.Parallel()

	if isCouncilTimeoutError(fmt.Errorf("provider failed")) {
		t.Fatalf("unexpected timeout match for generic error")
	}
	if !isCouncilTimeoutError(context.DeadlineExceeded) {
		t.Fatalf("expected context deadline exceeded to count as timeout")
	}
	if !isCouncilTimeoutError(fmt.Errorf("responses request canceled during backoff: %w", context.DeadlineExceeded)) {
		t.Fatalf("expected wrapped deadline exceeded to count as timeout")
	}
	if !isCouncilTimeoutError(fmt.Errorf("responses request failed: request timed out")) {
		t.Fatalf("expected timed out message to count as timeout")
	}
}

func TestRemoveTimedOutCouncilMemberRecordsEvent(t *testing.T) {
	t.Parallel()

	dir := t.TempDir()
	enginePath := filepath.Join(dir, "engine.sh")
	script := "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{\"ok\":true,\"state\":{\"case\":{\"phase\":\"deliberation\",\"resolution\":\"\",\"council_members\":[{\"member_id\":\"C1\",\"status\":\"timed_out\"}]}}}'\n"
	if err := os.WriteFile(enginePath, []byte(script), 0o755); err != nil {
		t.Fatalf("write engine script: %v", err)
	}
	rc := &runContext{
		cfg: Config{
			Engine:    lean.Engine{Command: []string{enginePath}},
			OutputDir: dir,
		},
		state: map[string]any{
			"case": map[string]any{
				"phase": "deliberation",
			},
		},
	}
	opportunity := Opportunity{Phase: "deliberation"}
	seat := CouncilSeat{MemberID: "C1", Model: "openrouter://openai/gpt-4o"}
	if err := rc.removeTimedOutCouncilMember(opportunity, seat, context.DeadlineExceeded); err != nil {
		t.Fatalf("removeTimedOutCouncilMember returned error: %v", err)
	}
	caseObj := mapAny(rc.state["case"])
	members := mapList(caseObj["council_members"])
	if len(members) != 1 {
		t.Fatalf("council member count = %d, want 1", len(members))
	}
	if got := mapString(members[0]["status"]); got != "timed_out" {
		t.Fatalf("member status = %q, want timed_out", got)
	}
	if len(rc.events) != 1 {
		t.Fatalf("event count = %d, want 1", len(rc.events))
	}
	event := rc.events[0]
	if event.Type != "council_member_removed" {
		t.Fatalf("event type = %q, want council_member_removed", event.Type)
	}
	if got := mapString(event.Payload["member_id"]); got != "C1" {
		t.Fatalf("member_id = %q, want C1", got)
	}
	if got := mapString(event.Payload["status"]); got != "timed_out" {
		t.Fatalf("status = %q, want timed_out", got)
	}
}
