package cli

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

func TestRunAttorneyToolsIncludesWorkspaceWriter(t *testing.T) {
	var stdout bytes.Buffer
	var stderr bytes.Buffer

	if err := RunAttorneyTools([]string{"--include-workspace-writer"}, &stdout, &stderr); err != nil {
		t.Fatalf("RunAttorneyTools returned error: %v", err)
	}
	if stderr.Len() != 0 {
		t.Fatalf("stderr = %q, want empty", stderr.String())
	}
	var tools []map[string]any
	if err := json.Unmarshal(stdout.Bytes(), &tools); err != nil {
		t.Fatalf("stdout is not JSON: %v\n%s", err, stdout.String())
	}
	var found bool
	for _, tool := range tools {
		if tool["method"] == "_aar/write_case_file" {
			found = true
			break
		}
	}
	if !found {
		t.Fatalf("tool list missing _aar/write_case_file: %#v", tools)
	}
}

func TestRunStageAttorneyPIHomeWritesFiles(t *testing.T) {
	commonRoot := t.TempDir()
	etcDir := filepath.Join(commonRoot, "etc")
	if err := os.MkdirAll(etcDir, 0o755); err != nil {
		t.Fatalf("mkdir etc: %v", err)
	}
	if err := os.WriteFile(filepath.Join(etcDir, "pi-settings.xproxy.json"), []byte("{\"defaultProvider\":\"xproxy\",\"defaultModel\":\"openai://gpt-5\"}\n"), 0o644); err != nil {
		t.Fatalf("write settings: %v", err)
	}
	if err := os.WriteFile(filepath.Join(etcDir, "pi-models.xproxy.json"), []byte("{\"providers\":{\"xproxy\":{\"models\":[{\"id\":\"openai://gpt-5\",\"name\":\"OpenAI GPT-5\"}]}}}\n"), 0o644); err != nil {
		t.Fatalf("write models: %v", err)
	}
	targetDir := filepath.Join(t.TempDir(), "pi-home")

	var stdout bytes.Buffer
	var stderr bytes.Buffer
	err := RunStageAttorneyPIHome([]string{
		"--dir", targetDir,
		"--common-root", commonRoot,
		"--model", "openai://gpt-5?tools=search",
	}, &stdout, &stderr)
	if err != nil {
		t.Fatalf("RunStageAttorneyPIHome returned error: %v", err)
	}
	if stdout.Len() != 0 {
		t.Fatalf("stdout = %q, want empty", stdout.String())
	}
	if stderr.Len() != 0 {
		t.Fatalf("stderr = %q, want empty", stderr.String())
	}
	for _, rel := range []string{
		filepath.Join(".pi", "agent", "settings.json"),
		filepath.Join(".pi", "agent", "models.json"),
		filepath.Join(".pi", "agent", "auth.json"),
	} {
		if _, err := os.Stat(filepath.Join(targetDir, rel)); err != nil {
			t.Fatalf("expected %s to exist: %v", rel, err)
		}
	}
}
