package runner

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

func TestUsesPIContainerWrapper(t *testing.T) {
	t.Parallel()

	if !usesPIContainerWrapper("/tmp/acp-podman.sh") {
		t.Fatalf("expected acp-podman.sh to be recognized")
	}
	if !usesPIContainerWrapper("pi-podman.sh") {
		t.Fatalf("expected pi-podman.sh to be recognized")
	}
	if usesPIContainerWrapper("/tmp/other-command") {
		t.Fatalf("did not expect unrelated command to be recognized")
	}
}

func TestPrepareEphemeralPIHomeStagesSearchModel(t *testing.T) {
	commonRoot := t.TempDir()
	etcDir := filepath.Join(commonRoot, "etc")
	if err := os.MkdirAll(etcDir, 0o755); err != nil {
		t.Fatalf("mkdir etc: %v", err)
	}
	settings := []byte("{\"defaultProvider\":\"xproxy\",\"defaultModel\":\"openai://gpt-5\"}\n")
	models := []byte("{\"providers\":{\"xproxy\":{\"models\":[{\"id\":\"openai://gpt-5\",\"name\":\"OpenAI GPT-5\"}]}}}\n")
	if err := os.WriteFile(filepath.Join(etcDir, "pi-settings.xproxy.json"), settings, 0o644); err != nil {
		t.Fatalf("write settings: %v", err)
	}
	if err := os.WriteFile(filepath.Join(etcDir, "pi-models.xproxy.json"), models, 0o644); err != nil {
		t.Fatalf("write models: %v", err)
	}

	homeDir, cleanup, err := prepareEphemeralPIHome(commonRoot)
	if err != nil {
		t.Fatalf("prepareEphemeralPIHome returned error: %v", err)
	}
	defer func() {
		if err := cleanup(); err != nil && !os.IsNotExist(err) {
			t.Fatalf("cleanup PI home dir: %v", err)
		}
	}()

	settingsRaw, err := os.ReadFile(filepath.Join(homeDir, ".pi", "agent", "settings.json"))
	if err != nil {
		t.Fatalf("read staged settings: %v", err)
	}
	var settingsObj map[string]any
	if err := json.Unmarshal(settingsRaw, &settingsObj); err != nil {
		t.Fatalf("parse staged settings: %v", err)
	}
	if got := stringValueOrDefault(settingsObj["defaultModel"], ""); got != attorneySearchModel {
		t.Fatalf("defaultModel = %q, want %q", got, attorneySearchModel)
	}

	modelsRaw, err := os.ReadFile(filepath.Join(homeDir, ".pi", "agent", "models.json"))
	if err != nil {
		t.Fatalf("read staged models: %v", err)
	}
	var modelsObj map[string]any
	if err := json.Unmarshal(modelsRaw, &modelsObj); err != nil {
		t.Fatalf("parse staged models: %v", err)
	}
	providers, _ := modelsObj["providers"].(map[string]any)
	xproxyProvider, _ := providers["xproxy"].(map[string]any)
	modelList, _ := xproxyProvider["models"].([]any)
	found := false
	for _, raw := range modelList {
		entry, _ := raw.(map[string]any)
		if stringValueOrDefault(entry["id"], "") == attorneySearchModel {
			found = true
			break
		}
	}
	if !found {
		t.Fatalf("staged model catalog missing search model: %#v", modelList)
	}

	authRaw, err := os.ReadFile(filepath.Join(homeDir, ".pi", "agent", "auth.json"))
	if err != nil {
		t.Fatalf("read staged auth: %v", err)
	}
	if string(authRaw) != "{}\n" {
		t.Fatalf("auth.json = %q, want {}\n", string(authRaw))
	}
}
