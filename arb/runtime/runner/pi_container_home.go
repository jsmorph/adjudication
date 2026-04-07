package runner

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	xproxy "adjudication/common/xproxy"
)

const DefaultAttorneyModel = "openai://gpt-5?tools=search"

func usesPIContainerWrapper(command string) bool {
	base := strings.TrimSpace(filepath.Base(command))
	return base == "acp-podman.sh" || base == "pi-podman.sh"
}

func ParseAttorneyModelForCLI(model string) (xproxy.ModelSpec, error) {
	return parseAttorneyModel(model)
}

func parseAttorneyModel(model string) (xproxy.ModelSpec, error) {
	model = strings.TrimSpace(model)
	if model == "" {
		model = DefaultAttorneyModel
	}
	spec, err := xproxy.ParseXProxyModel(model)
	if err != nil {
		return xproxy.ModelSpec{}, fmt.Errorf("parse attorney model %q: %w", model, err)
	}
	return spec, nil
}

func StageAttorneyPIHome(commonRoot string, homeDir string, model string) error {
	model = strings.TrimSpace(model)
	if model == "" {
		model = DefaultAttorneyModel
	}
	spec, err := parseAttorneyModel(model)
	if err != nil {
		return err
	}
	agentDir := filepath.Join(homeDir, ".pi", "agent")
	if err := os.MkdirAll(agentDir, 0o755); err != nil {
		return fmt.Errorf("create PI agent dir: %w", err)
	}
	settingsRaw, err := os.ReadFile(filepath.Join(commonRoot, "etc", "pi-settings.xproxy.json"))
	if err != nil {
		return fmt.Errorf("read pi settings: %w", err)
	}
	settingsRaw, err = stageAttorneyPISettings(settingsRaw, model)
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(agentDir, "settings.json"), settingsRaw, 0o644); err != nil {
		return fmt.Errorf("write settings.json: %w", err)
	}
	modelsRaw, err := os.ReadFile(filepath.Join(commonRoot, "etc", "pi-models.xproxy.json"))
	if err != nil {
		return fmt.Errorf("read pi model catalog: %w", err)
	}
	modelsRaw, err = stageAttorneyPIModelCatalog(modelsRaw, model, spec)
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(agentDir, "models.json"), modelsRaw, 0o644); err != nil {
		return fmt.Errorf("write models.json: %w", err)
	}
	authPath := filepath.Join(agentDir, "auth.json")
	if err := os.WriteFile(authPath, []byte("{}\n"), 0o644); err != nil {
		return fmt.Errorf("write %s: %w", authPath, err)
	}
	return nil
}

func prepareEphemeralPIHome(commonRoot string, model string) (string, func() error, error) {
	model = strings.TrimSpace(model)
	if model == "" {
		model = DefaultAttorneyModel
	}
	homeDir, err := os.MkdirTemp("", "agentarbitration-pi-home-")
	if err != nil {
		return "", nil, fmt.Errorf("create PI home dir: %w", err)
	}
	cleanup := func() error {
		if err := os.RemoveAll(homeDir); err != nil {
			return fmt.Errorf("remove PI home dir %s: %w", homeDir, err)
		}
		return nil
	}
	fail := func(err error) (string, func() error, error) {
		cleanupErr := cleanup()
		if cleanupErr != nil {
			err = errors.Join(err, cleanupErr)
		}
		return "", nil, err
	}
	if err := StageAttorneyPIHome(commonRoot, homeDir, model); err != nil {
		return fail(err)
	}
	return homeDir, cleanup, nil
}

func stageAttorneyPISettings(raw []byte, model string) ([]byte, error) {
	var settings map[string]any
	if err := json.Unmarshal(raw, &settings); err != nil {
		return nil, fmt.Errorf("parse pi settings: %w", err)
	}
	settings["defaultModel"] = strings.TrimSpace(model)
	updated, err := json.MarshalIndent(settings, "", "  ")
	if err != nil {
		return nil, fmt.Errorf("marshal pi settings: %w", err)
	}
	return append(updated, '\n'), nil
}

func stageAttorneyPIModelCatalog(raw []byte, model string, _ xproxy.ModelSpec) ([]byte, error) {
	var catalog map[string]any
	if err := json.Unmarshal(raw, &catalog); err != nil {
		return nil, fmt.Errorf("parse pi model catalog: %w", err)
	}
	providers, _ := catalog["providers"].(map[string]any)
	if providers == nil {
		return nil, fmt.Errorf("pi model catalog missing providers")
	}
	xproxyProvider, _ := providers["xproxy"].(map[string]any)
	if xproxyProvider == nil {
		return nil, fmt.Errorf("pi model catalog missing xproxy provider")
	}
	models, _ := xproxyProvider["models"].([]any)
	for _, rawModel := range models {
		entry, _ := rawModel.(map[string]any)
		if strings.TrimSpace(stringValueOrDefault(entry["id"], "")) == model {
			updated, err := json.MarshalIndent(catalog, "", "  ")
			if err != nil {
				return nil, fmt.Errorf("marshal pi model catalog: %w", err)
			}
			return append(updated, '\n'), nil
		}
	}
	models = append(models, map[string]any{
		"id":   model,
		"name": model,
	})
	xproxyProvider["models"] = models
	providers["xproxy"] = xproxyProvider
	catalog["providers"] = providers
	updated, err := json.MarshalIndent(catalog, "", "  ")
	if err != nil {
		return nil, fmt.Errorf("marshal pi model catalog: %w", err)
	}
	return append(updated, '\n'), nil
}

func stringValueOrDefault(value any, fallback string) string {
	if value == nil {
		return fallback
	}
	text := strings.TrimSpace(fmt.Sprintf("%v", value))
	if text == "" {
		return fallback
	}
	return text
}
