package runner

import (
	"fmt"
	"path/filepath"
	"strings"
)

const defaultRemoteSessionCwd = "/home/user"

func resolveAttorney(role string, cfg Config, complaintPath string) (AttorneyRunInfo, error) {
	role = strings.TrimSpace(role)
	base := AttorneyRoleConfig{
		Model:      cfg.AttorneyModel,
		ACPCommand: cfg.ACPCommand,
	}
	switch role {
	case "plaintiff":
		base = mergeAttorneyRoleConfig(base, cfg.PlaintiffAttorney)
	case "defendant":
		base = mergeAttorneyRoleConfig(base, cfg.DefendantAttorney)
	default:
		return AttorneyRunInfo{}, fmt.Errorf("unsupported attorney role %q", role)
	}
	model := strings.TrimSpace(base.Model)
	if model == "" {
		model = DefaultAttorneyModel
	}
	spec, err := parseAttorneyModel(model)
	if err != nil {
		return AttorneyRunInfo{}, err
	}
	sessionCwd := strings.TrimSpace(base.SessionCwd)
	transport := "stdio"
	command := strings.TrimSpace(base.ACPCommand)
	endpoint := strings.TrimSpace(base.ACPEndpoint)
	if endpoint != "" {
		transport = "tcp"
		if sessionCwd == "" {
			sessionCwd = defaultRemoteSessionCwd
		}
		command = ""
	} else {
		if command == "" {
			return AttorneyRunInfo{}, fmt.Errorf("%s attorney ACP command is required", role)
		}
		if sessionCwd == "" {
			sessionCwd, err = filepath.Abs(filepath.Dir(complaintPath))
			if err != nil {
				return AttorneyRunInfo{}, fmt.Errorf("resolve %s attorney session cwd: %w", role, err)
			}
		}
	}
	return AttorneyRunInfo{
		Role:          role,
		Model:         model,
		SearchEnabled: spec.SearchRequested,
		ACPTransport:  transport,
		ACPCommand:    command,
		ACPEndpoint:   endpoint,
		SessionCwd:    sessionCwd,
	}, nil
}

func mergeAttorneyRoleConfig(base AttorneyRoleConfig, override AttorneyRoleConfig) AttorneyRoleConfig {
	if strings.TrimSpace(override.Model) != "" {
		base.Model = strings.TrimSpace(override.Model)
	}
	if strings.TrimSpace(override.ACPCommand) != "" {
		base.ACPCommand = strings.TrimSpace(override.ACPCommand)
	}
	if strings.TrimSpace(override.ACPEndpoint) != "" {
		base.ACPEndpoint = strings.TrimSpace(override.ACPEndpoint)
	}
	if strings.TrimSpace(override.SessionCwd) != "" {
		base.SessionCwd = strings.TrimSpace(override.SessionCwd)
	}
	return base
}

func attorneyRunInfos(cfg Config, complaintPath string) ([]AttorneyRunInfo, error) {
	plaintiff, err := resolveAttorney("plaintiff", cfg, complaintPath)
	if err != nil {
		return nil, err
	}
	defendant, err := resolveAttorney("defendant", cfg, complaintPath)
	if err != nil {
		return nil, err
	}
	return []AttorneyRunInfo{plaintiff, defendant}, nil
}
