package cli

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"path/filepath"
	"strings"

	"adjudication/arb/runtime/runner"
)

func RunStageAttorneyPIHome(args []string, stdout io.Writer, stderr io.Writer) error {
	fs := flag.NewFlagSet("stage-attorney-pi-home", flag.ContinueOnError)
	fs.SetOutput(stderr)
	dir := fs.String("dir", "", "Target home directory")
	model := fs.String("model", runner.DefaultAttorneyModel, "Attorney ACP model id")
	commonRoot := fs.String("common-root", defaultCommonRoot(), "Path to the shared common directory")
	legacyCommonRoot := fs.String("agentcourt-root", "", "Deprecated alias for --common-root")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aar stage-attorney-pi-home --dir DIR [options]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	if strings.TrimSpace(*dir) == "" {
		return fmt.Errorf("--dir is required")
	}
	commonRootValue := strings.TrimSpace(*commonRoot)
	if strings.TrimSpace(*legacyCommonRoot) != "" {
		commonRootValue = strings.TrimSpace(*legacyCommonRoot)
	}
	commonRootResolved, err := filepath.Abs(commonRootValue)
	if err != nil {
		return fmt.Errorf("resolve --common-root: %w", err)
	}
	targetDir, err := filepath.Abs(strings.TrimSpace(*dir))
	if err != nil {
		return fmt.Errorf("resolve --dir: %w", err)
	}
	if err := runner.StageAttorneyPIHome(commonRootResolved, targetDir, strings.TrimSpace(*model)); err != nil {
		return err
	}
	return nil
}

func RunAttorneyTools(args []string, stdout io.Writer, stderr io.Writer) error {
	fs := flag.NewFlagSet("attorney-tools", flag.ContinueOnError)
	fs.SetOutput(stderr)
	includeWorkspaceWriter := fs.Bool("include-workspace-writer", false, "Include the workspace file writer tool")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aar attorney-tools [options]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	wire, err := json.Marshal(runner.ACPClientToolSpecs(*includeWorkspaceWriter))
	if err != nil {
		return fmt.Errorf("marshal attorney tools: %w", err)
	}
	if _, err := fmt.Fprintln(stdout, string(wire)); err != nil {
		return fmt.Errorf("write attorney tools: %w", err)
	}
	return nil
}
