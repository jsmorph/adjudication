package compat

import (
	"flag"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var coreCarveBinDir = flag.String("carve-bin-dir", "", "Directory containing carve executables")
var _ = flag.String("service-bin-dir", "", "Directory containing service executables")
var _ = flag.String("carve-root", "", "Carve checkout root")

type commandInterface struct {
	name       string
	subcommand string
	flags      []string
	required   string
}

func TestCoreCommandInterface(t *testing.T) {
	binDir := strings.TrimSpace(*coreCarveBinDir)
	if binDir == "" {
		t.Skip("-carve-bin-dir is not set")
	}

	interfaces := []commandInterface{
		{
			name:       "adc",
			subcommand: "case",
			flags: []string{
				"case-id", "run-id", "complaint", "out-dir", "caseapi-addr",
				"external-role", "engine", "roleapi-timeout-seconds",
			},
			required: "--complaint is required",
		},
		{
			name:       "adc",
			subcommand: "scenario",
			flags: []string{
				"case-id", "run-id", "scenario", "output", "runtime", "events",
				"db", "transcript", "digest", "report-model", "allow-assertion-failures",
				"caseapi-addr", "external-role", "engine",
			},
			required: "--scenario is required",
		},
		{
			name:       "aar",
			subcommand: "case",
			flags: []string{
				"case-id", "run-id", "complaint", "file", "out-dir", "caseapi-addr",
				"council-backend", "policy", "common-root", "engine", "council-pool",
				"attorney-instructions", "prompt-dir", "attorney-common-prompt",
				"attorney-arguments-prompt", "attorney-rebuttals-prompt",
				"lawyer-timeout-seconds", "timeout-seconds", "invalid-attempt-limit",
				"max-response-bytes",
			},
			required: "--complaint and --out-dir are required",
		},
		{
			name:       "aard",
			subcommand: "case",
			flags: []string{
				"case-id", "run-id", "complaint", "file", "out-dir", "caseapi-addr",
				"council-backend", "policy", "judgment-standard", "common-root", "engine",
				"council-pool", "council-size", "attorney-instructions", "prompt-dir",
				"attorney-common-prompt", "attorney-arguments-prompt",
				"attorney-rebuttals-prompt", "lawyer-timeout-seconds", "timeout-seconds",
				"invalid-attempt-limit", "max-response-bytes",
			},
			required: "--complaint and --out-dir are required",
		},
	}

	for _, iface := range interfaces {
		iface := iface
		t.Run(iface.name+"_"+iface.subcommand, func(t *testing.T) {
			bin := filepath.Join(binDir, iface.name)
			if info, err := os.Stat(bin); err != nil {
				t.Fatalf("stat %s: %v", bin, err)
			} else if info.IsDir() {
				t.Fatalf("core binary is a directory: %s", bin)
			}

			help, err := exec.Command(bin, "help", iface.subcommand).CombinedOutput()
			if err != nil {
				t.Fatalf("%s help %s: %v\n%s", bin, iface.subcommand, err, help)
			}
			for _, flagName := range iface.flags {
				pattern := regexp.MustCompile(`(?m)^\s+-` + regexp.QuoteMeta(flagName) + `(?:\s|$)`)
				if !pattern.Match(help) {
					t.Errorf("%s help %s lacks --%s\n%s", bin, iface.subcommand, flagName, help)
				}
			}

			output, err := exec.Command(bin, iface.subcommand).CombinedOutput()
			if err == nil {
				t.Fatalf("%s %s without required input succeeded\n%s", bin, iface.subcommand, output)
			}
			if !strings.Contains(string(output), iface.required) {
				t.Fatalf("%s %s missing required-input error %q\n%s", bin, iface.subcommand, iface.required, output)
			}
		})
	}
}
