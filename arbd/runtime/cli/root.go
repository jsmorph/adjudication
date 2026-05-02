package cli

import (
	"errors"
	"fmt"
	"io"
)

type ReportedError struct {
	Err error
}

func (e *ReportedError) Error() string {
	if e == nil || e.Err == nil {
		return ""
	}
	return e.Err.Error()
}

func (e *ReportedError) Unwrap() error {
	if e == nil {
		return nil
	}
	return e.Err
}

func IsReportedError(err error) bool {
	var reported *ReportedError
	return errors.As(err, &reported)
}

func Run(args []string, stdout io.Writer, stderr io.Writer) error {
	if len(args) == 0 {
		printRootUsage(stderr)
		return fmt.Errorf("subcommand is required")
	}
	switch args[0] {
	case "case":
		return RunCase(args[1:], stdout, stderr)
	case "complain":
		return RunComplain(args[1:], stdout, stderr)
	case "stage-attorney-pi-home":
		return RunStageAttorneyPIHome(args[1:], stdout, stderr)
	case "attorney-tools":
		return RunAttorneyTools(args[1:], stdout, stderr)
	case "validate":
		return RunValidate(args[1:], stdout, stderr)
	case "help", "-h", "--help":
		if len(args) == 1 {
			printRootUsage(stdout)
			return nil
		}
		switch args[1] {
		case "case":
			return RunCase([]string{"-h"}, stdout, stderr)
		case "complain":
			return RunComplain([]string{"-h"}, stdout, stderr)
		case "stage-attorney-pi-home":
			return RunStageAttorneyPIHome([]string{"-h"}, stdout, stderr)
		case "attorney-tools":
			return RunAttorneyTools([]string{"-h"}, stdout, stderr)
		case "validate":
			return RunValidate([]string{"-h"}, stdout, stderr)
		default:
			printRootUsage(stderr)
			return fmt.Errorf("unknown help topic %q", args[1])
		}
	default:
		printRootUsage(stderr)
		return fmt.Errorf("unknown subcommand %q", args[0])
	}
}

func printRootUsage(w io.Writer) {
	fmt.Fprintln(w, "Usage: aard <subcommand> [options]")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "Subcommands:")
	fmt.Fprintln(w, "  case       Initialize an arbitration case from a complaint")
	fmt.Fprintln(w, "  complain   Draft complaint.md from a situation markdown file")
	fmt.Fprintln(w, "  stage-attorney-pi-home   Stage PI settings for an attorney backend")
	fmt.Fprintln(w, "  attorney-tools           Print the _aar tool catalog as JSON")
	fmt.Fprintln(w, "  validate   Validate a complaint file")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "Use 'aard help <subcommand>' for subcommand flags.")
}
