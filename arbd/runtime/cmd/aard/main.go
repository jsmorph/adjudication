package main

import (
	"fmt"
	"os"

	"adjudication/arbd/runtime/cli"
)

func main() {
	if err := cli.Run(os.Args[1:], os.Stdout, os.Stderr); err != nil {
		if !cli.IsReportedError(err) {
			fmt.Fprintf(os.Stderr, "error: %v\n", err)
		}
		os.Exit(1)
	}
}
