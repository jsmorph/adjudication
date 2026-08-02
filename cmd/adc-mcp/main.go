package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"syscall"

	adcmcp "adjudication/service/mcp/adc"
)

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx, os.Args[1:], os.Stderr); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

func run(ctx context.Context, args []string, stderr io.Writer) error {
	fs := flag.NewFlagSet("adc-mcp", flag.ContinueOnError)
	fs.SetOutput(stderr)
	listenAddr := fs.String("listen", adcmcp.DefaultListenAddr, "MCP listen address")
	caseAPIBase := fs.String("caseapi-base", "", "Base URL for the ADC case API")
	bearerToken := fs.String("bearer-token", "", "Optional bearer token required from MCP clients")
	apiBearerToken := fs.String("api-bearer-token", "", "Optional bearer token sent to the case API")
	disableSessionExpiry := fs.Bool("disable-session-expiry", false, "Disable idle MCP session expiry")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: adc-mcp --caseapi-base URL [options]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	if strings.TrimSpace(*caseAPIBase) == "" {
		return fmt.Errorf("--caseapi-base is required")
	}
	return adcmcp.Run(ctx, adcmcp.Options{
		ListenAddr:           strings.TrimSpace(*listenAddr),
		CaseAPIBase:          strings.TrimSpace(*caseAPIBase),
		BearerToken:          strings.TrimSpace(*bearerToken),
		APIBearerToken:       strings.TrimSpace(*apiBearerToken),
		DisableSessionExpiry: *disableSessionExpiry,
		Log:                  stderr,
	})
}
