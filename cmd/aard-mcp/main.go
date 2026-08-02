package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"sort"
	"strings"
	"syscall"

	aardmcp "adjudication/service/mcp/arbd"
)

type originList struct {
	values []string
}

func (l *originList) String() string {
	values := append([]string{}, l.values...)
	sort.Strings(values)
	return strings.Join(values, ",")
}

func (l *originList) Set(value string) error {
	origin := strings.TrimSpace(value)
	if origin == "" {
		return fmt.Errorf("origin must not be empty")
	}
	l.values = append(l.values, origin)
	return nil
}

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx, os.Args[1:], os.Stderr); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

func run(ctx context.Context, args []string, stderr io.Writer) error {
	fs := flag.NewFlagSet("aard-mcp", flag.ContinueOnError)
	fs.SetOutput(stderr)
	var origins originList
	listenAddr := fs.String("listen", aardmcp.DefaultListenAddr, "MCP listen address")
	caseAPIBase := fs.String("caseapi-base", "", "Base URL for the AARD case API")
	bearerToken := fs.String("bearer-token", "", "Optional bearer token required from MCP clients")
	apiBearerToken := fs.String("api-bearer-token", "", "Optional bearer token sent to the case API")
	sessionTTL := fs.Duration("session-ttl", aardmcp.DefaultSessionTTL, "Idle MCP session TTL; 0 disables expiry")
	sessionCleanupInterval := fs.Duration("session-cleanup-interval", aardmcp.DefaultSessionCleanupInterval, "Interval for deleting expired MCP sessions")
	fs.Var(&origins, "allow-origin", "Allowed HTTP Origin; repeat when browser clients need non-localhost origins")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aard-mcp --caseapi-base URL [options]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	return aardmcp.Run(ctx, aardmcp.Options{
		ListenAddr:             strings.TrimSpace(*listenAddr),
		CaseAPIBase:            strings.TrimSpace(*caseAPIBase),
		BearerToken:            strings.TrimSpace(*bearerToken),
		APIBearerToken:         strings.TrimSpace(*apiBearerToken),
		SessionTTL:             *sessionTTL,
		DisableSessionExpiry:   *sessionTTL == 0,
		SessionCleanupInterval: *sessionCleanupInterval,
		AllowedOrigins:         origins.values,
		Log:                    stderr,
	})
}
