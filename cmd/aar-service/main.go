package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"

	aarservice "adjudication/service/arb"
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
	fs := flag.NewFlagSet("aar-service", flag.ContinueOnError)
	fs.SetOutput(stderr)
	listen := fs.String("listen", aarservice.DefaultListenAddr, "Service listen address")
	registryDir := fs.String("registry-dir", "", "Case registry directory")
	outputRoot := fs.String("out-root", "", "Case output root")
	aarBin := fs.String("aar-bin", "aar", "Path to the core aar binary")
	aarRunBin := fs.String("aar-run-bin", "aar-run", "Path to the service-owned aar-run binary")
	aarWorkingDir := fs.String("aar-working-dir", "", "Optional working directory for core aar processes")
	commonRoot := fs.String("common-root", "", "Optional common directory passed to core cases")
	enginePath := fs.String("engine", "", "Optional Lean engine binary passed to core cases")
	bearerToken := fs.String("bearer-token", "", "Optional bearer token required for service requests")
	startupWait := fs.Duration("case-startup-timeout", aarservice.DefaultCaseStartupWait, "Maximum time to wait for a child case API health response")
	attestedDriver := fs.String("attested-driver", "", "Path to the attested ARB driver")
	attestedUV := fs.String("attested-uv", "", "Optional uv executable used to run the attested driver")
	attestedParser := fs.String("attested-parser", "", "Optional attestation parser path")
	attestedInputPrefix := fs.String("attested-input-prefix", "", "Default S3 input prefix for attested Clerk runs")
	attestedOutputPrefix := fs.String("attested-output-prefix", "", "Default S3 output prefix for attested Clerk runs")
	attestedOutputRoot := fs.String("attested-output-root", "", "Default S3 output root for attested Clerk runs")
	attestedExecAMI := fs.String("attested-exec-ami", "", "Default exec AMI for attested Clerk runs")
	attestedDevHost := fs.String("attested-dev-host", "", "Default dev host used by the attested runner")
	attestedRemoteDir := fs.String("attested-remote-attest-dir", "", "Default attest repository path on the dev host")
	attestedAWSRegion := fs.String("attested-aws-region", "", "Default AWS region for attested Clerk runs")
	attestedInstanceType := fs.String("attested-instance-type", "", "Default EC2 instance type for attested Clerk runs")
	attestedInstanceProfile := fs.String("attested-iam-instance-profile", "", "Default IAM instance profile for attested Clerk runs")
	attestedImageTarS3 := fs.String("attested-image-tar-s3", "", "Default S3 tarball for the ARB image")
	attestedRootVolumeSizeGB := fs.Int("attested-root-volume-size-gb", 0, "Default exec root volume size in GiB")
	attestedExecPollAttempts := fs.Int("attested-exec-poll-attempts", 0, "Default exec host poll attempts")
	attestedPollIntervalSeconds := fs.Int("attested-poll-interval-seconds", 0, "Default attested runner poll interval")
	attestedTimeoutSeconds := fs.Int("attested-timeout-seconds", 0, "Default attested runner timeout")
	attestedExpectedPCR4 := fs.String("attested-expected-pcr4", "", "Expected PCR4 for attested Clerk verification")
	attestedExpectedPCR7 := fs.String("attested-expected-pcr7", "", "Expected PCR7 for attested Clerk verification")
	attestedExpectedPCR12 := fs.String("attested-expected-pcr12", "", "Expected PCR12 for attested Clerk verification")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aar-service [options]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	outRoot := strings.TrimSpace(*outputRoot)
	if outRoot == "" {
		outRoot = filepath.Join("out", "service")
	}
	regDir := strings.TrimSpace(*registryDir)
	if regDir == "" {
		regDir = filepath.Join(outRoot, "registry")
	}
	return aarservice.Run(ctx, aarservice.Config{
		ListenAddr:    strings.TrimSpace(*listen),
		RegistryDir:   regDir,
		OutputRoot:    outRoot,
		AARBin:        strings.TrimSpace(*aarBin),
		AARRunBin:     strings.TrimSpace(*aarRunBin),
		AARWorkingDir: strings.TrimSpace(*aarWorkingDir),
		CommonRoot:    strings.TrimSpace(*commonRoot),
		EnginePath:    strings.TrimSpace(*enginePath),
		BearerToken:   strings.TrimSpace(*bearerToken),
		Attested: aarservice.AttestedClerkConfig{
			DriverPath:          strings.TrimSpace(*attestedDriver),
			UV:                  strings.TrimSpace(*attestedUV),
			ParserPath:          strings.TrimSpace(*attestedParser),
			InputPrefix:         strings.TrimSpace(*attestedInputPrefix),
			OutputPrefix:        strings.TrimSpace(*attestedOutputPrefix),
			OutputRoot:          strings.TrimSpace(*attestedOutputRoot),
			ExecAMI:             strings.TrimSpace(*attestedExecAMI),
			DevHost:             strings.TrimSpace(*attestedDevHost),
			RemoteAttestDir:     strings.TrimSpace(*attestedRemoteDir),
			AWSRegion:           strings.TrimSpace(*attestedAWSRegion),
			InstanceType:        strings.TrimSpace(*attestedInstanceType),
			IAMInstanceProfile:  strings.TrimSpace(*attestedInstanceProfile),
			ImageTarS3:          strings.TrimSpace(*attestedImageTarS3),
			RootVolumeSizeGB:    *attestedRootVolumeSizeGB,
			ExecPollAttempts:    *attestedExecPollAttempts,
			PollIntervalSeconds: *attestedPollIntervalSeconds,
			TimeoutSeconds:      *attestedTimeoutSeconds,
			ExpectedPCR4:        strings.TrimSpace(*attestedExpectedPCR4),
			ExpectedPCR7:        strings.TrimSpace(*attestedExpectedPCR7),
			ExpectedPCR12:       strings.TrimSpace(*attestedExpectedPCR12),
		},
		StartupWait: *startupWait,
		Log:         stderr,
	})
}
