package main

import (
	"context"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"adjudication/arb/runtime/proceeding"
	"adjudication/arb/runtime/service"
)

func runService(ctx context.Context, args []string, stdout io.Writer, stderr io.Writer) error {
	fs := flag.NewFlagSet("service", flag.ContinueOnError)
	fs.SetOutput(stderr)
	listen := fs.String("listen", service.DefaultListenAddr, "Service listen address")
	registryDir := fs.String("registry-dir", "", "Case registry directory")
	outputRoot := fs.String("out-root", "", "Case output root")
	aarBin := fs.String("aar-bin", "", "Path to aar binary used for child cases")
	commonRoot := fs.String("common-root", proceeding.DefaultCommonRoot(), "Path to sibling shared common directory")
	enginePath := fs.String("engine", proceeding.DefaultEnginePath(), "Lean engine binary")
	bearerToken := fs.String("bearer-token", "", "Optional bearer token required for service requests")
	startupWait := fs.Duration("case-startup-timeout", service.DefaultCaseStartupWait, "Maximum time to wait for a child case API health response")
	attestedDriver := fs.String("attested-driver", "", "Path to service/attested/arb/run-arb-attested.py")
	attestedUV := fs.String("attested-uv", "", "Optional uv executable used as: uv run <attested-driver>")
	attestedParser := fs.String("attested-parser", "", "Optional attestation parser path")
	attestedInputPrefix := fs.String("attested-input-prefix", "", "Default S3 input prefix for attested Clerk runs")
	attestedOutputPrefix := fs.String("attested-output-prefix", "", "Default S3 output prefix for attested Clerk runs")
	attestedOutputRoot := fs.String("attested-output-root", "", "Default S3 output root for attested Clerk runs")
	attestedExecAMI := fs.String("attested-exec-ami", "", "Default exec AMI for attested Clerk runs")
	attestedDevHost := fs.String("attested-dev-host", "", "Default dev host used by the attested runner")
	attestedRemoteDir := fs.String("attested-remote-attest-dir", "", "Default attest repo path on the dev host")
	attestedAWSRegion := fs.String("attested-aws-region", "", "Default AWS region for attested Clerk runs")
	attestedInstanceType := fs.String("attested-instance-type", "", "Default EC2 instance type for attested Clerk runs")
	attestedInstanceProfile := fs.String("attested-iam-instance-profile", "", "Default IAM instance profile for attested Clerk runs")
	attestedImageTarS3 := fs.String("attested-image-tar-s3", "", "Default S3 tarball for the arb image")
	attestedRootVolumeSizeGB := fs.Int("attested-root-volume-size-gb", 0, "Default exec root volume size in GiB")
	attestedExecPollAttempts := fs.Int("attested-exec-poll-attempts", 0, "Default exec host poll attempts")
	attestedPollIntervalSeconds := fs.Int("attested-poll-interval-seconds", 0, "Default attested runner poll interval")
	attestedTimeoutSeconds := fs.Int("attested-timeout-seconds", 0, "Default attested runner timeout")
	attestedExpectedPCR4 := fs.String("attested-expected-pcr4", "", "Expected PCR4 for attested Clerk verification")
	attestedExpectedPCR7 := fs.String("attested-expected-pcr7", "", "Expected PCR7 for attested Clerk verification")
	attestedExpectedPCR12 := fs.String("attested-expected-pcr12", "", "Expected PCR12 for attested Clerk verification")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: aar service [options]\n\n")
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
	bin := strings.TrimSpace(*aarBin)
	if bin == "" {
		self, err := os.Executable()
		if err != nil {
			return fmt.Errorf("resolve current executable: %w", err)
		}
		bin = self
	}
	commonRootResolved, err := filepath.Abs(strings.TrimSpace(*commonRoot))
	if err != nil {
		return fmt.Errorf("resolve --common-root: %w", err)
	}
	cfg := service.Config{
		ListenAddr:  strings.TrimSpace(*listen),
		RegistryDir: regDir,
		OutputRoot:  outRoot,
		AARBin:      bin,
		CommonRoot:  commonRootResolved,
		EnginePath:  strings.TrimSpace(*enginePath),
		BearerToken: strings.TrimSpace(*bearerToken),
		Attested: service.AttestedClerkConfig{
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
	}
	return service.Run(ctx, cfg)
}
