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

	adcservice "adjudication/service/adc"
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
	fs := flag.NewFlagSet("adc-service", flag.ContinueOnError)
	fs.SetOutput(stderr)
	listenAddr := fs.String("listen", adcservice.DefaultListenAddr, "Service listen address")
	outputRoot := fs.String("output-root", "out/adc-service", "Directory containing service-created case output directories")
	adcBin := fs.String("adc-bin", "adc", "ADC binary used to start child cases")
	adcRunBin := fs.String("adc-run-bin", "adc-run", "Service-owned ADC local-agent launcher")
	adcWorkingDir := fs.String("adc-working-dir", "", "Optional working directory for core adc processes")
	enginePath := fs.String("engine", "", "Optional Lean engine command passed to child cases")
	bearerToken := fs.String("bearer-token", "", "Optional bearer token required from service clients")
	startupWait := fs.Duration("case-startup-timeout", adcservice.DefaultCaseStartupWait, "Maximum time to wait for a child case API health response")
	attestedDriver := fs.String("attested-driver", "", "Attested ADC driver path")
	attestedUV := fs.String("attested-uv", "", "uv executable used to run the attested ADC driver")
	attestedParser := fs.String("attested-parser", "", "Attestation parser path")
	attestedInputPrefix := fs.String("attested-input-prefix", "", "S3 prefix containing auth.json and keys.sh for attested ADC inputs")
	attestedOutputPrefix := fs.String("attested-output-prefix", "", "Exact S3 output prefix for attested ADC runs")
	attestedOutputRoot := fs.String("attested-output-root", "s3://agentcourt-data/arbattest/adc-runs", "S3 output root for attested ADC runs")
	attestedExecAMI := fs.String("attested-exec-ami", "", "Exec AMI ID for attested ADC runs")
	attestedDevHost := fs.String("attested-dev-host", "dev", "SSH host used for AWS and exec AMI launch commands")
	attestedRemoteAttestDir := fs.String("attested-remote-attest-dir", "/home/ec2-user/attest", "attest checkout path on the dev host")
	attestedAWSRegion := fs.String("attested-aws-region", "us-east-2", "AWS region for attested ADC runs")
	attestedInstanceType := fs.String("attested-instance-type", "m5.4xlarge", "EC2 instance type for attested ADC runs")
	attestedIAMInstanceProfile := fs.String("attested-iam-instance-profile", "ec2-nix-builder", "IAM instance profile for attested ADC runs")
	attestedImageTarS3 := fs.String("attested-image-tar-s3", "s3://agentcourt-data/arbattest/images/adc-glue-poc.tar", "S3 object containing the attested ADC image tar")
	attestedRootVolumeSizeGB := fs.Int("attested-root-volume-size-gb", 0, "Root volume size in GiB for attested ADC instances")
	attestedExecPollAttempts := fs.Int("attested-exec-poll-attempts", 0, "Exec launcher poll attempts for attested ADC runs; 0 derives the value from the driver timeout")
	attestedPollIntervalSeconds := fs.Int("attested-poll-interval-seconds", 30, "Seconds between attested ADC output polls")
	attestedTimeoutSeconds := fs.Int("attested-timeout-seconds", 10800, "Seconds before the attested ADC driver times out")
	attestedExpectedPCR4 := fs.String("attested-expected-pcr4", "", "Expected attestation PCR 4")
	attestedExpectedPCR7 := fs.String("attested-expected-pcr7", "", "Expected attestation PCR 7")
	attestedExpectedPCR12 := fs.String("attested-expected-pcr12", "", "Expected attestation PCR 12")
	fs.Usage = func() {
		fmt.Fprintf(stderr, "Usage: adc-service [options]\n\n")
		fs.PrintDefaults()
	}
	if err := fs.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return nil
		}
		return err
	}
	return adcservice.Run(ctx, adcservice.Config{
		ListenAddr:    strings.TrimSpace(*listenAddr),
		OutputRoot:    strings.TrimSpace(*outputRoot),
		ADCBin:        strings.TrimSpace(*adcBin),
		ADCRunBin:     strings.TrimSpace(*adcRunBin),
		ADCWorkingDir: strings.TrimSpace(*adcWorkingDir),
		EnginePath:    strings.TrimSpace(*enginePath),
		BearerToken:   strings.TrimSpace(*bearerToken),
		Attested: adcservice.AttestedClerkConfig{
			Verify:              true,
			DriverPath:          strings.TrimSpace(*attestedDriver),
			UV:                  strings.TrimSpace(*attestedUV),
			ParserPath:          strings.TrimSpace(*attestedParser),
			InputPrefix:         strings.TrimSpace(*attestedInputPrefix),
			OutputPrefix:        strings.TrimSpace(*attestedOutputPrefix),
			OutputRoot:          strings.TrimSpace(*attestedOutputRoot),
			ExecAMI:             strings.TrimSpace(*attestedExecAMI),
			DevHost:             strings.TrimSpace(*attestedDevHost),
			RemoteAttestDir:     strings.TrimSpace(*attestedRemoteAttestDir),
			AWSRegion:           strings.TrimSpace(*attestedAWSRegion),
			InstanceType:        strings.TrimSpace(*attestedInstanceType),
			IAMInstanceProfile:  strings.TrimSpace(*attestedIAMInstanceProfile),
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
