# Attested ADC Dev Host Requirements

## Scope

Attested ADC runs use the generic exec AMI launcher from the `attest` repository and add ADC-specific Docker, S3, secret, and verification requirements.  Start with `dev-host.md` in the external `attest` checkout, which defines the generic `dev` host, Nix, EC2, IAM, and launched-instance assumptions for `attest`.  This document adds the requirements for building the ADC attested workload image, staging complaint-packet inputs, collecting S3 artifacts, and verifying an ADC attestation.

The current attested ADC path supports the complaint path only.  The caller gives the same `complaint_path` that local ADC accepts, and the local driver packages the complaint plus linked files into `case.tar.gz` and `case-packet.json`.  Scenario input and local ADC runtime overrides are rejected by the attested clerk path until they have explicit attestation support.

## Host Layout

The `dev` host performs three ADC jobs.  It builds Docker images from a source checkout, stores the runtime launcher files used by the exec AMI, and reads or writes S3 objects for the local driver.  The launcher directory and source checkout are separate directories with different purposes.

| Path on `dev` | Required contents | Purpose |
| --- | --- | --- |
| `/home/ec2-user/adjudication-build-2361886` | Service checkout containing `service/attested/adc` | Docker build context for `arbattest-adc:dev` and `adc-glue:poc`. |
| `/home/ec2-user/attest` | `exec.sh`, `parse_attestation.py`, and `run-adc.sh` | Runtime launcher directory used by `run-adc-attested.py` and manual `exec.sh` commands. |
| `/home/ec2-user/arbattest-secrets/auth.json` | Codex auth JSON | Staged to S3 as the OpenClaw Codex auth file. |
| `/home/ec2-user/arbattest-secrets/keys.sh` | Shell assignments for provider keys | Staged to S3; must define `OPENROUTER_API_KEY` for Pi jurors. |
| `/home/ec2-user/adc-glue-poc.tar` | Docker archive produced by `docker save adc-glue:poc` | Uploaded to S3 for the exec AMI to download. |

`/home/ec2-user/attest` is the runtime directory used by the exec launcher.  Changes to `run-adc.sh` belong in `service/attested/adc/run-adc.sh`.  Copy the reviewed service version to the runtime directory before use.

## Host Software

The ADC build host inherits the generic `attest` requirements and adds Docker.  The verified host runs Amazon Linux 2023 with `aws`, `git`, `docker`, and Nix installed.  The `ec2-user` account must be able to run `sudo docker build`, `sudo docker save`, and `sudo chown` without an interactive password prompt.

Docker builds need enough root filesystem capacity for the ADC base image, the attested workload image, the saved image archive, and build cache.  A 32 GiB root volume with about 20 GiB free has worked after cleanup.  If the build fails because `/` is full, remove old Docker build cache, obsolete local images, and stale image tar files before rebuilding.

The local driver uses SSH and SCP to make `dev` read from S3, write case-packet inputs to S3, and copy artifacts back to the local output directory.  The current driver defaults to `DEV_HOST=dev` and `REMOTE_ATTEST_DIR=/home/ec2-user/attest`.  The caller also needs `uv` locally because verification runs `uv run attest/parse_attestation.py` after downloading the attestation.

## AWS Region, AMI, And Instance Profile

The verified region is `us-east-2`.  The current Docker-enabled exec AMI is `ami-011f957fe91cf7b81`, and the expected PCR values in the runbook correspond to that AMI.  Rebuilding the exec AMI requires recording the new AMI id and PCR values in the runbook and in commands that pass `--expected-pcr4` and `--expected-pcr7`.

The verified exec instance type is `m5.4xlarge`.  The exec AMI root filesystem is RAM-backed, and Docker extracts image layers into that RAM-backed filesystem.  Smaller instances can fail while loading the attested workload image because they do not have enough RAM-backed storage.

The verified instance profile is `ec2-nix-builder`.  The `dev` host role must be able to pass the role behind that instance profile when it launches the exec AMI.  The launched exec instance profile must have S3 permissions for the image tar, staged inputs, and run-output prefix.

## S3 Layout

The verified bucket is `s3://agentcourt-data` in `us-east-2`, with ADC attestation objects under the `arbattest/` prefix.  Use timestamped child prefixes for inputs and outputs.  Do not reuse an output prefix, because a run prefix is a record of one remote execution.

| Prefix | Producer | Consumer | Contents |
| --- | --- | --- | --- |
| `s3://agentcourt-data/arbattest/images/` | `dev` Docker build step | Exec AMI | `adc-glue-poc.tar`, the Docker archive loaded by `run-adc.sh`. |
| `s3://agentcourt-data/arbattest/adc-inputs/<run>/` | Secret staging and local driver | Exec workload container | `auth.json`, `keys.sh`, `case.tar.gz`, and `case-packet.json`. |
| `s3://agentcourt-data/arbattest/adc-runs/<run-id>/` | Exec workload container | Driver, service monitoring, and verification | `events.ndjson` during execution, plus terminal artifacts on success. |
| `s3://agentcourt-data/arbattest/container-poc/` | Container proof runs | Operator verification | Small proof outputs for attestation-only container runs. |

The successful terminal artifact set is `run.log`, `manifest.json`, `manifest.sha384`, `attestation.b64`, and `adc-output.tar.gz`.  The live `events.ndjson` object supports monitoring and may exist before the terminal set.  Current ADC failure paths upload `run.log`, `adc-partial.tar.gz`, and any available live events, then return failure without verified completion.

## S3 Permissions

The `dev` host role needs S3 permissions for staging inputs, uploading images, polling output prefixes, downloading output artifacts, and cleanup.  Large Docker archive uploads can use multipart upload, so include multipart actions.  Cleanup permissions should be granted only to operators expected to delete test runs or obsolete images.

| Prefix | Required `dev` actions |
| --- | --- |
| `arn:aws:s3:::agentcourt-data` | `s3:ListBucket` with prefix conditions for `arbattest/images/`, `arbattest/adc-inputs/`, `arbattest/adc-runs/`, and `arbattest/container-poc/`; `s3:ListBucketMultipartUploads` for large archive uploads. |
| `arn:aws:s3:::agentcourt-data/arbattest/images/*` | `s3:PutObject`, `s3:GetObject`, `s3:AbortMultipartUpload`, `s3:ListMultipartUploadParts`, and optional `s3:DeleteObject`. |
| `arn:aws:s3:::agentcourt-data/arbattest/adc-inputs/*` | `s3:PutObject`, `s3:GetObject`, `s3:ListMultipartUploadParts`, and optional `s3:DeleteObject`. |
| `arn:aws:s3:::agentcourt-data/arbattest/adc-runs/*` | `s3:GetObject`, `s3:PutObject` for manual diagnostics, `s3:AbortMultipartUpload`, `s3:ListMultipartUploadParts`, and optional `s3:DeleteObject`. |
| `arn:aws:s3:::agentcourt-data/arbattest/container-poc/*` | `s3:GetObject`, `s3:PutObject`, and optional `s3:DeleteObject`. |

The launched exec instance profile needs narrower S3 permissions.  It reads the attested workload image tar and input objects, then writes terminal run artifacts.  Grant list permission only for diagnostics or future scripts that enumerate objects.

| Prefix | Required launched-instance actions |
| --- | --- |
| `arn:aws:s3:::agentcourt-data/arbattest/images/*` | `s3:GetObject` |
| `arn:aws:s3:::agentcourt-data/arbattest/adc-inputs/*` | `s3:GetObject` |
| `arn:aws:s3:::agentcourt-data/arbattest/adc-runs/*` | `s3:PutObject`, `s3:AbortMultipartUpload`, `s3:ListMultipartUploadParts` |
| `arn:aws:s3:::agentcourt-data` | Optional `s3:ListBucket` with prefix conditions for diagnostics. |

If the bucket enforces SSE-KMS, add KMS permissions for the same actors.  Uploaders need `kms:Encrypt` and `kms:GenerateDataKey`.  Downloaders and verifiers need `kms:Decrypt` for objects they read.

## Secrets

`/home/ec2-user/arbattest-secrets/auth.json` must be the Codex auth file OpenClaw can import.  The staging command copies it to `INPUT_PREFIX/auth.json`, and ADC stages it into per-lawyer container-readable Codex homes inside the run output.  The file should remain outside Git and outside served artifact directories.

`/home/ec2-user/arbattest-secrets/keys.sh` must assign or export `OPENROUTER_API_KEY`.  The exec container entrypoint sources it before running ADC and exits if the key is absent.  Add further provider keys only when the selected runtime path requires them.

## OpenClaw Networking

Attested ADC runs start OpenClaw lawyer containers from inside the exec workload container through the host Docker socket.  Those child OpenClaw containers must use Docker host networking on the Docker-enabled exec AMI.  The ADC exec entrypoint passes `--openclaw-network host`, and `adc run` uses `127.0.0.1` as the Docker MCP host in that mode.

## Verification Configuration

The current lower-level command verifies the exec AMI with PCR4 and PCR7.  PCR12 defaults to all zeroes unless a caller supplies another value.  Store the expected PCR values with the AMI id and replace them whenever the exec AMI changes.

| Value | Current setting |
| --- | --- |
| Exec AMI | `ami-011f957fe91cf7b81` |
| Region | `us-east-2` |
| Instance type | `m5.4xlarge` |
| Instance profile | `ec2-nix-builder` |
| PCR4 | `83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4` |
| PCR7 | `98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35` |
| PCR12 | `000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000` |

Successful ADC verification checks `manifest.sha384`, the archive SHA-384, `run.log` SHA-384, the attestation signature and certificate chain, Nitro TPM user data, and the expected PCR values.  The service also requires an extracted `adc-output/run.json` before it marks an attested case `completed`.  Partial runs should be investigated through `run.log`, `progress.log`, `launcher.log`, and `adc-partial.tar.gz`.

## Operational Checks

Run these checks before rebuilding the attested workload image or launching a long run.  They verify host layout, tool paths, source checkout, launcher directory, secrets, Docker access, AWS identity, and free disk capacity.  They do not launch EC2 instances or write S3 objects.

```bash
ssh dev 'set -eu
printf "home=%s\n" "$HOME"
uname -a
command -v aws
command -v git
command -v docker
command -v nix
test -d /home/ec2-user/adjudication-build-2361886
test -d /home/ec2-user/attest
test -x /home/ec2-user/attest/exec.sh
test -x /home/ec2-user/attest/run-adc.sh
test -f /home/ec2-user/arbattest-secrets/auth.json
test -f /home/ec2-user/arbattest-secrets/keys.sh
sudo docker ps >/dev/null
AWS_DEFAULT_REGION=us-east-2 aws sts get-caller-identity --output json
df -h / /tmp 2>/dev/null || df -h /
'
```

Run these S3 checks when the role should be able to read and write the ADC prefixes.  The second command writes and deletes a small probe object, so use it only when cleanup permission is expected.  Replace the bucket or prefix if the deployment uses a different S3 location.

```bash
ssh dev 'AWS_DEFAULT_REGION=us-east-2 aws s3 ls s3://agentcourt-data/arbattest/'
ssh dev 'set -eu
probe="s3://agentcourt-data/arbattest/probes/dev-$(date -u +%Y%m%dT%H%M%SZ).txt"
printf "ok\n" >/tmp/arbattest-s3-probe.txt
AWS_DEFAULT_REGION=us-east-2 aws s3 cp /tmp/arbattest-s3-probe.txt "$probe" --no-progress
AWS_DEFAULT_REGION=us-east-2 aws s3 rm "$probe"
rm -f /tmp/arbattest-s3-probe.txt
'
```

## References

The generic host and AMI requirements live in `dev-host.md` in the external `attest` checkout.  The ADC image build, local driver run, Clerk service run, verification checks, and troubleshooting table live in [ADC Docker Image Runbook](Dockerfile.md).  The one-complaint helper is `service/attested/adc/run-one-attested-adc.sh`; it stages `auth.json` and `keys.sh` before invoking the lower-level driver and exec workload script in the same directory.
