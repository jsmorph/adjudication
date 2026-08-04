# Attested AARD Dev Host Requirements

## Scope

Attested AARD runs use the generic exec AMI launcher from the `attest` repository and add AARD-specific Docker, S3, secret, and verification requirements.  The `dev-host.md` file in the external `attest` checkout defines the generic `dev` host, Nix, EC2, IAM, and launched-instance assumptions for `attest`.  This document adds the requirements for building the AARD attested workload image, staging inputs, launching the Docker-enabled exec AMI, collecting S3 artifacts, and verifying an AARD attestation.

The Clerk request path lives in the [AARD Service Manual](../../arbd/README.md).  The image build, exec AMI run path, S3 artifact layout, and verification commands live in the [AARD Docker Image Runbook](Dockerfile.md).  This document defines the `dev` host requirements those paths assume.

The attested AARD path supports checked-in examples and Clerk-style local case inputs.  Example mode selects a case inside the AARD Docker image with `AARD_EXAMPLE`.  Case-packet mode packages a local `complaint_path` and optional `case_files` into `case.tar.gz` and `case-packet.json`, uploads them under the S3 input prefix through `dev`, and records their hashes in the attestation manifest.

## Host Layout

The `dev` host performs three AARD jobs.  It builds Docker images from a source checkout, stores the runtime launcher files used by the exec AMI, and stages or reads S3 objects for the local driver.  The launcher directory and source checkout are separate directories with different purposes.

| Path on `dev` | Required contents | Purpose |
| --- | --- | --- |
| `/home/ec2-user/adjudication-build-2361886` | Service checkout containing `service/attested/arbd` | Docker build context for `arbattest-aard:dev` and `arbd-glue:poc`. |
| `/home/ec2-user/attest` | `exec.sh`, `parse_attestation.py`, and `run-aard.sh` | Runtime launcher directory used by `run-arbd-attested.py` and manual `exec.sh` commands. |
| `/home/ec2-user/arbattest-secrets/auth.json` | Codex auth JSON | Staged to S3 as the OpenClaw Codex auth file. |
| `/home/ec2-user/arbattest-secrets/keys.sh` | Shell assignments for provider keys | Staged to S3; must define `OPENROUTER_API_KEY` for the current Pi council pool. |
| `/home/ec2-user/arbd-glue-poc.tar` | Docker archive produced by `docker save arbd-glue:poc` | Uploaded to S3 for the exec AMI to download. |

`/home/ec2-user/attest` is the runtime directory used by the exec launcher.  Changes to `run-aard.sh` belong in `service/attested/arbd/run-aard.sh`.  Copy the reviewed version to the runtime directory before use.

## Host Software

The AARD build host inherits the generic `attest` requirements and adds Docker.  The verified host runs Amazon Linux 2023 with `aws`, `git`, `docker`, and Nix installed.  The `ec2-user` account must be able to run `sudo docker build`, `sudo docker save`, and `sudo chown` without an interactive password prompt.

Docker builds need enough root filesystem capacity for the AARD base image, the attested workload image, the saved image archive, and build cache.  A 32 GiB root volume with about 20 GiB free has worked after cleanup.  If the build fails because `/` is full, remove old Docker build cache, obsolete local images, and stale image tar files before rebuilding.

The local driver uses SSH and SCP to make `dev` read from S3, write case-packet inputs to S3, and copy artifacts back to the local output directory.  The current driver defaults to `DEV_HOST=dev` and `REMOTE_ATTEST_DIR=/home/ec2-user/attest`.  The caller also needs `uv` locally because verification runs `uv run attest/parse_attestation.py` after downloading the attestation.

## AWS Region, AMI, And Instance Profile

The verified region is `us-east-2`.  The current Docker-enabled exec AMI is `ami-011f957fe91cf7b81`, and the expected PCR values in the runbook correspond to that AMI.  Rebuilding the exec AMI requires recording the new AMI id and PCR values in the runbook and in commands that pass `--expected-pcr4` and `--expected-pcr7`.

The verified exec instance type is `m5.4xlarge`.  The exec AMI root filesystem is RAM-backed, and Docker extracts image layers into that RAM-backed filesystem.  Smaller instances can fail while loading the attested workload image because they do not have enough RAM-backed storage.

The verified instance profile is `ec2-nix-builder`.  The `dev` host role must be able to pass the role behind that instance profile when it launches the exec AMI.  The launched exec instance profile must have S3 permissions for the image tar, staged inputs, and run-output prefix.

## S3 Layout

The verified bucket is `s3://agentcourt-data` in `us-east-2`, with all AARD attestation objects under the `arbattest/` prefix.  Use timestamped child prefixes for inputs and outputs.  Do not reuse an output prefix, because a run prefix is a record of one remote execution.

| Prefix | Producer | Consumer | Contents |
| --- | --- | --- | --- |
| `s3://agentcourt-data/arbattest/images/` | `dev` Docker build step | Exec AMI | `arbd-glue-poc.tar`, the Docker archive loaded by `run-aard.sh`. |
| `s3://agentcourt-data/arbattest/aard-inputs/<example>-<stamp>/` | `dev` staging step | Exec workload container on exec AMI | `auth.json` and `keys.sh`. |
| `s3://agentcourt-data/arbattest/aard-runs/<run-id>/` | Exec workload container on exec AMI | `dev` polling, Clerk monitoring, and download steps | `events.ndjson` during execution, plus `run.log`, `aard-output.tar.gz`, `manifest.json`, `manifest.sha384`, and `attestation.b64` on success. |
| `s3://agentcourt-data/arbattest/aard-runs/<run-id>/` | Exec workload container on exec AMI | `dev` polling, Clerk monitoring, and download steps | `events.ndjson` if AARD created it, plus `run.log` and `aard-partial.tar.gz` on current AARD failure paths. |
| `s3://agentcourt-data/arbattest/container-poc/` | Container proof runs | Operator verification | Small proof outputs for the attested workload image in attestation-only mode. |

The output prefix is the attestation record location.  The launcher console output is not the record.  Clerk reads `events.ndjson` from this prefix while an attested run is active, then uses the downloaded local copy or extracted archive after the run completes.

Verification reads the downloaded S3 files, checks the manifest hash, checks archive hashes, parses `attestation.b64`, and verifies that Nitro TPM user data equals `manifest.sha384`.  The live `events.ndjson` object supports monitoring, but the verified event log is the copy inside the manifest-bound archive.  A complete success prefix has a small object count: five terminal objects plus the live event log.

## S3 Permissions

The `dev` host role needs S3 permissions for staging inputs, uploading images, polling output prefixes, downloading output artifacts, and cleanup.  Large Docker archive uploads can use multipart upload, so include the multipart actions.  Cleanup should be granted only to operators expected to delete test runs or obsolete images.

| Prefix | Required `dev` actions |
| --- | --- |
| `arn:aws:s3:::agentcourt-data` | `s3:ListBucket` with prefix conditions for `arbattest/images/`, `arbattest/aard-inputs/`, `arbattest/aard-runs/`, and `arbattest/container-poc/`; `s3:ListBucketMultipartUploads` for large archive uploads. |
| `arn:aws:s3:::agentcourt-data/arbattest/images/*` | `s3:PutObject`, `s3:GetObject`, `s3:AbortMultipartUpload`, `s3:ListMultipartUploadParts`, and optional `s3:DeleteObject`. |
| `arn:aws:s3:::agentcourt-data/arbattest/aard-inputs/*` | `s3:PutObject`, `s3:GetObject`, `s3:ListMultipartUploadParts`, and optional `s3:DeleteObject`. |
| `arn:aws:s3:::agentcourt-data/arbattest/aard-runs/*` | `s3:GetObject`, `s3:PutObject` for manual diagnostics, `s3:AbortMultipartUpload`, `s3:ListMultipartUploadParts`, and optional `s3:DeleteObject`. |
| `arn:aws:s3:::agentcourt-data/arbattest/container-poc/*` | `s3:GetObject`, `s3:PutObject`, and optional `s3:DeleteObject`. |

The launched exec instance profile needs narrower S3 permissions.  It reads the attested workload image tar and input secrets, then writes terminal run artifacts.  Grant list permission only for prefixes used by diagnostics or future scripts that enumerate objects.

| Prefix | Required launched-instance actions |
| --- | --- |
| `arn:aws:s3:::agentcourt-data/arbattest/images/*` | `s3:GetObject` |
| `arn:aws:s3:::agentcourt-data/arbattest/aard-inputs/*` | `s3:GetObject` |
| `arn:aws:s3:::agentcourt-data/arbattest/aard-runs/*` | `s3:PutObject`, `s3:AbortMultipartUpload`, `s3:ListMultipartUploadParts` |
| `arn:aws:s3:::agentcourt-data` | Optional `s3:ListBucket` with prefix conditions for diagnostics. |

If the bucket enforces SSE-KMS, add KMS permissions for the same actors.  Uploaders need `kms:Encrypt` and `kms:GenerateDataKey`.  Downloaders and verifiers need `kms:Decrypt` for objects they read.

## EC2 And IAM Permissions

The `dev` host role needs all generic `attest` runner permissions because the local AARD driver starts `/home/ec2-user/attest/exec.sh` on `dev`.  It also needs `iam:PassRole` for the role used by the `ec2-nix-builder` instance profile.  The launched instance does not need EC2 launch permissions for the current AARD run path.

| Actor | Required AWS actions |
| --- | --- |
| `dev` host role | Generic `attest` build and runner actions from `dev-host.md` in the external `attest` checkout, plus the S3 actions above. |
| `dev` host role when passing `ec2-nix-builder` | `iam:PassRole` on the role attached to the `ec2-nix-builder` instance profile. |
| Launched exec instance profile | S3 read/write actions above; no EC2 launch action is required by the current AARD exec path. |

The launched exec instance needs outbound network access.  It reads S3, starts Docker, runs OpenClaw lawyer containers, runs Pi council containers, and those agents call their configured providers.  The current run path uses `OPENROUTER_API_KEY` for the Pi council pool and Codex auth for OpenClaw.

## Secret Files

`/home/ec2-user/arbattest-secrets/auth.json` must be the Codex auth file OpenClaw can import.  The staging command copies it to `INPUT_PREFIX/auth.json`, and the exec container entrypoint mounts it into the OpenClaw Codex home.  The file should remain outside Git and outside served artifact directories.

`/home/ec2-user/arbattest-secrets/keys.sh` must assign or export `OPENROUTER_API_KEY`.  The exec container entrypoint sources it before running AARD and exits if the key is absent.  Add further provider keys there only when the selected council pool or lawyers require them.

The input S3 prefix currently stores these secret files as plain S3 objects subject to bucket policy and optional bucket encryption.  Limit read access to the launched exec instance profile and operators who need to diagnose a run.  Remove obsolete input prefixes when they are no longer needed, unless the run must preserve inputs for audit.

## Verification Configuration

The current lower-level command verifies the exec AMI with PCR4 and PCR7.  The expected PCR12 value defaults to all zeroes.  Store the expected PCR values with the AMI id and replace them whenever the exec AMI changes.

| Value | Current setting |
| --- | --- |
| Exec AMI | `ami-011f957fe91cf7b81` |
| Region | `us-east-2` |
| Instance type | `m5.4xlarge` |
| Instance profile | `ec2-nix-builder` |
| PCR4 | `83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4` |
| PCR7 | `98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35` |
| PCR12 | `000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000` |

Successful AARD verification checks `manifest.sha384`, the archive SHA-384, `run.log` SHA-384, the attestation signature and certificate chain, Nitro TPM user data, and the expected PCR values.  Current partial AARD runs do not produce a manifest or attestation.  That behavior should change before failed AARD runs are treated as attested terminal records.

## Operational Checks

Run these checks before rebuilding the attested workload image or launching a long run.  They verify the host layout, tool paths, source checkout, launcher directory, secrets, Docker access, AWS identity, and free disk capacity.  They do not launch EC2 instances or write S3 objects.

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
test -x /home/ec2-user/attest/run-aard.sh
test -f /home/ec2-user/arbattest-secrets/auth.json
test -f /home/ec2-user/arbattest-secrets/keys.sh
sudo docker ps >/dev/null
AWS_DEFAULT_REGION=us-east-2 aws sts get-caller-identity --output json
df -h / /tmp 2>/dev/null || df -h /
'
```

Run these S3 checks when the role should be able to read and write the AARD prefixes.  The second command writes and deletes a small probe object, so use it only when cleanup permission is expected.  Replace the bucket or prefix if the deployment uses a different S3 location.

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

The Clerk request path lives in the [AARD Service Manual](../../arbd/README.md).  The generic host and AMI requirements live in `dev-host.md` in the external `attest` checkout.  The AARD image build and run sequence lives in [AARD Docker Image Runbook](Dockerfile.md), while the lower-level runner and example wrapper live in this directory.
