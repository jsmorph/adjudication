# AAR Docker Image Runbook

## Scope

This runbook covers the AAR base image, attested workload image, and exec run under `service/attested/arb`.  The base image combines the core `aar` and `aarengine` binaries with the service `aar-run` launcher, the required core data, the Docker CLI, and an embedded Pi council root filesystem.  The attested workload image adds AWS CLI, `nitro-tpm-attest`, the TSS runtime libraries, and the exec container entrypoint.

The Clerk path uses the `aar-service` command and Clerk API.  Its request shape, service flags, monitoring route, artifact routes, and completion rule live in the [ARB Service Manual](../../arb/README.md).  This runbook covers the Docker image, exec AMI, S3 artifact flow, local driver, and verification procedure used by those service requests.

The attested path supports two AAR input modes.  Example mode runs a checked-in core directory under `arb/examples/<name>` selected by `AAR_EXAMPLE`; when the variable is absent, both `run-aar.sh` and the exec container entrypoint use `ex01`.  Case-packet mode runs a local complaint and optional case files by packaging them through `aar case-packet`, uploading `case.tar.gz` and `case-packet.json` under `INPUT_PREFIX`, and passing the extracted inputs to `aar-run`.

The exec input schema always reads `auth.json` and `keys.sh` from `INPUT_PREFIX`.  Example mode adds only the `AAR_EXAMPLE` selector.  Case-packet mode adds `case.tar.gz`, `case-packet.json`, `AAR_CASE_PACKET_SHA384`, and `AAR_CASE_MANIFEST_SHA384`, so the manifest and verifier bind the exact arbitrary case packet used by the exec instance.

## Files And Branches

| Item | Location | Role |
| --- | --- | --- |
| AAR base image | `service/attested/arb/Dockerfile` | Builds core at `CORE_COMMIT`, builds service at `SERVICE_COMMIT`, and assembles the AAR runtime image. |
| Attested workload image | `service/attested/arb/Dockerfile.glue` | Adds AWS CLI, `nitro-tpm-attest`, TSS libraries, and the S3 artifact flow. |
| Exec container entrypoint | `service/attested/arb/exec-container-entrypoint.sh` | Runs the selected AAR input, archives output, writes the manifest, obtains the TPM attestation, and uploads artifacts to S3. |
| Exec launcher | `attest/exec.sh` | Starts the Docker-enabled exec AMI with user-data from a script. |
| AAR exec script | `service/attested/arb/run-aar.sh` | Downloads the attested workload image tar on the exec AMI, loads it into Docker, and starts the exec workload container. |
| Local AAR driver | `service/attested/arb/run-arb-attested.py` | Starts `exec.sh` through `dev`, polls S3, downloads artifacts, extracts the AAR archive, and can verify the result. |
| Container proof script | `service/attested/arb/run-container-poc.sh` | Runs the attested workload image in `attest-only` mode for the container attestation proof. |
| Attestation parser | `attest/parse_attestation.py` | Verifies the attestation signature and certificate chain and prints user data and PCR values. |
| Dev source checkout | `/home/ec2-user/adjudication-build-2361886` on `dev` | Source tree used for Docker builds on `dev`. |
| Dev launcher directory | `/home/ec2-user/attest` on `dev` | Runtime directory for `exec.sh`, `run-aar.sh`, and helper scripts.  This directory is not the source-control checkout. |

Build from full 40-character core and service commit IDs.  The current Docker-enabled exec AMI is `ami-011f957fe91cf7b81` in `us-east-2`.  Its expected PCR values are listed in the verification section and must be replaced when the exec AMI is rebuilt.

## Dev Host And AWS Requirements

The generic `dev` host requirements for the exec AMI launcher live in `dev-host.md` in the external `attest` checkout.  That document covers the base x86_64 host, Nix daemon setup, AWS CLI, EC2 permissions, EBS direct snapshot permissions, role passing, default VPC assumptions, disk requirements, and verification commands.  Review it before building or launching through `attest/exec.sh`.

The AAR-specific requirements live in [Attested AAR Dev Host Requirements](attested-dev-host.md).  That document adds the Docker build checkout, launcher directory, secret file locations, S3 prefixes, S3 permissions, `ec2-nix-builder` instance profile, expected PCR values, and operational checks for attested AAR runs.  The `dev` host builds and uploads `arb-glue:poc`, stages `auth.json` and `keys.sh`, launches the exec AMI, polls the output prefix, downloads terminal artifacts, and supports verification.

## Attestation Record

The attestation record lives in S3, not stdout.  Stdout from `exec.sh` is useful for launch progress and the instance ID, but verification reads the S3 prefix.  During AAR execution, the exec container refreshes `events.ndjson` under `OUTPUT_PREFIX`; a completed run leaves that live event object with the terminal objects `run.log`, `aar-output.tar.gz`, `manifest.json`, `manifest.sha384`, and `attestation.b64`.

`events.ndjson` at the S3 prefix exists for live monitoring.  The verified event log remains the `events.ndjson` file inside `aar-output.tar.gz`, because the manifest binds the archive hash.  `manifest.sha384` contains the SHA-384 hash of `manifest.json`, and the exec container entrypoint passes that file to `nitro-tpm-attest --user-data`, so the attestation `User Data` field must equal the manifest hash.

The manifest binds the input mode, selected example or case-packet hashes, input prefix, output prefix, exec AMI, instance ID, attested workload image ID, attested workload image tar hash, run log hash, and AAR archive hash.  If `aar-run` exits nonzero, the attested workload image uploads `events.ndjson` if the run created it, uploads `run.log` and `aar-partial.tar.gz`, then exits with the launcher status.  A failed run has no `manifest.json`, `manifest.sha384`, or `attestation.b64`, so it has no attestation verification.

## Runtime Topology

The exec AMI runs Docker on the host.  `run-aar.sh` downloads `s3://agentcourt-data/arbattest/images/arb-glue-poc.tar`, computes its SHA-384 hash, loads `arb-glue:poc`, records the Docker image ID, and starts the exec workload container.  The container receives `/var/run/docker.sock`, `/dev/tpm0`, `/dev/tpmrm0` when present, `INPUT_PREFIX`, `OUTPUT_PREFIX`, `RUN_ID`, `AAR_INPUT_MODE`, `AAR_EXAMPLE`, optional case-packet fields, and image identity fields.

The exec workload container starts `/usr/local/bin/aar-run-entrypoint`, which supplies the installed core executable, engine, working directory, and common-data root to `aar-run`.  The launcher starts OpenClaw lawyer containers and Pi council containers through the host Docker daemon.  It passes `--openclaw-network host` so OpenClaw uses `127.0.0.1` for the AAR MCP server.

The parent and child containers share paths through the host Docker daemon, so AAR output must live under a path that the host Docker daemon can mount into child containers.  The exec path uses `ARB_EXEC_WORK_ROOT=/var/lib/arbattest-aar`, mounted into the exec workload container at the same absolute path.  The local direct-run command below follows the same rule by mounting the output root at the identical path inside the parent container.

## Required Inputs

The attested workload image reads secrets from S3 so the attested instance does not depend on SSH file transfer at run time.  `INPUT_PREFIX` must contain `auth.json` and `keys.sh`.  `auth.json` is the Codex auth file used by OpenClaw, and `keys.sh` must assign or export `OPENROUTER_API_KEY` for the Pi council.

The verified instance profile for the first version is the same profile used on `dev`, passed to `exec.sh` as `IAM_INSTANCE_PROFILE=ec2-nix-builder`.  The verified instance type is `m5.4xlarge`, because the exec AMI root filesystem is RAM-backed and Docker extracts image layers into that RAM-backed filesystem.  The verified region is `us-east-2`, and the verified S3 bucket prefix is `s3://agentcourt-data/arbattest/`.

Valid `AAR_EXAMPLE` values are core example directory names accepted by `aar-run`: nonempty, no slash, no dot prefix, and no `..`.  The distilled core retains `ex01` as its acceptance example.  The exec container entrypoint records the chosen example in `manifest.json` as `aar_example`.

Case-packet input uses `AAR_INPUT_MODE=case-packet`.  The local driver invokes the installed `aar case-packet` command, then uploads `case.tar.gz` and `case-packet.json` through `dev` and passes their SHA-384 hashes to the exec AMI.  The core packet builder applies complaint-directory scanning, explicit glob expansion, duplicate-basename rejection, and prohibited-extension checks; absent `--file` arguments select ordinary immediate case files, while explicit selectors limit the packet to their matches.

## Build The Base Image Locally

Run the base image build from the service repository root.  The Dockerfile clones `CORE_REPO` and `SERVICE_REPO`, fetches the commits named by `CORE_COMMIT` and `SERVICE_COMMIT`, and verifies both resulting `HEAD` values.  Both commit arguments must contain full 40-character lowercase commit IDs.

```bash
docker build --no-cache \
  --build-arg CORE_COMMIT="$CORE_COMMIT" \
  --build-arg SERVICE_COMMIT="$SERVICE_COMMIT" \
  -t arbattest-aar:local \
  -f service/attested/arb/Dockerfile \
  .
```

Validate any checked-in example complaint with the selected image.  This command tests that the image contains the example and that the complaint parses.  Replace `ex01` with any checked-in example name.

```bash
AAR_EXAMPLE=ex01
docker run --rm \
  --entrypoint /opt/core/arb/.bin/aar \
  arbattest-aar:local \
  validate --complaint "examples/$AAR_EXAMPLE/complaint.md"
```

The expected output is:

```text
ok
```

## Run An Example Locally Without Attestation

The local direct run exercises the AAR image, OpenClaw lawyers, and Pi council containers without the exec AMI.  It needs a readable Codex auth file at `tmp/auth.json`, a key file at `tmp/keys.sh`, and the host Docker socket.  It writes a timestamped output directory under `aar-out` and a sibling log file.

```bash
set -eu
AAR_EXAMPLE="${AAR_EXAMPLE:-ex01}"
. "$PWD/tmp/keys.sh"
output_root="$PWD/aar-out"
mkdir -p "$output_root"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
out="$output_root/$AAR_EXAMPLE-local-$stamp"
log="$output_root/$AAR_EXAMPLE-local-$stamp.log"
docker run --rm --network host \
  --user "$(id -u):$(id -g)" \
  --group-add "$(stat -c '%g' /var/run/docker.sock)" \
  -v /var/run/docker.sock:/var/run/docker.sock \
  -v "$output_root:$output_root" \
  -v "$PWD/tmp/auth.json:/run/secrets/codex-auth.json:ro" \
  -e OPENROUTER_API_KEY \
  arbattest-aar:local \
  --out-dir "$out" \
  --openclaw-auth codex \
  --openclaw-codex-auth /run/secrets/codex-auth.json \
  --openclaw-network host \
  --docker docker \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest \
  "$AAR_EXAMPLE" \
  >"$log" 2>&1
printf '%s\n' "$out"
printf '%s\n' "$log"
```

Read the local result after the command exits.  A completed run writes `local-run.json` with `status` and `resolution`.  The first completed local `ex01` run produced `status=ok` and `resolution=demonstrated`.

```bash
python3 -m json.tool "$out/local-run.json"
```

Check that the cleanup code removed runtime credential files from a new output directory.  The command should print no paths for current runs.  Older completed directories can contain files created before the cleanup fix.

```bash
find "$out" \
  \( -name .mcp.json -o -path '*/.pi/agent/auth.json' \) \
  -print
```

## Build And Upload The Attested Workload Image On `dev`

Build the base and attested workload images on `dev` from a service checkout, then upload the Docker archive used by `run-aar.sh`.  Set `CORE_COMMIT` and `SERVICE_COMMIT` to the reviewed full commit IDs before the build.  Record the printed SHA-384 hash because the entrypoint manifest records the image tar hash for each run.

```bash
ssh dev 'set -eu
cd /home/ec2-user/adjudication-build-2361886
CORE_COMMIT=REPLACE_WITH_40_CHARACTER_CORE_COMMIT
SERVICE_COMMIT=REPLACE_WITH_40_CHARACTER_SERVICE_COMMIT
sudo docker build --no-cache \
  --build-arg CORE_COMMIT="$CORE_COMMIT" \
  --build-arg SERVICE_COMMIT="$SERVICE_COMMIT" \
  -t arbattest-aar:dev \
  -f service/attested/arb/Dockerfile \
  .
sudo docker build --no-cache \
  --build-arg AAR_IMAGE=arbattest-aar:dev \
  -t arb-glue:poc \
  -f service/attested/arb/Dockerfile.glue \
  .
sudo docker save arb-glue:poc -o /home/ec2-user/arb-glue-poc.tar
sudo chown ec2-user:ec2-user /home/ec2-user/arb-glue-poc.tar
sha384sum /home/ec2-user/arb-glue-poc.tar
AWS_DEFAULT_REGION=us-east-2 \
  aws s3 cp /home/ec2-user/arb-glue-poc.tar \
  s3://agentcourt-data/arbattest/images/arb-glue-poc.tar
'
```

Validate the base image on `dev` after the build.  This command checks the selected example in the image that the attested workload image was based on.  It does not require runtime secrets.

```bash
ssh dev 'set -eu
AAR_EXAMPLE="${AAR_EXAMPLE:-ex01}"
sudo docker run --rm \
  --entrypoint /opt/core/arb/.bin/aar \
  arbattest-aar:dev \
  validate --complaint "examples/$AAR_EXAMPLE/complaint.md"
'
```

## Install The Exec Runner On `dev`

`/home/ec2-user/attest` on `dev` is the runtime launcher directory used by the AMI runner.  Copy generic exec files from `attest` and the AAR exec script from `service/attested/arb`.  The current `run-aar.sh` accepts `AAR_EXAMPLE`, defaults to `ex01`, passes it to the exec workload container, and names default runs as `aar-$AAR_EXAMPLE-$STAMP`.

```bash
ssh dev 'mkdir -p /home/ec2-user/attest'
scp attest/exec.sh attest/parse_attestation.py service/attested/arb/run-aar.sh dev:/home/ec2-user/attest/
ssh dev 'chmod 755 /home/ec2-user/attest/exec.sh /home/ec2-user/attest/run-aar.sh /home/ec2-user/attest/parse_attestation.py'
```

The runtime copy on `dev` executes the service-owned script.  `service/attested/arb/run-aar.sh` remains its reviewed source.  Record its service commit with the image build record.

## Prepare The S3 Input Prefix

Stage the runtime secret files in S3 before every run.  The input prefix is separate from the output prefix so a verifier can see exactly which S3 input location the manifest names.  In case-packet mode, the local driver also writes `case.tar.gz` and `case-packet.json` under the same input prefix before it starts the exec AMI.

```bash
ssh dev 'set -eu
AAR_EXAMPLE="${AAR_EXAMPLE:-ex01}"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
input_prefix="s3://agentcourt-data/arbattest/aar-inputs/$AAR_EXAMPLE-$stamp"
AWS_DEFAULT_REGION=us-east-2 aws s3 cp \
  /home/ec2-user/arbattest-secrets/auth.json \
  "$input_prefix/auth.json"
AWS_DEFAULT_REGION=us-east-2 aws s3 cp \
  /home/ec2-user/arbattest-secrets/keys.sh \
  "$input_prefix/keys.sh"
printf "INPUT_PREFIX=%s\n" "$input_prefix"
AWS_DEFAULT_REGION=us-east-2 aws s3 ls "$input_prefix/"
'
```

The `keys.sh` file must define `OPENROUTER_API_KEY`.  The exec container entrypoint sources that file inside the container and exits before AAR starts if the variable is absent.  For arbitrary local cases, use the local driver to create the packet; the driver writes deterministic packet objects and records their hashes in `run.env`.

## Run The Attested AAR

For Clerk-managed attested runs, start with the [ARB Service Manual](../../arb/README.md).  The commands here run the lower-level driver directly.  They also expose the S3 and verification path used by the service.

The example wrapper is `service/attested/arb/run-one-attested-arb.sh`.  It takes the path to an example directory from the selected core checkout and verifies that the directory contains `complaint.md`.  It stages `auth.json` and `keys.sh` into a fresh S3 input prefix, chooses timestamped input and output prefixes, starts the exec AMI, downloads the S3 artifacts, extracts the AAR archive, and verifies the attestation.

```bash
service/attested/arb/run-one-attested-arb.sh /path/to/core/arb/examples/ex01
```

The lower-level local driver is `service/attested/arb/run-arb-attested.py`.  It starts the exec AMI through `dev`, polls the S3 output prefix, writes progress and launcher logs under the local output directory, downloads all S3 artifacts into that directory, extracts the AAR archive, and can run verification.  The driver treats `run.log`, `aar-output.tar.gz`, `manifest.json`, `manifest.sha384`, and `attestation.b64` as the successful terminal set; `events.ndjson` can appear before that set and continues to be downloaded with the final artifacts.

```bash
uv run service/attested/arb/run-arb-attested.py \
  --example ex01 \
  --input-prefix s3://agentcourt-data/arbattest/aar-inputs/ex01-REPLACE_WITH_STAMP \
  --exec-ami ami-011f957fe91cf7b81 \
  --out-dir /tmp/aar-ex01-REPLACE_WITH_STAMP \
  --verify \
  --expected-pcr4 83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4 \
  --expected-pcr7 98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35
```

Run an arbitrary local case by replacing `--example` with `--complaint` and optional repeated `--file` flags.  The driver calls the installed core `aar case-packet` command before launch, creates `case.tar.gz` and `case-packet.json`, uploads them through `dev` to `INPUT_PREFIX`, and sends `AAR_INPUT_MODE=case-packet` to the exec AMI.  The exec workload container verifies the packet hashes before extraction, then starts `aar-run` with the extracted complaint and case files.

```bash
uv run service/attested/arb/run-arb-attested.py \
  --aar-bin /path/to/core/aar \
  --case-id arb-custom-REPLACE_WITH_STAMP \
  --run-id aar-custom-REPLACE_WITH_STAMP \
  --complaint work/my-case/complaint.md \
  --file 'work/my-case/*.txt' \
  --input-prefix s3://agentcourt-data/arbattest/aar-inputs/custom-REPLACE_WITH_STAMP \
  --exec-ami ami-011f957fe91cf7b81 \
  --out-dir /tmp/aar-custom-REPLACE_WITH_STAMP \
  --verify \
  --expected-pcr4 83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4 \
  --expected-pcr7 98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35
```

The output directory receives `run.env`, `progress.log`, `launcher.log`, the downloaded S3 artifacts, `attestation.txt` when verification runs, `verification.log` when verification runs, and either `aar-output/` or `aar-partial/` extracted from the archive.  When the exec container has published live events, the top-level downloaded artifacts include `events.ndjson`; after archive extraction, the canonical event log is also present under `aar-output/events.ndjson` or `aar-partial/events.ndjson`.  The driver defaults to `DEV_HOST=dev`, `AWS_REGION=us-east-2`, `INSTANCE_TYPE=m5.4xlarge`, `IAM_INSTANCE_PROFILE=ec2-nix-builder`, `IMAGE_TAR_S3=s3://agentcourt-data/arbattest/images/arb-glue-poc.tar`, and `REMOTE_ATTEST_DIR=/home/ec2-user/attest`.

The manual command below is the same example execution path without the local driver.  Run the exec AMI from `/home/ec2-user/attest` on `dev`.  Pass `RUN_ID` and `OUTPUT_PREFIX` explicitly so the verifier does not need to recover them from console output.  Set `AAR_EXAMPLE` to any checked-in example name.

```bash
ssh dev 'set -eu
cd /home/ec2-user/attest
AAR_EXAMPLE=ex01
INPUT_PREFIX=s3://agentcourt-data/arbattest/aar-inputs/ex01-REPLACE_WITH_STAMP
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
RUN_ID="${RUN_ID:-aar-$AAR_EXAMPLE-$stamp}"
OUTPUT_PREFIX="${OUTPUT_PREFIX:-s3://agentcourt-data/arbattest/aar-runs/$RUN_ID}"
env \
  AWS_DEFAULT_REGION=us-east-2 \
  INSTANCE_TYPE=m5.4xlarge \
  IAM_INSTANCE_PROFILE=ec2-nix-builder \
  POLL_ATTEMPTS=1800 \
  EXEC_ENV_VARS=INPUT_PREFIX,IMAGE_TAR_S3,AAR_INPUT_MODE,AAR_EXAMPLE,RUN_ID,OUTPUT_PREFIX \
  INPUT_PREFIX="$INPUT_PREFIX" \
  IMAGE_TAR_S3=s3://agentcourt-data/arbattest/images/arb-glue-poc.tar \
  AAR_INPUT_MODE=example \
  AAR_EXAMPLE="$AAR_EXAMPLE" \
  RUN_ID="$RUN_ID" \
  OUTPUT_PREFIX="$OUTPUT_PREFIX" \
  ./exec.sh ami-011f957fe91cf7b81 /home/ec2-user/attest/run-aar.sh
printf "RUN_ID=%s\n" "$RUN_ID"
printf "OUTPUT_PREFIX=%s\n" "$OUTPUT_PREFIX"
'
```

`exec.sh` prints the EC2 instance ID after launch and terminates the instance on normal exit.  The current launcher still depends on EC2 console output to notice `ATTESTATION END`, while the attestation record lives in S3.  If S3 contains a complete verified result and the launcher keeps polling, use the printed instance ID to inspect or terminate that instance.

## Download The Result For Verification

Use local AWS credentials when available.  This path keeps verification in the local workspace where `uv` is available for the parser.  The same commands work for any `RUN_ID` and `OUTPUT_PREFIX`.

```bash
RUN_ID=aar-ex01-REPLACE_WITH_STAMP
OUTPUT_PREFIX="s3://agentcourt-data/arbattest/aar-runs/$RUN_ID"
LOCAL="/tmp/$RUN_ID"
mkdir -p "$LOCAL"
aws s3 cp "$OUTPUT_PREFIX/" "$LOCAL/" --recursive
find "$LOCAL" -maxdepth 1 -type f -printf '%f\n' | sort
```

If only `dev` has S3 access, download there and copy the small artifact set back.  The successful archive path has five terminal S3 objects plus `events.ndjson`, so this transfer should remain small.  A large object count means the archive path regressed and needs diagnosis before more runs.

```bash
RUN_ID=aar-ex01-REPLACE_WITH_STAMP
OUTPUT_PREFIX="s3://agentcourt-data/arbattest/aar-runs/$RUN_ID"
ssh dev "set -eu
LOCAL=/tmp/$RUN_ID
mkdir -p \"\$LOCAL\"
AWS_DEFAULT_REGION=us-east-2 aws s3 cp '$OUTPUT_PREFIX/' \"\$LOCAL/\" --recursive
find \"\$LOCAL\" -maxdepth 1 -type f -printf '%f\n' | sort
"
scp -r "dev:/tmp/$RUN_ID" /tmp/
```

The expected successful object list is:

```text
aar-output.tar.gz
attestation.b64
events.ndjson
manifest.json
manifest.sha384
run.log
```

## Verify The Manifest And Archive

Run these checks from the local workspace root.  Set `AAR_INPUT_MODE`, `AAR_EXAMPLE` for example runs, `OUTPUT_PREFIX`, and `LOCAL` to the run under review.  The script checks the manifest hash, selected input, output prefix, run log hash, archive hash, and archive byte count.

```bash
set -eu
AAR_INPUT_MODE=example
AAR_EXAMPLE=ex01
RUN_ID=aar-ex01-REPLACE_WITH_STAMP
OUTPUT_PREFIX="s3://agentcourt-data/arbattest/aar-runs/$RUN_ID"
LOCAL="/tmp/$RUN_ID"
cd "$LOCAL"
python3 - "$AAR_INPUT_MODE" "$AAR_EXAMPLE" "$OUTPUT_PREFIX" <<'PY'
import hashlib
import json
import sys
from pathlib import Path

expected_mode, expected_example, expected_output = sys.argv[1:4]

def sha384(path: str) -> str:
    h = hashlib.sha384()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

manifest = json.loads(Path("manifest.json").read_text())
checks = [
    ("manifest.sha384", sha384("manifest.json") == Path("manifest.sha384").read_text().strip()),
    ("mode", manifest.get("mode") == "aar"),
    ("input_mode", manifest.get("input_mode") == expected_mode),
    ("output_prefix", manifest.get("output_prefix") == expected_output),
    ("archive_key", manifest.get("aar_archive_key") == expected_output.rstrip("/") + "/aar-output.tar.gz"),
    ("run.log sha384", sha384("run.log") == manifest.get("log_sha384")),
    ("archive sha384", sha384("aar-output.tar.gz") == manifest.get("aar_archive_sha384")),
    ("archive bytes", str(Path("aar-output.tar.gz").stat().st_size) == manifest.get("aar_archive_bytes")),
    ("container image id present", bool(manifest.get("container_image_id"))),
    ("container tar hash present", bool(manifest.get("container_image_tar_sha384"))),
]
if expected_mode == "example":
    checks.append(("aar_example", manifest.get("aar_example") == expected_example))
else:
    checks.extend([
        ("case_packet key present", bool(manifest.get("case_packet_key"))),
        ("case_packet sha384 present", bool(manifest.get("case_packet_sha384"))),
        ("case_manifest key present", bool(manifest.get("case_manifest_key"))),
        ("case_manifest sha384 present", bool(manifest.get("case_manifest_sha384"))),
    ])
failed = [name for name, ok in checks if not ok]
if failed:
    for name in failed:
        print(f"failed: {name}")
    sys.exit(1)
print("manifest and archive checks passed")
PY
```

Inspect the AAR result inside the archive.  A completed run should report `status=ok`; the resolution depends on the case.  The verified `ex01` run reported `resolution=demonstrated`.

```bash
tar -xOf aar-output.tar.gz ./local-run.json | python3 -m json.tool
```

Confirm that the archive excludes the large per-agent homes and staged OpenClaw Codex directories.  This check should print only `archive exclusion check passed`.  Any printed path means the archive contains data that should have stayed out of S3.

```bash
if tar -tzf aar-output.tar.gz | grep -E '^\./(pi-|openclaw-[^/]+-codex)(/|$)'; then
  echo "error: archive contains excluded runtime directory" >&2
  exit 1
fi
echo "archive exclusion check passed"
```

## Verify The Attestation

Run the attestation parser from the local workspace root.  The parser verifies the COSE signature and certificate chain, then prints the `User Data` field and all NitroTPM PCR values.  The current parser uses `uv`; `uv` is available locally at `/home/somebody/.local/bin/uv` in the verified environment and is absent on `dev`.

```bash
set -eu
RUN_ID=aar-ex01-REPLACE_WITH_STAMP
LOCAL="/tmp/$RUN_ID"
UV="${UV:-/home/somebody/.local/bin/uv}"
cd /media/hd2/src/arbattest
"$UV" run attest/parse_attestation.py "$LOCAL/attestation.b64" > "$LOCAL/attestation.txt"
sed -n '1,40p' "$LOCAL/attestation.txt"
```

Compare the attestation output against the manifest hash and the expected exec AMI PCR values.  These values apply to `ami-011f957fe91cf7b81`; replace them after rebuilding the exec AMI.  PCR12 is all zeros for the current verified run.

```bash
set -eu
RUN_ID=aar-ex01-REPLACE_WITH_STAMP
LOCAL="/tmp/$RUN_ID"
EXPECTED_PCR4=83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4
EXPECTED_PCR7=98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35
EXPECTED_PCR12=000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
MANIFEST_SHA384="$(cat "$LOCAL/manifest.sha384")"
grep -q '^Signature: VALID' "$LOCAL/attestation.txt"
grep -q "^User Data: $MANIFEST_SHA384$" "$LOCAL/attestation.txt"
grep -q "^PCR  4: $EXPECTED_PCR4$" "$LOCAL/attestation.txt"
grep -q "^PCR  7: $EXPECTED_PCR7$" "$LOCAL/attestation.txt"
grep -q "^PCR 12: $EXPECTED_PCR12$" "$LOCAL/attestation.txt"
echo "attestation checks passed"
```

The reference `ex01` run `aar-ex01-20260612T001855Z` verified with manifest SHA-384 `ae52d9b5acccd76a45ce0e6c8f3cabf8e775ddb20e0761702fa1d73e15dffdcab080a0be859556170aaa3a23e9971f41` and archive SHA-384 `ce42ae939df866a2919f20ff8ccd5ffc86df0ffc0f7376b84811f9ae0a44dac8b664b4aaf0a7913b25677a2a7fc75bb0`.  Its attestation `User Data` matched the manifest hash.  That run predates the `aar_example` manifest field; use the manifest script above for runs made with the current attested workload image.

## Run Any Arb

Use example mode for cases that live under `arb/examples/<name>` at the selected core commit.  Rebuild the image with the selected core and service commit IDs, upload the attested workload image tar from `dev`, and install the corresponding `service/attested/arb/run-aar.sh` in `/home/ec2-user/attest`.  Stage `auth.json` and `keys.sh` under a new S3 input prefix, run the exec AMI with `AAR_INPUT_MODE=example` and `AAR_EXAMPLE=<name>`, and verify the resulting output prefix.

Use case-packet mode for a local case directory or an explicit complaint path outside the image.  Stage `auth.json` and `keys.sh` under a new S3 input prefix, then run `service/attested/arb/run-arb-attested.py --aar-bin PATH --complaint PATH` with any repeated `--file` selectors.  The driver uploads the deterministic packet before launch, and the manifest records the S3 keys and SHA-384 hashes for both `case.tar.gz` and `case-packet.json`.

Use a fresh `RUN_ID` and `OUTPUT_PREFIX` for every run.  The recommended naming form is `aar-$AAR_EXAMPLE-$STAMP` for examples and `aar-case-$STAMP` or a case-specific `aar-$NAME-$STAMP` for case packets, with `STAMP` from `date -u +%Y%m%dT%H%M%SZ`.  Timestamped prefixes keep failed, partial, and verified runs separate and make S3 cleanup decisions explicit.

The manifest is the boundary for later verification.  It names the selected input mode, example name or case-packet hashes, input prefix, output prefix, image identity, image tar hash, log hash, and archive hash.  Verification should treat the manifest hash in the attestation `User Data` field, plus matching PCR values, as the link between the attested exec AMI and the exact S3 artifacts.

## First-Failure Checks

Read `run.log` first.  For a successful run, read it from the downloaded artifact directory.  For a failed AAR run, download `run.log` and `aar-partial.tar.gz` from the output prefix and inspect `local-run.json` inside the partial archive if it exists.

Use the first concrete failing line as the diagnostic start.  An output prefix without `manifest.json`, `manifest.sha384`, and `attestation.b64` has no verified attestation.  Do not infer success from console output when S3 artifacts disagree.

| Symptom | Cause already diagnosed | Fix already used |
| --- | --- | --- |
| Docker layer extraction fails with `no space left on device` on the exec AMI. | The exec AMI root filesystem is RAM-backed, and Docker writes into that RAM-backed filesystem. | Use `m5.4xlarge` for the verified path. |
| `OPENROUTER_API_KEY is required`. | `keys.sh` was absent from `INPUT_PREFIX`, unreadable, or did not define the variable. | Upload `keys.sh` to the input prefix and verify it defines `OPENROUTER_API_KEY`. |
| OpenClaw cannot read `/aar-codex/auth.json`. | The child container runs as user `node` and needs world-readable staged Codex auth in this private AMI flow. | Current AAR code stages the Codex home with mode `0777` and `auth.json` with mode `0666`. |
| OpenClaw reports a stream disconnect on the exec AMI while the same request works on `dev`. | The diagnosed exec path failed when child OpenClaw used Docker bridge networking and passed when it used host networking. | Current entrypoint passes `--openclaw-network host`. |
| S3 prefix contains tens of thousands of AAR objects. | The old entrypoint success path recursively uploaded the AAR output tree, including Pi package trees. | Current entrypoint uploads one `aar-output.tar.gz` or one `aar-partial.tar.gz`. |
| `exec.sh` keeps polling after S3 has complete artifacts. | EC2 console output did not show the final marker even though S3 had the verified record. | Verify the S3 artifacts, then use the printed instance ID to inspect or terminate the instance. |

## Cleanup

Keep completed output prefixes that have been cited in notes or commits.  Delete failed experimental prefixes only after recording the cause and confirming that no later diagnosis depends on them.  The old recursive upload prefix was deleted after it was identified as an obsolete failure mode and the archive upload path replaced it.

Docker build cache and old image tars on `dev` can consume the root volume used by builds.  Check disk usage before a rebuild, especially after repeated `--no-cache` builds.  Remove obsolete rebuild artifacts only after confirming the current uploaded image tar hash and the current source commit.
