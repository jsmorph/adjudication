# ADC Docker Image Runbook

## Scope

This runbook covers the ADC base image, attested workload image, and exec run under `service/attested/adc`.  The base image combines the core `adc` and `adcengine` binaries with the service `adc-run` launcher, the required core court and shared data, the Docker CLI, and an embedded Pi juror root filesystem.  The attested workload image adds AWS CLI, `nitro-tpm-attest`, TSS runtime libraries, and the exec container entrypoint.

The current ADC attested path supports complaint input only.  The local driver packages a local `complaint_path` and its linked local Markdown files into `case.tar.gz` and `case-packet.json`, uploads those objects under `INPUT_PREFIX`, and passes the extracted complaint path to `adc-run`.  Scenario input, examples, and local runtime overrides are local-service features until the attested path has explicit support for them.

## Files And Branches

| Item | Location | Role |
| --- | --- | --- |
| ADC base image | `service/attested/adc/Dockerfile` | Builds core at `CORE_COMMIT`, builds service at `SERVICE_COMMIT`, and assembles the ADC runtime image. |
| Attested workload image | `service/attested/adc/Dockerfile.glue` | Adds AWS CLI, `nitro-tpm-attest`, TSS libraries, and the S3 artifact flow. |
| Exec container entrypoint | `service/attested/adc/exec-container-entrypoint.sh` | Runs `adc-run`, uploads live events, archives output, writes the manifest, obtains the TPM attestation, and uploads artifacts to S3. |
| Exec script | `service/attested/adc/run-adc.sh` | Loads `adc-glue:poc` on the exec AMI and starts the attested workload container. |
| Local driver | `service/attested/adc/run-adc-attested.py` | Uses the installed core `adc` command to build the complaint packet, starts `exec.sh` through `dev`, downloads artifacts, and verifies the attestation. |
| One-run helper | `service/attested/adc/run-one-attested-adc.sh` | Stages `auth.json` and `keys.sh`, chooses run-specific S3 prefixes, and invokes the local driver for one complaint. |
| Container proof script | `service/attested/adc/run-container-poc.sh` | Runs the attested workload image in attestation-only mode. |
| Clerk service | `adc-service` | Starts local or attested ADC cases through `/clerk/v1/cases`. |

The generic exec AMI launcher lives under `attest`.  The launcher directory on `dev` is `/home/ec2-user/attest`, and that directory must contain `exec.sh`, `parse_attestation.py`, and `run-adc.sh`.  Build each image from full 40-character core and service commit IDs so the image records the reviewed pair.

## Dev Host And AWS Requirements

The generic `dev` host requirements for the exec AMI launcher live in [Dev Host Requirements](../../../attest/dev-host.md).  Read that document before building or launching through `attest/exec.sh`.  It covers the base x86_64 host, Nix daemon setup, AWS CLI, EC2 permissions, EBS direct snapshot permissions, role passing, default VPC assumptions, disk requirements, and verification commands.

ADC-specific requirements live in [Attested ADC Dev Host Requirements](attested-dev-host.md).  The ADC document adds Docker image build requirements, S3 prefixes, secret file locations, instance profile requirements, expected PCR values, and operational checks.  The verified first path uses `us-east-2`, `m5.4xlarge`, `ec2-nix-builder`, `s3://agentcourt-data/arbattest/images/adc-glue-poc.tar`, `s3://agentcourt-data/arbattest/adc-inputs/`, and `s3://agentcourt-data/arbattest/adc-runs/`.

## Attestation Record

The attestation record lives in S3.  The local driver uses stdout from `exec.sh` only for progress and instance-id discovery, then reads terminal artifacts from the configured S3 output prefix.  A successful run leaves `run.log`, `manifest.json`, `manifest.sha384`, `attestation.b64`, `adc-output.tar.gz`, and a live `events.ndjson` object under `OUTPUT_PREFIX`.

The live `events.ndjson` object supports monitoring while ADC is running.  The verified event log remains the copy inside `adc-output.tar.gz`, because the manifest binds the archive hash.  `manifest.sha384` contains the SHA-384 hash of `manifest.json`, and the exec container passes that file to `nitro-tpm-attest --user-data`, so the attestation user data must equal the manifest hash.

The manifest binds the input mode, case-packet object hashes, input prefix, output prefix, exec AMI, instance ID, workload image ID, workload image tar hash, run log hash, and ADC output archive hash.  If `adc-run` exits nonzero, the container uploads `run.log`, `adc-partial.tar.gz`, and any available live events, then exits with failure.  A failed ADC run does not produce a verified completion record through the current driver path.

## Build Locally

Run the base image build from the service repository root.  The Dockerfile clones `CORE_REPO` and `SERVICE_REPO`, fetches the commits named by `CORE_COMMIT` and `SERVICE_COMMIT`, and verifies both resulting `HEAD` values.  Both commit arguments must contain full 40-character lowercase commit IDs.

```bash
docker build --no-cache \
  --build-arg CORE_COMMIT="$CORE_COMMIT" \
  --build-arg SERVICE_COMMIT="$SERVICE_COMMIT" \
  -t arbattest-adc:local \
  -f service/attested/adc/Dockerfile \
  .
```

Build the attested workload image from the same directory.  The glue build uses the ADC base image as its parent and adds the attestation entrypoint.  The image name used by the exec script is `adc-glue:poc`.

```bash
docker build --no-cache \
  --build-arg ADC_IMAGE=arbattest-adc:local \
  -t adc-glue:poc \
  -f service/attested/adc/Dockerfile.glue \
  .
```

Validate the base image before a long run.  This command checks that the installed core command can read a complaint directory and build the deterministic packet consumed by the service driver.  It does not start OpenClaw, Pi, Docker-in-Docker, or the exec AMI.

```bash
CASE_DIR=/path/to/case
COMPLAINT=complaint.md
docker run --rm \
  -v "$CASE_DIR:/case:ro" \
  --entrypoint /opt/core/adc/.bin/adc \
  arbattest-adc:local \
  case-packet \
  --complaint "/case/$COMPLAINT" \
  --packet /tmp/case.tar.gz \
  --manifest /tmp/case-packet.json
```

## Build And Upload On `dev`

Build on `dev` from the service checkout.  Set `CORE_COMMIT` and `SERVICE_COMMIT` to the reviewed full commit IDs, then save the glue image as a Docker archive and upload it to S3.  Record the SHA-384 hash because the exec entrypoint records that value in each manifest.

```bash
ssh dev 'set -eu
cd /home/ec2-user/adjudication-build-2361886
CORE_COMMIT=REPLACE_WITH_40_CHARACTER_CORE_COMMIT
SERVICE_COMMIT=REPLACE_WITH_40_CHARACTER_SERVICE_COMMIT
sudo docker build --no-cache \
  --build-arg CORE_COMMIT="$CORE_COMMIT" \
  --build-arg SERVICE_COMMIT="$SERVICE_COMMIT" \
  -t arbattest-adc:dev \
  -f service/attested/adc/Dockerfile \
  .
sudo docker build --no-cache \
  --build-arg ADC_IMAGE=arbattest-adc:dev \
  -t adc-glue:poc \
  -f service/attested/adc/Dockerfile.glue \
  .
sudo docker save adc-glue:poc -o /home/ec2-user/adc-glue-poc.tar
sudo chown ec2-user:ec2-user /home/ec2-user/adc-glue-poc.tar
sha384sum /home/ec2-user/adc-glue-poc.tar
AWS_DEFAULT_REGION=us-east-2 \
  aws s3 cp /home/ec2-user/adc-glue-poc.tar \
  s3://agentcourt-data/arbattest/images/adc-glue-poc.tar
'
```

Install the runner file into the launcher directory.  This directory is the runtime directory used by `exec.sh`, while the reviewed source remains under `service/attested/adc`.  Copy the reviewed service version whenever `run-adc.sh` changes.

```bash
ssh dev 'mkdir -p /home/ec2-user/attest'
scp attest/exec.sh attest/parse_attestation.py service/attested/adc/run-adc.sh dev:/home/ec2-user/attest/
ssh dev 'chmod 755 /home/ec2-user/attest/exec.sh /home/ec2-user/attest/run-adc.sh /home/ec2-user/attest/parse_attestation.py'
```

## Prepare Inputs

`INPUT_PREFIX` must contain `auth.json` and `keys.sh`.  `auth.json` is the Codex auth file used by OpenClaw, and `keys.sh` must assign or export `OPENROUTER_API_KEY` for Pi jurors.  The local driver uploads `case.tar.gz` and `case-packet.json` into the same prefix before launching the exec AMI.  The one-run helper stages both secret objects before invoking the driver.

```bash
ssh dev 'set -eu
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
input_prefix="s3://agentcourt-data/arbattest/adc-inputs/adc-$stamp"
AWS_DEFAULT_REGION=us-east-2 aws s3 cp \
  /home/ec2-user/arbattest-secrets/auth.json \
  "$input_prefix/auth.json"
AWS_DEFAULT_REGION=us-east-2 aws s3 cp \
  /home/ec2-user/arbattest-secrets/keys.sh \
  "$input_prefix/keys.sh"
printf "INPUT_PREFIX=%s\n" "$input_prefix"
'
```

The complaint packet is deterministic for the same complaint and linked files.  ADC reads Markdown links with the same loader used by local complaint setup, and every linked local file must live under the complaint directory.  The packet keeps the complaint at `case/<complaint basename>` and linked files under their same relative paths, so existing relative Markdown links continue to work after extraction.

## Run Through The Local Driver

The local driver is the normal operator path.  It builds the complaint packet locally, uploads packet objects through `dev`, starts the exec AMI, polls the output prefix, downloads terminal artifacts, extracts `adc-output.tar.gz`, and verifies the attestation when `--verify` is set.  Use the helper for ordinary one-complaint runs because it stages the two required secret objects before calling the driver.  Use fresh input and output prefixes for each run.

```bash
CORE_ROOT=/path/to/carve
ADC_BIN="$CORE_ROOT/adc/.bin/adc" \
service/attested/adc/run-one-attested-adc.sh \
  PATH/TO/complaint.md
```

```bash
CORE_ROOT=/path/to/carve
uv run service/attested/adc/run-adc-attested.py \
  --adc-bin "$CORE_ROOT/adc/.bin/adc" \
  --case-id adc-custom-REPLACE_WITH_STAMP \
  --run-id adc-custom-REPLACE_WITH_STAMP \
  --complaint "$CORE_ROOT/adc/examples/ex1/complaint.md" \
  --input-prefix s3://agentcourt-data/arbattest/adc-inputs/adc-REPLACE_WITH_STAMP \
  --exec-ami ami-011f957fe91cf7b81 \
  --out-dir /tmp/adc-custom-REPLACE_WITH_STAMP \
  --verify \
  --expected-pcr4 83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4 \
  --expected-pcr7 98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35
```

The output directory receives `run.env`, `progress.log`, `launcher.log`, `case.tar.gz`, `case-packet.json`, downloaded S3 artifacts, `attestation.txt`, `verification.log`, and either `adc-output/` or `adc-partial/`.  A successful verified run has `adc-output/run.json`, `adc-output/events.ndjson`, `adc-output/digest.md`, and any submitted evidence files.  The driver defaults to `DEV_HOST=dev`, `AWS_REGION=us-east-2`, `INSTANCE_TYPE=m5.4xlarge`, `IAM_INSTANCE_PROFILE=ec2-nix-builder`, `IMAGE_TAR_S3=s3://agentcourt-data/arbattest/images/adc-glue-poc.tar`, and `REMOTE_ATTEST_DIR=/home/ec2-user/attest`.

## Clerk Service End-To-End

The clerk service can start the same attested path with `execution.mode = "attested"`.  The service runs the local driver as a child process, stores the driver output in the case output directory, exposes live attestation events through HTTP, and marks the case `completed` only after verification succeeds.  This sequence uses separate core and service checkouts and passes every executable and working directory explicitly.

Prepare one run by choosing a case id, run id, local service output root, and S3 input prefix.  The input prefix must contain the secret files before the create request is posted, because the service driver writes only `case.tar.gz` and `case-packet.json` into that prefix.  The same prefix is recorded in `manifest.json`, so use a fresh prefix for each run.

```bash
CORE_ROOT=/path/to/carve
SERVICE_ROOT=/path/to/service
cd "$SERVICE_ROOT"

make -C "$CORE_ROOT/adc" build
mkdir -p .bin
go build -buildvcs=false -o .bin/adc-service ./cmd/adc-service
go build -buildvcs=false -o .bin/adc-run ./cmd/adc-run

stamp="$(date -u +%Y%m%dT%H%M%SZ)"
case_id="adc-attested-ex1-$stamp"
run_id="run-$case_id"
service_root="/tmp/adc-attested-service-$stamp"
input_prefix="s3://agentcourt-data/arbattest/adc-inputs/$case_id"
output_root="s3://agentcourt-data/arbattest/adc-runs"

mkdir -p "$service_root"

ssh dev "set -eu
AWS_DEFAULT_REGION=us-east-2 aws s3 cp /home/ec2-user/arbattest-secrets/auth.json '$input_prefix/auth.json' --no-progress
AWS_DEFAULT_REGION=us-east-2 aws s3 cp /home/ec2-user/arbattest-secrets/keys.sh '$input_prefix/keys.sh' --no-progress
AWS_DEFAULT_REGION=us-east-2 aws s3 ls '$input_prefix/'"
```

Start the service with attestation defaults.  Leave `--attested-exec-poll-attempts` unset unless a run has a specific reason to override it; the driver derives the exec console polling limit from `--attested-timeout-seconds` with ten minutes of headroom.  The service output root is local and separate from the S3 output root.

```bash
.bin/adc-service \
  --listen 127.0.0.1:19870 \
  --output-root "$service_root" \
  --adc-bin "$CORE_ROOT/adc/.bin/adc" \
  --adc-run-bin "$SERVICE_ROOT/.bin/adc-run" \
  --adc-working-dir "$CORE_ROOT/adc" \
  --engine "$CORE_ROOT/adc/.bin/adcengine" \
  --attested-driver "$SERVICE_ROOT/service/attested/adc/run-adc-attested.py" \
  --attested-uv uv \
  --attested-input-prefix "$input_prefix" \
  --attested-output-root "$output_root" \
  --attested-exec-ami ami-011f957fe91cf7b81 \
  --attested-expected-pcr4 83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4 \
  --attested-expected-pcr7 98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35 \
  > "$service_root/service.log" 2>&1 &

service_pid="$!"
printf 'SERVICE_PID=%s\n' "$service_pid" > "$service_root/service.env"

ready=0
for attempt in $(seq 1 30); do
  if curl -fsS http://127.0.0.1:19870/clerk/v1/cases > "$service_root/service-ready.json"; then
    ready=1
    break
  fi
  sleep 1
done
test "$ready" = 1
```

Create an attested ADC case through the same service API.  The request shape matches the local clerk create API for the case input: `complaint_path` is the complaint path, `case_id` and `run_id` are optional, and omitted `out_dir` makes the service use `OUTPUT_ROOT/CASE_ID`.  Attested ADC currently rejects `scenario_path` and local runtime fields such as model overrides, Docker commands, jury overrides, and OpenClaw options.

```bash
cat > "$service_root/create.json" <<EOF
{
  "mode": "run",
  "case_id": "$case_id",
  "run_id": "$run_id",
  "complaint_path": "$CORE_ROOT/adc/examples/ex1/complaint.md",
  "execution": {
    "mode": "attested",
    "attestation": {
      "verify": true
    }
  }
}
EOF

curl -sS -X POST http://127.0.0.1:19870/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data @"$service_root/create.json" \
  > "$service_root/create-response.json"
```

Monitor the service record and event stream through HTTP.  While the driver is running, `/attestation/events` reads the live S3 `events.ndjson` object when the local output copy is absent.  After completion, artifact, result, and evidence routes read from the extracted `adc-output/` directory.

```bash
curl -sS "http://127.0.0.1:19870/clerk/v1/cases/$case_id" \
  > "$service_root/record.json"

curl -sS "http://127.0.0.1:19870/clerk/v1/cases/$case_id/attestation/events" \
  > "$service_root/events.ndjson"

python3 -c 'import json, sys
record = json.load(open(sys.argv[1]))
att = ((record.get("execution") or {}).get("attestation") or {})
print("status=" + str(record.get("status")))
print("attestation=" + str(att.get("status")))
print("exit_code=" + str(record.get("exit_code")))
' "$service_root/record.json"
```

Poll manually until the record reaches `completed`, `failed`, or `killed`.  During a long run, compare the record status with the event count and with `progress.log`; an increasing event count means ADC is still making case progress.  The local case directory is `$service_root/$case_id`, and the driver logs are `$service_root/$case_id/progress.log` and `$service_root/$case_id/launcher.log`.

```bash
while :; do
  curl -sS "http://127.0.0.1:19870/clerk/v1/cases/$case_id" \
    > "$service_root/record.json"
  curl -sS "http://127.0.0.1:19870/clerk/v1/cases/$case_id/attestation/events" \
    > "$service_root/events.ndjson"
  python3 -c 'import json, sys
record = json.load(open(sys.argv[1]))
att = ((record.get("execution") or {}).get("attestation") or {})
print("status=" + str(record.get("status")) + " attestation=" + str(att.get("status")) + " exit_code=" + str(record.get("exit_code")))
' "$service_root/record.json"
  wc -l "$service_root/events.ndjson"
  status="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1])).get("status", ""))' "$service_root/record.json")"
  case "$status" in
    completed|failed|killed)
      break
      ;;
  esac
  sleep 30
done
```

Inspect the completed run through the service API and the local output directory.  A completed attested record must have `execution.attestation.status` equal to `verified`, an exit code of zero, a readable `verification.log`, and an extracted `adc-output/run.json`.  The terminal S3 prefix should contain a small object set: `events.ndjson`, `run.log`, `adc-output.tar.gz`, `manifest.json`, `manifest.sha384`, and `attestation.b64`.

```bash
curl -sS "http://127.0.0.1:19870/clerk/v1/cases/$case_id/artifacts" \
  > "$service_root/artifacts.json"
curl -sS "http://127.0.0.1:19870/clerk/v1/cases/$case_id/result" \
  > "$service_root/result.json"

test -f "$service_root/$case_id/verification.log"
test -f "$service_root/$case_id/adc-output/run.json"

python3 -c 'import json, sys
record = json.load(open(sys.argv[1]))
att = ((record.get("execution") or {}).get("attestation") or {})
if record.get("status") != "completed":
    raise SystemExit("case did not complete")
if record.get("exit_code") != 0:
    raise SystemExit("driver exit code was not zero")
if att.get("status") != "verified":
    raise SystemExit("attestation was not verified")
print(att.get("output_prefix", ""))
' "$service_root/record.json"
```

Stop the service after the run has reached a terminal state.  The service record remains on disk under `$service_root/$case_id`, and the attested artifacts remain in S3 under the recorded output prefix.  A later service process started with the same `--output-root` can load the saved record.

```bash
kill "$service_pid"
```

## Verification

A verified ADC run checks the manifest hash, the ADC archive hash, `run.log` hash, the attestation signature and certificate chain, Nitro TPM user data, and expected PCR values.  The expected PCR values in this runbook correspond to the current Docker-enabled exec AMI and must change when that AMI changes.  The local driver writes `verification.log`; the service requires that file and a readable extracted `adc-output/run.json` before marking the case completed.

Run these checks from the repository root when reviewing a downloaded run directory.  They verify the local materialization, the S3 object shape, and the attestation parser output without starting another exec instance.  Replace `LOCAL` with the case output directory used by the driver or service.

```bash
LOCAL=/tmp/adc-attested-service-REPLACE/adc-attested-ex1-REPLACE

test -f "$LOCAL/run.env"
test -f "$LOCAL/progress.log"
test -f "$LOCAL/launcher.log"
test -f "$LOCAL/run.log"
test -f "$LOCAL/manifest.json"
test -f "$LOCAL/manifest.sha384"
test -f "$LOCAL/attestation.b64"
test -f "$LOCAL/verification.log"
test -f "$LOCAL/adc-output.tar.gz"
test -f "$LOCAL/adc-output/run.json"
test -f "$LOCAL/adc-output/events.ndjson"

python3 -c 'import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
manifest = json.loads((root / "manifest.json").read_text())
required = [
    "run_id",
    "input_mode",
    "input_prefix",
    "output_prefix",
    "archive_key",
    "archive_sha384",
    "run_log_sha384",
    "case_packet_key",
    "case_packet_sha384",
    "case_manifest_key",
    "case_manifest_sha384",
]
missing = [name for name in required if not manifest.get(name)]
if missing:
    raise SystemExit("manifest missing fields: " + ", ".join(missing))
print(manifest["output_prefix"])
' "$LOCAL"
```

## Troubleshooting

Use the first concrete failing line as the diagnostic start.  The service record tells whether the Clerk layer failed before launch, the driver logs tell whether staging or `exec.sh` failed, S3 tells whether the exec container reached terminal artifact upload, and `verification.log` tells whether the record was cryptographically accepted.  Console output alone is not the attestation record; the S3 prefix and downloaded artifacts are the record.

| Symptom | Cause | Fix |
| --- | --- | --- |
| The readiness check cannot fetch `/clerk/v1/cases`. | The service did not start, the port is already occupied, or a configured executable path is stale. | Read `$service_root/service.log`, check `ss -ltnp` for `127.0.0.1:19870`, and rebuild the core `adc` and `adcengine` binaries and the service `adc-service` and `adc-run` binaries. |
| `attested execution requires input_prefix`, `exec_ami`, `expected_pcr4`, or `expected_pcr7` appears in the create response. | The service was started without a required `--attested-*` default, and the request did not provide the value. | Restart the service with the required defaults or provide those fields in `execution.attestation`. |
| The exec entrypoint reports that `auth.json`, `keys.sh`, or `OPENROUTER_API_KEY` is missing. | The selected S3 input prefix was fresh and contained only the case packet, or `keys.sh` did not assign or export the provider key. | Stage `/home/ec2-user/arbattest-secrets/auth.json` and `/home/ec2-user/arbattest-secrets/keys.sh` to the exact `--attested-input-prefix` before posting the create request, then confirm with `aws s3 ls`. |
| OpenClaw cannot read `/adc-codex/auth.json` or fails while importing the Codex token. | ADC could not stage a container-readable Codex home from the downloaded `auth.json`, or the auth file no longer contains a valid token. | Inspect the lawyer stderr log in the extracted ADC output and verify that the source `auth.json` on `dev` is current.  The staged Codex home should be mode `0777`, and `auth.json` should be mode `0666` in this private exec-image path. |
| OpenClaw imports Codex auth but later reports a Codex stream disconnect from the exec AMI. | The child OpenClaw container is using Docker bridge networking inside the exec-container topology. | Confirm that the attested image contains the current entrypoint and that `run.log` shows `--openclaw-network host`.  Rebuild and upload `adc-glue:poc` if the image predates that argument. |
| The run fails near one hour while `events.ndjson` still shows active ADC progress. | `attest/exec.sh` reached its console polling limit and terminated the exec instance before ADC produced terminal S3 artifacts. | Leave `--attested-exec-poll-attempts` unset so the driver derives it from `--attested-timeout-seconds`, or set it high enough for the expected legal run.  The current driver adds ten minutes of headroom over the ADC timeout. |
| The S3 output prefix has `events.ndjson` but no terminal artifacts. | ADC was still running, the exec instance was terminated, or the entrypoint failed before terminal upload. | Check `$LOCAL/progress.log`, `$LOCAL/launcher.log`, EC2 instance state from the launcher output, and any partial S3 objects.  If `adc-partial.tar.gz` exists, extract it and read the ADC logs before changing code or configuration. |
| The S3 output prefix contains thousands of ADC output objects. | The entrypoint recursively uploaded the run directory instead of one archive. | Rebuild and upload the current `adc-glue:poc`; the current path uploads one `adc-output.tar.gz` on success or one `adc-partial.tar.gz` on failure. |
| The service record reaches `failed` with driver exit code zero absent or nonzero. | The child driver failed, or it produced partial artifacts rather than a verified success archive. | Read `$service_root/$case_id/service-logs/adc.stdout`, `$service_root/$case_id/service-logs/adc.stderr`, `progress.log`, and `launcher.log`.  The driver error should name the failed command or missing terminal object. |
| Verification fails on `manifest.sha384`, archive hash, run-log hash, user data, or PCR values. | The downloaded files do not match the manifest, the attestation user data does not equal the manifest hash, or the exec AMI changed. | Treat the run as unverified.  Compare `manifest.json`, `manifest.sha384`, `attestation.txt`, and the expected PCR values recorded in this runbook before updating any expected values. |
| `/attestation/events` returns an HTTP error. | The case is not an attested record, the service cannot read the live S3 event object, or the driver has not yet uploaded events. | Inspect `GET /clerk/v1/cases/$case_id`, confirm `execution.attestation.output_prefix`, and check `$service_root/$case_id/progress.log` for the driver stage. |
| The service rejects `out_dir` as outside the output root. | The supplied path does not resolve to an immediate child of `--output-root`. | Omit `out_dir` in the create request for the standard path, or use an immediate child such as `$service_root/$case_id`. |
