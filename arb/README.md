# Agent Arbitration

Agent Arbitration (AAR) decides one proposition through an adversarial record and a council vote.  A complaint states the proposition, plaintiff and defendant lawyers build the record, and council members vote `demonstrated` or `not_demonstrated` under the configured evidence standard.  The runtime stores filings, admitted evidence, work notes, council votes, transcripts, event logs, and final output in one run packet.

## Documentation

The manual documents commands and HTTP APIs.  The attested runbook documents the Docker image, exec AMI, S3 artifact layout, and verification procedure.  A Clerk-managed attested run uses the manual's `aar service` and Clerk API sections with the attested Docker runbook and dev-host requirements.

| Document | Use |
| --- | --- |
| [Agent Arbitration Manual](manual.md) | Commands and operating details for `aar case`, `aar run`, `aar council-replay`, `aar juror-replay`, `aar service`, `aar mcp`, Lawyer and Council APIs, Clerk routes, attested Clerk requests, `attestation/events`, output files, failure behavior, and troubleshooting. |
| [AAR Docker Image Runbook](Dockerfile.md) | AAR base image, attested workload image, exec AMI launch path, S3 input and output prefixes, `events.ndjson`, attestation artifacts, local driver commands, and verification. |
| [Attested AAR Dev Host Requirements](docs/attested-dev-host.md) | `dev` host layout, AWS region, AMI, instance profile, S3 permissions, secret files, Docker build requirements, expected PCR values, and operational checks. |
| [Council and Juror Replay Guide](docs/council-replay.md) | Same-spec council replay, experimental juror replay, snapshot selection, model config creation, replay output files, and troubleshooting. |
| [Agent Arbitration Practice Guide](docs/practice.md) | Lawyer and council practice: phase work, evidence search, source preservation, technical reports, work notes, and council deliberation. |
| [Agent Rules for Arbitration Procedure](docs/ARAP.md) | Governing AAR procedure. |

## Requirements

| Requirement | Purpose |
| --- | --- |
| Go `1.25` | Builds the AAR runtime. |
| Lean `4.32.0` and `lake` | Builds the Lean engine and proof tree. |
| Docker | Runs OpenClaw lawyer containers in `aar run`. |
| Podman | Runs Pi council containers in `aar run`. |
| Codex `auth.json` or `OPENAI_API_KEY` | Authenticates OpenClaw lawyers. |
| `OPENROUTER_API_KEY` | Authenticates current local Pi council pool entries that use OpenRouter. |
| Attested AAR `dev` host | See [Attested AAR Dev Host Requirements](docs/attested-dev-host.md) for the remote Docker, S3, IAM, secret, and verification requirements. |

## Build

Build from `arb/`:

```bash
make build
make test
make prove
```

`make build` writes `.bin/aar` and `.bin/aarengine`.  `make test` runs the Go tests for the runtime.  `make prove` builds the Lean proof tree.

## First Run

Run an example with OpenClaw lawyers using Codex auth and Pi council agents sampled from `pool.jsonl`:

```bash
export OPENROUTER_API_KEY=REPLACE_WITH_KEY

.bin/aar run \
  --openclaw-auth codex \
  --openclaw-codex-auth PATH/TO/auth.json \
  --council-pool "$(pwd)/pool.jsonl" \
  ex01
```

Start the Clerk service when cases should be created and managed through HTTP:

```bash
.bin/aar service \
  --listen 127.0.0.1:19770 \
  --out-root out/service \
  --aar-bin .bin/aar
```

## Juror Replay

`aar juror-replay` runs one fresh Pi council-member deliberation from an existing AAR output packet with a selected model config and persona.  Use it from `arb/` after building `.bin/aar`; it requires `OPENROUTER_API_KEY`, a runnable Pi image, and access to the configured container command.  The [Agent Arbitration Manual](manual.md#aar-juror-replay) gives the full command, model-config creation steps, output files, and troubleshooting notes.

```bash
source="out/local-direct-three-per-ex-only-20260629/ex13/run-03"
member=C1

jq --arg member "$member" '
  .[] | select(.member_id == $member) | .request_spec
' "$source/council.json" >"/tmp/aar-juror-replay-$member-model.json"

.bin/aar juror-replay \
  --source-output "$source" \
  --member-id "$member" \
  --model-config "/tmp/aar-juror-replay-$member-model.json" \
  --persona "../evals/model-pool/personas/experiments/attorneys/Brandeis.txt" \
  --out-dir "out/juror-replays/ex13-run-03-$member-brandeis" \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest
```

## Layout

| Path | Purpose |
| --- | --- |
| [Agent Arbitration Manual](manual.md) | Commands, APIs, outputs, and troubleshooting. |
| [AAR Docker Image Runbook](Dockerfile.md) | Attested Docker image and exec runbook. |
| `docs/` | Rules, practice guide, API/process specs, evidence handling, policy notes, and proof references. |
| `engine/` | Lean arbitration engine and proofs. |
| `runtime/` | Go CLI, case runtime, HTTP APIs, MCP adapter, local run code, and service. |
| `agent-instructions/` | Templates for OpenClaw lawyers, remote OpenClaw lawyers, and Pi council agents. |
| `examples/` | Example complaints and case packets. |
| `prompts/` | Prompt templates used by the case runtime. |
| `pool.jsonl` | Local council request-spec pool when present. |

## Output

Run output contains `run.json`, `state.json`, `transcript.md`, `digest.md`, `events.ndjson`, `work-notes.ndjson`, `evidence-manifest.json`, `evidence-store/`, process logs, and local-run metadata.  Council turn snapshots live under `council-turns/` when the run records replayable deliberation inputs.  Attested runs add launcher logs, progress logs, manifests, attestation files, verification logs, and output archives described in the [AAR Docker Image Runbook](Dockerfile.md).

## License

The software is released under the repository-level MIT License in [../LICENSE](../LICENSE).  Trademark and related notice terms are in [../NOTICES.md](../NOTICES.md).
