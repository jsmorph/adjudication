# Agent District Court

Agent District Court (ADC) is an experimental civil-litigation runtime for AI legal agents.  The Go runtime manages intake, prompts, storage, role APIs, reports, and local agent processes.  The Lean engine enforces procedure and state transitions under the Agent Rules for Civil Procedure.

ADC starts from either a situation file, a complaint, or a scenario JSON file.  A situation file can be turned into a complaint with `adc complain`.  A complaint can be turned into a one-claim case packet and then run through pleadings, motions, discovery, trial, verdict, and judgment.

The current external-agent path uses a case-owned HTTP Role API and a Streamable HTTP MCP adapter.  OpenClaw lawyers connect through MCP.  Pi jurors connect through MCP when `adc run` starts a fresh juror agent for an active juror opportunity from a JSONL request-spec pool.  If a deliberating juror agent fails, ADC removes that juror from the effective concurrence count and derives any verdict from the eligible jurors who remain.

Jury size and verdict threshold are case-policy settings.  `adc case`, `adc scenario`, and `adc run` accept `--juror-count`, `--unanimous-required`, and `--minimum-concurring`; the Clerk create API accepts `juror_count`, `unanimous_required`, and `minimum_concurring`.  When those values are omitted, ADC uses the scenario policy or the default six-person unanimous jury.

## Documentation

The manual documents commands and HTTP APIs.  The attested runbook documents the Docker image, exec AMI, S3 artifact layout, and verification procedure.  A Clerk-managed attested run uses the manual's `adc service` section with the ADC Docker runbook and dev-host requirements.

| Document | Use |
| --- | --- |
| [Agent District Court Manual](manual.md) | Commands and operating details for `adc case`, `adc scenario`, `adc run`, `adc service`, Role API, MCP, Clerk routes, attested Clerk requests, `attestation/events`, output files, failure behavior, and troubleshooting. |
| [ADC Docker Image Runbook](../service/attested/adc/Dockerfile.md) | ADC base image, attested workload image, exec AMI launch path, S3 input and output prefixes, live `events.ndjson`, attestation artifacts, local driver commands, Clerk service sequence, verification, and troubleshooting. |
| [Attested ADC Dev Host Requirements](../service/attested/adc/attested-dev-host.md) | `dev` host layout, AWS region, AMI, instance profile, S3 permissions, secret files, Docker build requirements, expected PCR values, and operational checks. |
| [Attested ADC run helper](../service/attested/adc/run-one-attested-adc.sh) | One-complaint attested run helper that stages `auth.json` and `keys.sh`, selects run-specific S3 prefixes, and invokes the verified local driver. |
| [Agent District Court Practice Guide](docs/practice.md) | Pleadings, discovery, evidence search, evidence analysis, trial work, jury instructions, closings, and deliberation. |
| [Agent Rules for Civil Procedure](docs/ARCP.md) | Governing ADC procedure. |

## Requirements

| Requirement | Purpose |
| --- | --- |
| Go `1.25` | Builds the ADC runtime. |
| Lean `4.32.0` and `lake` | Builds the Lean engine and proof tree. |
| `make` | Runs build, test, proof, and example targets. |
| Docker | Runs OpenClaw lawyer containers in `adc run`. |
| Podman | Runs Pi juror containers in `adc run`. |
| `OPENROUTER_API_KEY` | Required for Pi jurors selected from a request-spec pool. |
| Codex `auth.json` or `OPENAI_API_KEY` | Required for OpenClaw lawyers.  Codex auth supports subscription-backed OpenClaw runs. |
| Attested ADC `dev` host | See [Attested ADC Dev Host Requirements](../service/attested/adc/attested-dev-host.md) for the remote Docker, S3, IAM, secret, and verification requirements. |

## Build

Build both local binaries from `adc/`:

```bash
make build
```

That writes `.bin/adc` and `.bin/adcengine`.  Run the Go tests with:

```bash
make test
```

Build the Lean proof tree with:

```bash
make prove
```

## Basic Runs

Draft a complaint from example 1:

```bash
.bin/adc complain \
  --situation examples/ex1/situation.md \
  --out examples/ex1/complaint.md
```

Run the complaint with direct internal roles:

```bash
.bin/adc case \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-direct
```

Run the complaint with local OpenClaw lawyers and Pi jurors:

```bash
export OPENROUTER_API_KEY=REPLACE_WITH_KEY
.bin/adc run \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-openclaw-pi \
  --openclaw-auth codex \
  --openclaw-codex-auth PATH/TO/auth.json
```

Run the Clerk service:

```bash
.bin/adc service \
  --listen 127.0.0.1:19870 \
  --output-root out/adc-service \
  --adc-bin .bin/adc \
  --engine .bin/adcengine
```

Create a local-agent case through the Clerk service:

```bash
curl -sS -X POST http://127.0.0.1:19870/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "mode": "run",
    "case_id": "adc-ex1",
    "complaint_path": "examples/ex1/complaint.md",
    "out_dir": "out/adc-service/adc-ex1",
    "openclaw_auth": "codex",
    "openclaw_codex_auth_path": "PATH/TO/auth.json",
    "juror_personas": "../common/data/personas/pool.jsonl"
  }'
```

## Repository Layout

| Path | Purpose |
| --- | --- |
| `engine/` | Lean rule engine, proofs, and Lake project. |
| `runtime/` | Go CLI, runtime, Role API, MCP adapter, local run code, and Clerk service. |
| `agent-instructions/` | Templates passed to OpenClaw lawyers and Pi jurors. |
| `etc/` | Court profile files. |
| `examples/` | Example case source documents. |
| `docs/` | Rules, practice guide, reference notes, proof notes, and procedure analysis. |
| `analysis/` | Mermaid diagrams and explanatory notes. |
| [Agent District Court Manual](manual.md) | Commands, APIs, outputs, and troubleshooting. |

## Output

Run output contains `run.json`, `state.json`, `certificate.json`, `runtime.json`, `events.ndjson`, `run.db`, `transcript.md`, `digest.md`, and `work-notes.ndjson`.  Complaint-driven runs also write `normalized-case.json`, `plaintiff-strategy.md`, `defense-strategy.md`, and `generated-scenario.json`.  `adc run` adds process logs and local-agent metadata under the selected output directory.

## License

The software is released under the repository-level MIT License in [../LICENSE](../LICENSE).  Trademark and related notice terms are in [../NOTICES.md](../NOTICES.md).
