# Agent-driven adjudication

This repo provides agent-driven adjudication that uses agents in legal procedures controlled by explicit rules.  In these systems, lawyers, jurors, judges (if applicable) and council members operate together to perform an adjudication in some form.  A rigorous engine, implemented in Lean, controls phases, opportunities, accepted actions, and final outcomes.  Each run produces a record that can be evaluated and, in some modes, verified via an attestation.

## Approach

Each system separates procedure from advocacy and fact evaluation.  The procedural engine (Lean) controls the current phase, required opportunities, accepted actions, and ending conditions.  The (Go) runtime exposes the engine through commands, HTTP APIs, MCP adapters, services, and artifacts.  Lawyers, jurors, and council members create filings, votes, and answers that the engine accepts or rejects.

The systems use different procedures for different goals.  [Agent District Court](adc/README.md) models civil litigation with pleadings, motions, discovery, voir dire, trial, jury deliberation, verdict, and judgment.  [Arbitration](arb/README.md) models binary arbitration over whether a proposition has been demonstrated.  [Arbitration of Degree](arbd/README.md) models degree arbitration over a numerical answer.

## Core Capabilities

| Capability | Description |
| --- | --- |
| Lean engines | The three systems use separate Lean engines for phases, opportunities, accepted actions, and final states. |
| Engine proofs | The proof work checks engine behavior and certificate replay.  Lawyer search quality and juror reasoning are judged from records and evals, not Lean proofs. |
| Run records | Completed runs write state, event, transcript, and certificate artifacts for later inspection and replay verification. |
| Pool sampling | Model-pool evals compare candidate model endpoints, group behavior, and sample juror or council panels for live runs. |
| External lawyers | Lawyer agents can participate through assigned role APIs and MCP adapters. |
| OpenClaw support | A run can start OpenClaw lawyers for one or both sides as one way to run lawyer agents.  For example, `adc run --auto-lawyers defendant` starts the defendant lawyer locally and writes plaintiff instructions for an independently running OpenClaw session. |
| Evals | Evals cover model pools, juror and council behavior, and Agent District Court judge decisions.  The judge evals include voir dire question rulings and test candidate prompts before use in live Agent District Court runs. |
| Attested execution | Attested runs package case inputs, run the procedure on an attested host, and link uploaded artifacts to attestation records and manifest hashes. |
| Service operation | Long-lived services can create, track, inspect, and stop case runs through service APIs. |

## Example Usage

Run a direct [Arbitration](arb/README.md) case to start the core procedure from the command line.  The command exposes case-owned Lawyer and Council HTTP APIs and waits for external lawyer clients.  Its default direct council backend samples `pool.jsonl` and calls the selected council models after the lawyers finish.

```bash
cd arb
make build

mkdir -p work/example-arbitration
cat > work/example-arbitration/complaint.md <<'EOF'
# Proposition

During May 2026 (ET), Iran initiated a major non-weather closure of its airspace.
EOF

export OPENROUTER_API_KEY=REPLACE_WITH_OPENROUTER_KEY

.bin/aar case \
  --complaint work/example-arbitration/complaint.md \
  --council-pool "$(pwd)/pool.jsonl" \
  --out-dir out/example-arbitration
```

The command writes its listener address to stderr after checking the council pool.  Plaintiff and defendant clients use that address to read opportunities and submit filings through the Lawyer API.  The completed case writes the transcript, event log, state, certificate, and summary files under its output directory.

## Systems

| Path | Command | Manual | Purpose |
| --- | --- | --- | --- |
| [adc/](adc/README.md) | `adc` | [Agent District Court Manual](adc/manual.md) | Civil litigation procedure with pleadings, motions, discovery, trial, jury deliberation, verdict, and judgment. |
| [arb/](arb/README.md) | `aar` | [Agent Arbitration Manual](arb/manual.md) | Arbitration over one proposition, with plaintiff and defendant lawyers and a council vote on demonstrated or not demonstrated. |
| [arbd/](arbd/README.md) | `aard` | [Agent Arbitration Degree Manual](arbd/manual.md) | Degree arbitration over one question, with plaintiff and defendant lawyers and council answers from `0` through `100`. |
| [evals/model-pool/](evals/model-pool/README.md) | `cd evals/model-pool && uv run tools/COMMAND.py` | [Model-Pool Evals Manual](evals/model-pool/manual.md) | Core and deliberation eval sets, model endpoint inventory, scoring, grouping, and pool sampling tools. |

The manuals document commands, services, HTTP APIs, MCP adapters, attested execution, outputs, and troubleshooting.  The practice guides describe how lawyers, jurors, and council members examine evidence, create the record, and deliberate within each procedure.

## Shared Directories

| Path | Purpose |
| --- | --- |
| `common/` | Shared Go packages, model-request types, persona data, Pi container support, and common tools. |
| [docs/](docs/README.md) | Cross-system proof and repository notes. |
| [scratch/](scratch/README.md) | Archived notes, old drafts, run observations, and investigation records. |
| `skills/` | Local analysis notes for proof review. |
| [web/](web/README.md) | Service console, run report, and ARB management web servers. |

## Requirements

| Requirement | Purpose |
| --- | --- |
| Go `1.25` | Builds the Go runtimes. |
| Lean `4.27.0` and `lake` | Build the Lean engines and proof trees. |
| `make` | Runs build, test, proof, and example targets in each system directory. |
| Docker | Runs the included OpenClaw lawyer containers and builds attested workload images. |
| Podman | Runs Pi juror and council containers for local-agent runs. |
| Model-provider credentials | The included OpenClaw support uses Codex `auth.json` or `OPENAI_API_KEY`.  Current Pi pools use OpenRouter through `OPENROUTER_API_KEY`. |

## Build

Build one or more systems from the repository root:

```bash
make -C adc build test prove
make -C arb build test prove
make -C arbd build test prove
```

The repository root has no top-level `Makefile`.  Shared packages build through the system commands because the runtimes use the same Go module.  Build the Pi container image from `common/pi-container/` when a local-agent run needs the local Pi image.

## Documentation

| Area | Primary documents |
| --- | --- |
| Agent District Court | [README](adc/README.md), [manual](adc/manual.md), [practice guide](adc/docs/practice.md), [rules](adc/docs/ARCP.md), [attested runbook](adc/Dockerfile.md), [dev-host requirements](adc/docs/attested-dev-host.md). |
| Arbitration | [README](arb/README.md), [manual](arb/manual.md), [practice guide](arb/docs/practice.md), and [rules](arb/docs/ARAP.md). |
| Arbitration of Degree | [README](arbd/README.md), [manual](arbd/manual.md), [practice guide](arbd/docs/practice.md), and [rules](arbd/docs/ARAP.md). |
| Evals | [README](evals/README.md), [model-pool manual](evals/model-pool/manual.md), [sampling runbook](evals/model-pool/docs/sampling-runbook.md), [model inventory notes](evals/model-pool/docs/model-inventory.md), [judge eval plan](evals/adc/judge/plan.md). |
| Proofs | [Proof work status](docs/proof-notes.md). |
| Web | [Web servers overview](web/README.md), [web runbook](web/runbook.md). |
| Shared model pools | [Jury and council pool generation](evals/model-pool/docs/jury-pool-generation.md). |

## License

The software is released under the MIT License in [LICENSE](LICENSE).  Trademark and related notice terms are in [NOTICES.md](NOTICES.md).
