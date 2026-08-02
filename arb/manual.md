# Agent Arbitration Manual

## Overview

Agent Arbitration, or AAR, runs a dispute about one proposition.  A complaint states the proposition, two lawyers build and argue the record, and a council decides whether the proposition has been demonstrated under the configured evidence standard.  The runtime keeps the case record, enforces turn order and limits, stores admitted evidence, records private lawyer work notes outside the record, and writes a final packet that can be inspected after the case ends.

AAR supports several operating modes.  `aar case` runs one case and exposes HTTP APIs for lawyers, observers, and optional council members.  `aar run` starts a complete local arbitration with OpenClaw lawyer containers, a local MCP server, and Pi council agents.  `aar service` runs a long-lived HTTP service that can start and track many `aar run` cases through the Clerk API.  `aar mcp` exposes the case and role APIs through MCP for lawyers, observers, and council members that use MCP instead of direct HTTP.

The normal end-to-end path is `aar run`.  It starts the case process in Go, starts the AAR MCP server, starts OpenClaw lawyers unless a role is assigned to a remote OpenClaw, starts Pi council agents when deliberation begins, and writes final output under one run directory.  The service path uses the same `aar run` command as a child process; the Clerk API gives an operator HTTP endpoints to create, list, and kill those full runs.

All commands in this document assume the working directory is `arb/` unless a command says otherwise.

## Operating Model

A case process owns the arbitration.  It owns the current phase, turn order, deadlines, attempt budgets, evidence registry, work-note log, council roster, and final output packet.  Lawyers, observers, and council members are clients of that process.  They read the case and act through HTTP or MCP tools; they do not need filesystem mounts or private access to the case output directory.

`aar run` is the complete one-case command.  It embeds the case process in the same Go process, starts an MCP server for the case, starts local OpenClaw lawyer containers according to `--auto-lawyers`, and starts Pi council agents when deliberation begins.  Its MCP server is part of the run and exits when the run ends.

`aar service` is the long-lived process.  Its Clerk API starts full `aar run` child processes and tracks them through `clerk.json` files in their output directories.  Its direct case API starts `aar case` child processes for direct HTTP testing and role-proxy use.  The service keeps two registries: Clerk cases are managed through `/clerk/v1`, while direct cases are managed through `/api/v1` and the service role proxies.

## Choosing A Command

| Goal | Command |
| --- | --- |
| Run one complete local case with OpenClaw lawyers and Pi council agents. | `aar run EXAMPLE` or `aar run --complaint FILE`. |
| Build a deterministic case packet for attested complaint input. | `aar case-packet --complaint FILE --packet case.tar.gz --manifest case-packet.json`. |
| Run one complete case where one lawyer is an independently running OpenClaw. | `aar run --auto-lawyers defendant` for a remote plaintiff, or `aar run --auto-lawyers plaintiff` for a remote defendant. |
| Start and track many full runs from an HTTP service. | `aar service`, then `POST /clerk/v1/cases`. |
| Drive lawyers or council members by direct HTTP instead of local agents. | `aar case`, or `aar service` with `POST /api/v1/cases`. |
| Give an MCP client access to an existing case or service role API. | `aar mcp --caseapi-base URL`. |
| Normalize or check a complaint file. | `aar complain` and `aar validate`. |
| Replay-check a completed packet against its final state. | `aar verify-certificate --dir DIR`. |

## Core Concepts

An AAR case begins with a complaint.  The complaint contains one proposition, usually written under a `# Proposition` heading.  The plaintiff lawyer tries to demonstrate that proposition, and the defendant lawyer tests the proof, identifies gaps, develops contrary evidence when available, and argues that the proposition has not been demonstrated.

The record contains lawyer filings, admitted evidence, technical reports, and council votes.  Initial case files enter the record when the case starts.  Lawyers may also submit evidence during arguments, rebuttals, and surrebuttals.  Openings and closings may read evidence but may not submit new evidence.

The case proceeds through lawyer phases and then deliberation.  The lawyer phases are openings, arguments, rebuttals, surrebuttals, and closings.  The final council phase asks council members to vote `demonstrated` or `not_demonstrated` and explain their vote.  A configured vote threshold determines the final resolution.

The runtime distinguishes record evidence from work notes.  Evidence is part of the case record and may be cited by `evidence_id`.  Work notes are private operator-facing notes sent by lawyers through `send_work_notes`; they are stored in `work-notes.ndjson` and are not evidence, filings, or case events.

## Operator Guidance

Use AAR when the proceeding should decide whether one proposition has been demonstrated under an evidence standard.  Keep the proposition narrow enough that lawyers can search for evidence, test provenance, and argue the record within the configured filing limits.  Use AARD when the desired output is a numeric answer or supported degree; AAR reduces the merits question to `demonstrated` or `not_demonstrated`.

Treat the output directory as the case record for one run.  Preserve `run.json`, `state.json`, `certificate.json`, `transcript.md`, `digest.md`, `events.ndjson`, `work-notes.ndjson`, `evidence-manifest.json`, `evidence-store/`, and `council-turns/` together.  Use `events.ndjson` to reconstruct process sequence, `transcript.md` to read the record, `digest.md` to check the outcome, `certificate.json` to replay-check the accepted state transitions, and `work-notes.ndjson` to review lawyer planning that stayed outside the evidentiary record.

## Repository Layout

| Path | Meaning |
| --- | --- |
| `runtime/cmd/aar/` | Go command-line package for `aar`. |
| `runtime/proceeding/` | Case runner, Lawyer API, Council API, evidence storage, rendering, and policy logic. |
| `runtime/mcp/` | MCP server that forwards tool calls to the Lawyer and Council APIs. |
| `runtime/localrun/` | `aar run`: local orchestration for OpenClaw lawyers, MCP, and Pi council agents. |
| `runtime/service/` | `aar service`: long-running HTTP service, role API proxy, and Clerk API. |
| `engine/` | Lean arbitration engine used by the Go runtime. |
| `prompts/` | Lawyer prompt files used by the case runner. |
| `agent-instructions/` | Templates given to OpenClaw lawyers and Pi council agents by `aar run`. |
| `examples/` | Example cases.  Each example has a `complaint.md` and may have supporting case files. |
| `pool.jsonl` | Local council pool used by `aar run` when present. |
| `personas/` | Persona files referenced by the council pool. |

## Build And Environment

Build from `arb/`.  `make build` builds the Lean engine and the Go CLI into `.bin/`.  A direct Go build is useful when only the Go command changed, but a complete local run also needs the engine binary.

```bash
make build
```

The direct Go build is:

```bash
go build -o .bin/aar ./runtime/cmd/aar
```

The full test command for the Go runtime is:

```bash
go test -count=1 ./runtime/...
```

`aar run` uses Docker for OpenClaw lawyer containers and Podman for Pi council agents.  The default OpenClaw image is `ghcr.io/openclaw/openclaw:latest`.  The default Pi image is `agentcourt-pi-sandbox`, unless `PI_CONTAINER_IMAGE` is set and `--pi-image` is omitted.  The default Pi MCP adapter path is `/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter`, which the shared Pi image builds from pinned `pi-mcp-adapter@2.11.0`.

Pi council agents require `OPENROUTER_API_KEY`.  `aar run` validates that the variable exists before starting.  Council model, provider, quantization, and persona come from the selected entries in `pool.jsonl`; AAR passes those request-spec entries to Pi without deriving a separate model string.

OpenClaw lawyers can use a Codex auth file or `OPENAI_API_KEY`.  The usual local path is Codex auth: `--openclaw-auth codex --openclaw-codex-auth PATH`.  If `--openclaw-auth auto` is used, AAR first looks for a readable Codex auth file and then falls back to `OPENAI_API_KEY`.  The default Codex auth path is `$CODEX_HOME/auth.json` when `CODEX_HOME` is set, otherwise `$HOME/.codex/auth.json`.

An environment file used by examples should export `OPENROUTER_API_KEY`.  It may also export `OPENAI_API_KEY` if OpenClaw lawyers will use API-key mode.  Codex auth mode reads `auth.json` from the path supplied by `--openclaw-codex-auth`.

```bash
export OPENROUTER_API_KEY=REPLACE_WITH_KEY
```

The council pool is a JSONL file with request-spec records.  A local `pool.jsonl` in `arb/` takes precedence when `--council-pool` is omitted.  If `--council-pool` or Clerk `council_pool_path` is set, use an absolute path unless the intended pool lives under the shared common root.  Persona paths in pool records are resolved from the pool base directory.  The sampled council roster is written into the run packet so the final output records which members, provider settings, quantization, and personas were used.

## Complaint Files

A complaint is markdown.  If it contains a heading named `Proposition`, AAR uses that section as the proposition.  If no such heading exists, AAR treats the whole trimmed file as the proposition.

```markdown
# Proposition

The defendant sent the signed confession attached to the case packet.
```

Use `aar validate` before running a case if the complaint was written or transformed by another tool:

```bash
.bin/aar validate --complaint examples/ex01/complaint.md
```

On success, `aar validate` prints `ok`.

Use `aar complain` to normalize a situation file into canonical complaint form.  The command parses the input the same way as a complaint and writes a `# Proposition` complaint file.

```bash
.bin/aar complain \
  --situation work/my-case/situation.md \
  --out work/my-case/complaint.md
```

On success, `aar complain` prints the output path.

## Initial Evidence

When `aar case` or `aar run` starts without `--file`, the case runner scans the complaint directory for initial case files.  It skips the complaint file, a situation file, `README.md`, editor backup files ending in `~`, signing evidence, and directories.  Text-like files such as `.txt`, `.md`, `.pem`, and `.b64` are loaded as readable text evidence; other file types are stored as byte-bearing evidence.

Use `--file` to provide explicit initial evidence.  The flag may be repeated.  Supplying any `--file` value replaces automatic complaint-directory scanning, so list every initial evidence file that belongs in the starting packet.

```bash
.bin/aar case \
  --complaint work/my-case/complaint.md \
  --file work/my-case/source-a.pdf \
  --file 'work/my-case/captures/*.png' \
  --out-dir out/my-case
```

`aar case-packet` packages the same complaint and initial evidence selection into the attested-run input format.  It writes a deterministic `case.tar.gz` and a `case-packet.json` manifest, using the proceeding package's automatic scan and explicit-file validation.  The attested local driver calls this command before uploading packet objects to S3, so local and attested Clerk complaint input share one case-file implementation.

## Commands

| Command | Purpose |
| --- | --- |
| `aar complain` | Write a canonical complaint from a situation markdown file. |
| `aar validate` | Validate that a complaint parses. |
| `aar case-packet` | Build `case.tar.gz` and `case-packet.json` for attested complaint input. |
| `aar case` | Run one case and expose the private Lawyer and optional Council APIs. |
| `aar mcp` | Run an MCP server that forwards tools to a Case API or service API base. |
| `aar run` | Run one complete local arbitration with OpenClaw lawyers and Pi council agents. |
| `aar council-replay` | Re-run one council member against a saved AAR output packet. |
| `aar juror-replay` | Run one fresh juror deliberation from a saved AAR output packet with an explicit model config and persona. |
| `aar verify-certificate` | Replay-check `certificate.json` against `state.json` using the Lean engine. |
| `aar service` | Run the long-lived HTTP service, including Clerk APIs for full `aar run` cases. |

Use command help to see current flags:

```bash
.bin/aar help run
.bin/aar help council-replay
.bin/aar help juror-replay
.bin/aar help verify-certificate
.bin/aar help service
```

## `aar case`

`aar case` runs one case and waits for lawyers and, when configured, council members to act through HTTP APIs.  It writes the private case API base URL to stderr in the form `caseapi listening on http://127.0.0.1:PORT`.  It writes one JSON summary to stdout after the case ends.  That summary reports success, result, vote counts, run id, output directory, or a failure message.

Basic command:

```bash
.bin/aar case \
  --complaint examples/ex01/complaint.md \
  --out-dir out/ex01-direct
```

Important flags:

| Flag | Meaning |
| --- | --- |
| `--complaint` | Complaint markdown file.  Required. |
| `--out-dir` | Output directory for the run packet.  Required. |
| `--file` | Initial evidence file or glob.  May repeat. |
| `--policy` | Policy JSON file.  Defaults to `./etc/policy.json` when present. |
| `--council-size` | Override `policy.council_size`. |
| `--evidence-standard` | Override `policy.evidence_standard`. |
| `--attorney-instructions` | Standing lawyer instructions file. |
| `--prompt-dir` | Prompt directory override. |
| `--attorney-common-prompt` | Attorney common prompt file override. |
| `--attorney-arguments-prompt` | Attorney arguments prompt file override. |
| `--attorney-rebuttals-prompt` | Attorney rebuttals prompt file override. |
| `--common-root` | Shared `common/` tree for council pool and personas. |
| `--council-pool` | Council JSONL request-spec pool.  Use an absolute path unless the pool lives under the common root. |
| `--caseapi-addr` | Private Case API listen address.  Default: `127.0.0.1:0`. |
| `--council-backend` | `direct` or `councilapi`. |
| `--timeout-seconds` | Council LLM timeout override for direct council. |
| `--lawyer-timeout-seconds` | Lawyer turn timeout override. |
| `--max-response-bytes` | Parsed response byte limit override. |
| `--invalid-attempt-limit` | Invalid tool-call attempt limit override. |
| `--engine` | Lean engine binary. |
| `--run-id` | Run id override. |
| `--case-id` | Case id override.  Default: `arb-1` for direct `aar case`. |

The default council backend is `direct`.  In direct mode, the case runner samples council members and calls their configured model endpoints.  In `councilapi` mode, the case runner exposes `/councilapi/v1` and waits for external council agents to connect, read the record, and submit votes.

The private Case API has a health endpoint at `/health`.  It returns HTTP `204` after the case process has bound the listener.  `aar run` and `aar service` use that endpoint while waiting for child case startup.

## Lawyer API

The Lawyer API is available at `/lawyerapi/v1` on a private `aar case` listener and through the public service proxy.  Lawyer roles are `plaintiff` and `defendant`; the `observer` role is read-only.  Every request includes `case_id`, and lawyer requests include `role_id`.

Use `GET /lawyerapi/v1/get` to read the current status.  If a turn is ready, the response includes a prompt, a `turn` object, available tool specs, limits, remaining time, attempts left, and an `opportunity_id`.  Use `GET /lawyerapi/v1/wait` to wait up to the requested timeout for a ready turn or state change.  Use `GET /lawyerapi/v1/status` for role status and `GET /lawyerapi/v1/result` for final result information.

Tool calls use `POST /lawyerapi/v1/do`.  Lawyer tool calls must include the current `opportunity_id` unless the tool is `case_status`.  A successful final filing consumes the opportunity and advances the case.  Tool-specific validation failures can count against the turn's invalid-attempt limit; identity errors, missing opportunity ids, and wrong-turn calls return errors without consuming a turn attempt.

Example read:

```bash
BASE=http://127.0.0.1:21345/lawyerapi/v1

curl -sS "$BASE/wait?case_id=arb-1&role_id=plaintiff&timeout_ms=30000"
```

Example work notes:

```bash
curl -sS -X POST "$BASE/do" \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "arb-1",
    "role_id": "plaintiff",
    "opportunity_id": "arguments:plaintiff",
    "tool": "send_work_notes",
    "arguments": {
      "notes": "Plan: verify the signature file, compare it to the confession, then submit any missing provenance before filing."
    }
  }'
```

Example final filing:

```bash
curl -sS -X POST "$BASE/do" \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "arb-1",
    "role_id": "plaintiff",
    "opportunity_id": "openings:plaintiff",
    "tool": "submit_decision",
    "arguments": {
      "kind": "tool",
      "tool_name": "record_opening_statement",
      "payload": {
        "text": "The record will show that the defendant sent the signed confession.",
        "offered_evidence": [],
        "technical_reports": []
      }
    }
  }'
```

Lawyer tools include `case_status`, `get_case`, `send_work_notes`, `list_evidence`, `stat_evidence`, `read_evidence_range`, `submit_evidence`, `begin_evidence_upload`, `write_evidence_chunk`, `commit_evidence_upload`, and `submit_decision`.  Evidence submission and upload tools are available during arguments, rebuttals, and surrebuttals.  The legal filing actions passed through `submit_decision` are `record_opening_statement`, `submit_argument`, `submit_rebuttal`, `submit_surrebuttal`, `deliver_closing_statement`, and `pass_phase_opportunity` when that pass action is allowed.

Observer tools include `case_status`, `get_case`, `get_turn`, `list_events`, `list_evidence`, `stat_evidence`, and `read_evidence_range`.  These tools are read-only.  `get_turn` reports the current role, phase, deadline, and remaining attempts when a lawyer turn is active.

## Council API

The Council API is available when a case starts with `--council-backend councilapi`.  Calls go to `/councilapi/v1` and include `case_id` and `member_id`.  A council member uses `GET /councilapi/v1/wait` or `GET /councilapi/v1/get` to receive its deliberation opportunity, reads the record through evidence tools, and submits one vote through `POST /councilapi/v1/do`.

Council tools include `get_case`, `list_evidence`, `stat_evidence`, `read_evidence_range`, and `submit_council_vote`.  A council vote payload has `vote` and `rationale`.  The vote must be `demonstrated` or `not_demonstrated`, and the rationale should explain the vote from the admitted record.  After `submit_council_vote` succeeds, that council member is finished and should stop; it should not wait for later council opportunities assigned to other members.

The `POST /councilapi/v1/fail` endpoint lets a supervising process report council-member failure for an active opportunity.  `aar run` uses this endpoint when a Pi council process exits before completing its opportunity or exceeds the configured output byte limit.  A council member failure dismisses that member and the case continues under the council rules.

## MCP

`aar mcp` exposes AAR role APIs as MCP tools.  It needs one Case API or service API base URL.  MCP sessions are bound by query parameters, not by separate processes.  A lawyer session uses `/mcp?case_id=CASE_ID&role_id=plaintiff`, `/mcp?case_id=CASE_ID&role_id=defendant`, or `/mcp?case_id=CASE_ID&role_id=observer`.  A council session uses `/mcp?case_id=CASE_ID&member_id=C1`.

Start a standalone MCP server:

```bash
.bin/aar mcp \
  --caseapi-base http://127.0.0.1:21345 \
  --listen 127.0.0.1:19780
```

`aar mcp` prints `aar mcp listening on http://HOST:PORT/mcp` to stderr after binding the listener.  It also serves `/health`, which returns HTTP `204` when the MCP server is accepting requests.

Important flags:

| Flag | Meaning |
| --- | --- |
| `--caseapi-base` | Base URL for the Case API or service API.  Required. |
| `--listen` | MCP listen address.  Default: `127.0.0.1:19780`. |
| `--bearer-token` | Optional bearer token required for MCP requests. |
| `--api-bearer-token` | Optional bearer token sent from MCP to the Case API or service. |
| `--session-ttl` | Idle session lifetime.  `0` disables expiry. |
| `--session-cleanup-interval` | Interval for deleting expired sessions. |
| `--allow-origin` | Allowed browser Origin.  May repeat. |

An MCP client creates a session by sending the JSON-RPC `initialize` request to `/mcp` with the case and role query parameters.  The server returns an `Mcp-Session-Id` response header.  Subsequent MCP JSON-RPC requests for that session must include that header, and `DELETE /mcp` with the same header deletes the session.  A client that loses its session can initialize a new one with the same case and role query parameters.

The MCP tool set is stable during a session.  Tools that are not allowed for the current opportunity return an AAR error rather than changing the MCP tool list.  All MCP sessions expose `wait_for_opportunity` and `get_current_opportunity`.  Lawyer and observer sessions also expose role tools; council sessions expose council tools.

| Session | MCP tools |
| --- | --- |
| Plaintiff or defendant lawyer | `wait_for_opportunity`, `get_current_opportunity`, `case_status`, `get_case`, `get_case_result`, `send_work_notes`, evidence readers, evidence submission and upload tools, and `submit_decision`. |
| Observer | `wait_for_opportunity`, `get_current_opportunity`, `case_status`, `get_case`, `get_case_result`, `get_turn`, `list_events`, and evidence readers. |
| Council member | `wait_for_opportunity`, `get_current_opportunity`, `get_case`, evidence readers, and `submit_council_vote`. |

The first MCP tool call should be `wait_for_opportunity`.  If it returns `state: waiting`, call it again with `after_version`; if it returns `state: ready`, complete that opportunity; if it returns `done`, `failed`, or `error`, stop.  A council member should stop after an accepted `submit_council_vote` call.  MCP adds the active `opportunity_id` to forwarded mutating calls, so the client usually needs to copy the opportunity id only when using the HTTP APIs directly.

## `aar run`

`aar run` runs one full arbitration.  It starts the case runner, starts the local MCP server, starts OpenClaw lawyers according to `--auto-lawyers`, starts Pi council members when they are ready to deliberate, and writes `local-run.json` in addition to the normal case packet.  It starts the case runner with the Council API backend so Pi council agents can deliberate through MCP instead of direct model calls inside the case runner.

Basic example:

```bash
set -a
. path/to/aar-env.sh
set +a

pool="$(pwd)/pool.jsonl"

.bin/aar run \
  --openclaw-auth codex \
  --openclaw-codex-auth "$HOME/.codex/auth.json" \
  --council-pool "$pool" \
  ex01
```

`aar run` accepts at most one example name.  When the example name is present, it uses `examples/EXAMPLE/complaint.md`, creates a case id like `arb-ex01-YYYYMMDDHHMMSS`, and writes output under `out/EXAMPLE-openclaw-pi-YYYYMMDDHHMMSS` unless `--out-dir` is set.  Without an example name, it requires an explicit complaint path and uses a generated case id like `arb-YYYYMMDDHHMMSS`.

Important run flags:

| Flag | Meaning |
| --- | --- |
| `--complaint` | Complaint file.  Default for examples: `examples/EXAMPLE/complaint.md`. |
| `--file` | Explicit initial evidence file or glob.  May repeat. |
| `--out-dir` | Run output directory. |
| `--policy` | Policy JSON file. |
| `--council-size` | Override council size. |
| `--evidence-standard` | Override evidence standard. |
| `--common-root` | Shared `common/` tree. |
| `--council-pool` | Council JSONL request-spec pool.  Use an absolute path unless the pool lives under the common root. |
| `--caseapi-addr` | Private Case API address. |
| `--mcp-listen` | MCP listen address.  Default: `0.0.0.0:0`. |
| `--mcp-bearer-token` | MCP bearer token.  Default: generated. |
| `--council-timeout-seconds` | Council turn timeout.  Default: 900 seconds. |
| `--lawyer-timeout-seconds` | Lawyer turn timeout.  Default: 900 seconds. |
| `--max-response-bytes` | Runtime response size override. |
| `--invalid-attempt-limit` | Invalid attempt limit override. |
| `--engine` | Lean engine binary. |
| `--run-id` | Run id override. |
| `--case-id` | Case id override. |
| `--lawyer-instructions` | OpenClaw lawyer instruction template. |
| `--remote-lawyer-skill` | Remote OpenClaw lawyer skill template. |
| `--council-instructions` | Pi council instruction template. |
| `--auto-lawyers` | `both`, `plaintiff`, or `defendant`.  Default: `both`. |
| `--mcp-public-base-url` | Public MCP base URL for remote lawyers. |
| `--docker` | Docker command.  Default: `docker`. |
| `--podman` | Podman command.  Default: `podman`. |
| `--openclaw-image` | OpenClaw container image. |
| `--openclaw-model` | OpenClaw model.  Default: `gpt-5.5`. |
| `--openclaw-thinking` | OpenClaw thinking setting.  Default: `low`. |
| `--openclaw-timeout-seconds` | OpenClaw agent timeout.  Default: 3600 seconds. |
| `--openclaw-auth` | `auto`, `codex`, or `api-key`. |
| `--openclaw-codex-auth` | Codex `auth.json` path. |
| `--openclaw-lawyer-start-delay-seconds` | Delay between plaintiff and defendant container starts.  Default: 15 seconds. |
| `--pi-image` | Pi container image. |
| `--pi-mcp-adapter` | Pi MCP adapter path or package source. |
| `--council-output-limit-bytes` | Total stdout plus stderr limit per Pi council process.  Default: 128 MiB. |
| `--docker-mcp-host` | Host name Docker containers use to reach MCP.  Default: `host.docker.internal`. |
| `--podman-mcp-host` | Host name Podman containers use to reach MCP.  Default: `127.0.0.1`. |

The council output limit is enforced by the local `aar run` process while it monitors compacted Pi stdout logs and stderr byte counts.  Pi can emit JSON `message_update` records whose `thinking` or `text` fields repeat accumulated content.  The local runner compacts prefix-repeated content before writing and counting the stdout log, preserving only the new tail and adding `aar_log_filter.message: "earlier repeated message_update events dropped"`.  A council process that writes large non-repeated output can still exceed the configured limit, and the process can write more than the limit before the next monitor check kills it.  The failure event records the configured limit, bytes written, stdout bytes, stderr bytes, process name, process error, and failed council member.

`aar run` writes one pid file per child process in the output directory.  It writes MCP logs under `logs/mcp.stderr`, lawyer and council process logs under `logs/`, final case artifacts in the output root, and `local-run.json` with run-level settings.  After completion, it prints one final JSON result to stdout.  The process exits when the case reaches a terminal state or when an agent/process error requires termination.

## `aar council-replay`

`aar council-replay` runs one Pi council member against a saved AAR output packet.  The command starts a frozen local Council API server, starts an MCP server for that replay, starts one Pi council container, and waits for that member to submit one vote.  It writes a replay packet under `--out-dir`; it does not modify the source AAR output directory.

Replay has two bases.  `reconstructed_first_round` supports completed output packets that predate council-turn snapshots.  It reads `run.json`, `state.json`, `policy.json`, `runtime.json`, `evidence-manifest.json`, and `evidence-store/`, restores the case to deliberation round 1, clears council votes and the resolution, seats the supplied single member, and renders a fresh first-round council prompt.  `snapshot` supports newer output packets that contain `council-turns/turn-NNNNNN-MEMBER/input.json`; it reads the saved turn state and opportunity, then renders a fresh prompt with the supplied model config.

Basic reconstructed replay from `arb/`:

```bash
source="../../aar-attested/aar-ex03-20260613T210952Z/aar-output"
member=C1
arb_dir="$(pwd)"

jq --arg member "$member" --arg arb "$arb_dir" '
  .[] | select(.member_id == $member) |
  .request_spec + {
    persona: (
      if ((.persona_file // .request_spec.persona) | startswith("/"))
      then (.persona_file // .request_spec.persona)
      else $arb + "/" + (.persona_file // .request_spec.persona)
      end
    )
  }
' "$source/council.json" >"/tmp/aar-replay-$member.json"

.bin/aar council-replay \
  --basis reconstructed_first_round \
  --source-output "$source" \
  --config "/tmp/aar-replay-$member.json" \
  --out-dir "../aar-replays/aar-ex03-$member-same" \
  --member-id "$member" \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest
```

The config file must contain one JSON request-spec record.  Same-spec replay should derive that file from the member's `request_spec` in the original `council.json`, and the `persona` field must point to a readable persona file.  The example above uses an absolute persona path so the parser does not depend on the temporary config file's directory.

Snapshot replay uses a captured turn directory from a newer AAR output packet:

```bash
.bin/aar council-replay \
  --basis snapshot \
  --source-output out/ex03-new \
  --snapshot out/ex03-new/council-turns/turn-000009-C1 \
  --config /tmp/aar-replay-C1.json \
  --out-dir out/replays/ex03-C1-snapshot \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest
```

Important replay flags:

| Flag | Meaning |
| --- | --- |
| `--basis` | `reconstructed_first_round` or `snapshot`.  Required. |
| `--source-output` | Extracted AAR output directory, or a run directory containing `aar-output` or `aar-partial`.  Required. |
| `--snapshot` | Snapshot directory or `input.json`.  Required for `snapshot`. |
| `--config` | Single council JSON request-spec record.  Required. |
| `--out-dir` | Replay output directory.  Required. |
| `--member-id` | Council member id for `reconstructed_first_round`.  Default: `C1`. |
| `--prompt-dir` | Prompt directory override.  From `arb/`, the default `prompts/` is correct. |
| `--council-instructions` | Pi council instruction template.  From `arb/`, the default `agent-instructions/pi-council.md.tmpl` is correct. |
| `--podman` | Container command for Pi council.  Use `--podman docker` when Docker runs the Pi image. |
| `--pi-image` | Pi container image. |
| `--timeout-seconds` | Replay council timeout.  Default: 900 seconds. |
| `--council-output-limit-bytes` | Total stdout plus stderr limit for the replay Pi process.  Default: 128 MiB. |

When running from the repository root with `go run`, pass prompt and instruction paths explicitly because the defaults are relative to the process working directory:

```bash
go run ./arb/runtime/cmd/aar council-replay \
  --basis reconstructed_first_round \
  --source-output ../aar-attested/aar-ex03-20260613T210952Z/aar-output \
  --config /tmp/aar-replay-C1.json \
  --out-dir ../aar-replays/aar-ex03-C1-same \
  --member-id C1 \
  --prompt-dir arb/prompts \
  --council-instructions arb/agent-instructions/pi-council.md.tmpl \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest
```

The replay output directory contains `input.json`, `prompt.txt`, `result.json`, `tool-calls.ndjson`, one Pi pid file, and logs under `logs/`.  `result.json` records the replay status, vote, rationale, model, source output directory, tool calls, and the replay input.  `tool-calls.ndjson` records each Council API tool call in order, which is the fastest way to see whether the member read evidence bytes before voting.

## `aar verify-certificate`

`aar verify-certificate` checks a completed packet's replay certificate.  The command reads `certificate.json`, replays its initialization request and accepted public actions through the configured Lean engine, and compares the replayed final state to the certificate's claimed final-state hash.  It also reads `state.json` from the same packet and requires that file to match the certificate hash.

The certificate contains the engine-visible transition record.  `initialize_request` contains the exact initial state, proposition, and council roster sent to `initialize_case`.  `actions` contains the public actions the engine accepted, in order, with `action_type`, `actor_role`, and `payload`.  `claimed_final_state_sha256` is the SHA-256 hash of the compact JSON encoding of `claimed_final_state`.

The name "certificate" overstates what this file is.  It is a package of the run's input, its accepted-action record, and its claimed final state, with hashes tying the package to the packet.  It carries no signature and no endorsement.  The word is borrowed from complexity theory, where a certificate is a witness that makes a claim checkable without search; here the check is a full re-execution of every engine transition, and it saves work only because the recorded actions remove any search and the model calls are not repeated.  A passing verification shows that the claimed outcome follows from the recorded history under the engine's rules.  It does not show that the recorded history is what actually happened: any internally legal history yields a passing package.  Establishing that the record is genuine requires attested execution or records held by the participants themselves.

Verification checks four conditions:

| Check | Failure reported |
| --- | --- |
| The claimed final-state hash matches `claimed_final_state`. | `certificate final state hash mismatch` |
| The packet's `state.json` matches the claimed final-state hash. | `packet final state mismatch` |
| The Lean engine accepts `initialize_case` and every recorded action. | `initialize_case rejected` or `certificate action N (...) rejected` |
| Replaying the recorded actions yields the claimed final state. | `replayed final state mismatch` |

Basic command:

```bash
.bin/aar verify-certificate --dir out/ex01-direct
```

Important flags:

| Flag | Meaning |
| --- | --- |
| `--dir` | Output packet directory containing `certificate.json` and `state.json`. |
| `--certificate` | Certificate path override. |
| `--state` | Final state path override. |
| `--engine` | Lean engine binary. |

Successful verification prints a JSON object with `status: "ok"`, the case id, the run id when present, the accepted action count, and the final-state hash.  A certificate hash mismatch, packet-state mismatch, rejected replay action, or replayed final-state mismatch exits with an error.  The command does not inspect lawyer work notes, logs, or evidence bytes; it checks the engine-visible state transition sequence recorded in the certificate.

The service APIs expose `certificate.json` through artifact routes when the packet contains it.  They do not run certificate verification automatically.  Verification remains an explicit operator action through `aar verify-certificate`.

## `aar juror-replay`

`aar juror-replay` runs one fresh Pi deliberation from a saved AAR output packet with a model config and persona chosen at command time.  It starts the same frozen Council API, MCP server, Pi container, and replay recorder used by `aar council-replay`.  The command supports persona experiments, alternative-model comparisons, and repeat runs against existing `ex*` output packets.

The command needs four inputs: a source AAR output packet, one JSON model request-spec record, one persona text file, and a new output directory.  The source output can be a directory containing `run.json`, or a parent run directory containing `aar-output/` or `aar-partial/`.  The model config can come from an original run's `council.json`, from `pool.jsonl`, or from another file containing one request-spec JSON object accepted by `common/modelrequest`.

Snapshot selection controls the case state presented to the fresh juror.  An explicit `--snapshot` uses that saved turn input.  A supplied `--member-id` makes the command scan `council-turns/*/input.json` and require exactly one snapshot with that `member_id`.  When the source output has no `council-turns/` directory, the command uses `reconstructed_first_round`, which rebuilds a first-round deliberation from the durable run files.

Create a model config from an original council member:

```bash
source="out/local-direct-three-per-ex-only-20260629/ex13/run-03"
member=C1

jq --arg member "$member" '
  .[] | select(.member_id == $member) | .request_spec
' "$source/council.json" >"/tmp/aar-juror-replay-$member-model.json"
```

Create a model config from the current AAR pool instead:

```bash
jq -c '
  select(.openrouter_model_id == "minimax/minimax-m2.5")
  | select(.provider_name == "Minimax")
' pool.jsonl | head -n 1 >"/tmp/aar-juror-replay-pool-model.json"
```

Run from `arb/` with an experimental persona:

```bash
.bin/aar juror-replay \
  --source-output "$source" \
  --member-id "$member" \
  --model-config "/tmp/aar-juror-replay-$member-model.json" \
  --persona "../evals/model-pool/personas/experiments/attorneys/Brandeis.txt" \
  --out-dir "out/juror-replays/ex13-run-03-$member-brandeis" \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest
```

Run from the repository root with `go run` by passing the prompt and instruction paths explicitly:

```bash
go run ./arb/runtime/cmd/aar juror-replay \
  --source-output arb/out/local-direct-three-per-ex-only-20260629/ex13/run-03 \
  --member-id C1 \
  --model-config /tmp/aar-juror-replay-C1-model.json \
  --persona evals/model-pool/personas/experiments/attorneys/Brandeis.txt \
  --out-dir arb/out/juror-replays/ex13-run-03-C1-brandeis \
  --prompt-dir arb/prompts \
  --council-instructions arb/agent-instructions/pi-council.md.tmpl \
  --podman docker \
  --pi-image agentcourt-pi-sandbox:latest
```

Important `juror-replay` flags:

| Flag | Meaning |
| --- | --- |
| `--source-output` | Extracted AAR output directory, or a run directory containing `aar-output` or `aar-partial`.  Required. |
| `--model-config` | Single JSON request-spec record.  Required.  Pool JSONL rows and `council.json` request specs both satisfy this format. |
| `--persona` | Persona text file for the fresh juror.  Required.  Relative paths resolve from the current working directory. |
| `--out-dir` | Replay output directory.  Required. |
| `--basis` | Optional replay basis.  Valid values are `reconstructed_first_round` and `snapshot`.  Omit it for automatic selection. |
| `--snapshot` | Snapshot directory or `input.json`.  This selects snapshot replay directly. |
| `--member-id` | Member id used to find one snapshot, or the member id used for reconstructed replay. |
| `--prompt-dir` | Prompt directory override.  From `arb/`, the default `prompts/` is correct. |
| `--council-instructions` | Pi council instruction template.  From `arb/`, the default `agent-instructions/pi-council.md.tmpl` is correct. |
| `--podman` | Container command for Pi council.  Use `--podman docker` when Docker runs the Pi image. |
| `--pi-image` | Pi container image. |
| `--timeout-seconds` | Replay council timeout.  Default: 900 seconds. |
| `--council-output-limit-bytes` | Total stdout plus stderr limit for the replay Pi process.  Default: 128 MiB. |

The command prints one JSON summary to stdout.  `status=ok` means the fresh juror submitted a vote, while `status=error` reports the setup, container, provider, timeout, or tool error that stopped the replay.  The output directory contains `input.json`, `prompt.txt`, `result.json`, `tool-calls.ndjson`, a Pi pid file, logs under `logs/`, and `juror-replay.json`.

Use these checks after a run:

```bash
jq '{status,basis,case_id,member_id,model,vote,tool_call_count,persona_path,snapshot_dir}' \
  out/juror-replays/ex13-run-03-C1-brandeis/juror-replay.json

jq -r '.tool' out/juror-replays/ex13-run-03-C1-brandeis/tool-calls.ndjson

rg -n 'Persona:|You are an attorney' out/juror-replays/ex13-run-03-C1-brandeis/prompt.txt
```

`juror-replay.json` records the source output, selected snapshot, model config path, persona path, persona SHA-256, vote, rationale, and tool-call count.  `input.json` records the rendered prompt, case view, evidence manifest, policy, runtime limits, and selected seat.  `tool-calls.ndjson` records the Council API calls in order, which shows whether the fresh juror examined evidence bytes before voting.

Common failures have specific causes:

| Message or symptom | Cause | Fix |
| --- | --- | --- |
| `OPENROUTER_API_KEY is required` | The selected Pi model config uses OpenRouter. | Export `OPENROUTER_API_KEY` in the environment that runs `aar juror-replay`. |
| `stat persona ...` or `empty persona text` | `--persona` points to a missing, directory, or empty file. | Pass the intended persona text file, usually under `../evals/model-pool/personas/experiments/` from `arb/`. |
| `source output has multiple council-turn snapshots` | The source run has more than one captured turn and the command cannot infer the target turn. | Pass `--member-id MEMBER` or `--snapshot PATH`. |
| `member MEMBER has N council-turn snapshots` | The same member has more than one captured turn, usually after later deliberation rounds. | Pass the exact `--snapshot` directory. |
| `operation not permitted` while binding `127.0.0.1:0` | The process cannot open the local replay HTTP listener in the current environment. | Run the command in a local shell with permission to bind loopback ports. |
| Pi image or container command failure | The configured container command cannot run the Pi image. | Check `docker image inspect agentcourt-pi-sandbox:latest` or the matching Podman image, then use `--podman docker` or `--podman podman` consistently. |
| Missing prompt or instruction template | The command ran from a directory where default relative paths do not exist. | Run from `arb/`, or pass `--prompt-dir arb/prompts` and `--council-instructions arb/agent-instructions/pi-council.md.tmpl`. |

The replay output can include a large `pi-MEMBER/` filesystem because Pi installs or caches runtime packages inside the replay home.  The replay runner removes generated secret files such as `.mcp.json` and Pi `auth.json` before returning, including failed Pi-start paths.  Keep `input.json`, `prompt.txt`, `result.json`, `tool-calls.ndjson`, `juror-replay.json`, and `logs/` when publishing or comparing replay behavior.

## OpenClaw Lawyer Auth

Codex auth mode copies only `auth.json` into a per-lawyer Codex home under the run output directory, mounts that directory into the OpenClaw container as `/aar-codex`, and sets `CODEX_HOME=/aar-codex`.  The container command unsets `OPENAI_API_KEY`, reads the staged access token, and imports it into OpenClaw with `openclaw models auth paste-token --provider openai --profile-id openai:codex`.  `aar run` removes those staged Codex homes during normal cleanup; an interrupted process can leave a staged copy behind and should be checked before preserving or sharing the run directory.

Use this command shape for local runs:

```bash
pool="$(pwd)/pool.jsonl"

.bin/aar run \
  --openclaw-auth codex \
  --openclaw-codex-auth "$HOME/.codex/auth.json" \
  --council-pool "$pool" \
  ex04
```

API-key mode is supported by the code.  It requires `OPENAI_API_KEY` and passes that variable into the OpenClaw container.  Use it only when the deployment intentionally uses Platform API billing for OpenClaw lawyers.

## Secrets And Access

Treat Codex `auth.json`, copied per-lawyer Codex homes, `OPENAI_API_KEY`, `OPENROUTER_API_KEY`, service bearer tokens, MCP bearer tokens, and generated remote-lawyer skill files as secrets.  The generated remote-lawyer skill contains an MCP server JSON object with a bearer token for one case role.  Give that file only to the OpenClaw instance assigned to that role.

Run packets can contain case evidence, filings, private lawyer work notes, and process logs.  They should be handled as case material.  The command examples use placeholder environment files and hostnames so the manual can be copied without exposing local credentials or machine names.

## Remote OpenClaw Lawyers

Remote lawyer mode lets an independently running OpenClaw act as one lawyer.  The local `aar run` process still owns the case, starts MCP, starts the other lawyer container, starts Pi council members, and writes final output.  The remote OpenClaw connects through MCP and works autonomously by repeatedly calling `wait_for_opportunity`.

Use `--auto-lawyers defendant` when the remote OpenClaw will be the plaintiff.  AAR then starts only the defendant lawyer locally and writes `openclaw-plaintiff-lawyer-skill.md` in the output directory.  Use `--auto-lawyers plaintiff` when the remote OpenClaw will be the defendant.  AAR then starts only the plaintiff lawyer locally and writes `openclaw-defendant-lawyer-skill.md`.

Remote runs need a public MCP base URL that the remote OpenClaw process can reach.  The MCP listener is where AAR accepts traffic; the public base URL is what the generated skill gives to the remote OpenClaw.  In VM, NAT, or forwarded-network cases, those addresses often differ.

When the remote OpenClaw can reach the AAR host directly, bind MCP on the AAR host and use the reachable host name or IP address as the public base URL:

```bash
out="out/ex01-remote-plaintiff-$(date -u +%Y%m%d%H%M%S)"
AAR_HOST=aar-host.example
pool="$(pwd)/pool.jsonl"

.bin/aar run \
  --out-dir "$out" \
  --auto-lawyers defendant \
  --mcp-listen 0.0.0.0:8001 \
  --mcp-public-base-url "http://${AAR_HOST}:8001" \
  --openclaw-auth codex \
  --openclaw-codex-auth "$HOME/.codex/auth.json" \
  --council-pool "$pool" \
  ex01
```

If the remote OpenClaw can reach only localhost, run a TCP forward on the remote machine and set `--mcp-public-base-url` to that local forwarded URL.  The forward target must be a host and port that can reach the AAR MCP listener.

```bash
FORWARD_HOST=aar-forward.example
socat TCP-LISTEN:9001,bind=127.0.0.1,fork,reuseaddr "TCP:${FORWARD_HOST}:8001"
```

With that remote-localhost forward, start `aar run` with `--mcp-public-base-url http://127.0.0.1:9001`.  A healthy MCP service returns HTTP `204` at `/health`:

```bash
curl -i http://127.0.0.1:9001/health
```

Give the generated skill file to the remote OpenClaw.  The file contains the case id, role id, MCP URL, bearer token, server JSON, and the exact work loop.  The remote OpenClaw should configure MCP, call `wait_for_opportunity`, act on ready turns, send work notes before filings, submit admissible evidence when allowed, and stop when `wait_for_opportunity` returns `done`, `failed`, or `error`.

## `aar service`

`aar service` is the long-lived HTTP service.  It has three groups of routes.  The Clerk routes under `/clerk/v1` start and manage full `aar run` child processes.  The direct case routes under `/api/v1` start `aar case` child processes.  The role proxy routes under `/lawyerapi/v1` and `/councilapi/v1` forward role calls by `case_id` for direct `/api/v1/cases` records.

Start the service:

```bash
.bin/aar service \
  --listen 127.0.0.1:19770 \
  --out-root out/service \
  --aar-bin .bin/aar
```

The service prints `aar service listening on http://HOST:PORT` to stderr after binding the listener.

Important flags:

| Flag | Meaning |
| --- | --- |
| `--listen` | Service listen address.  Default: `127.0.0.1:19770`. |
| `--registry-dir` | Directory for `/api/v1/cases` records.  Defaults to `<out-root>/registry`. |
| `--out-root` | Parent output directory for service-managed cases.  Default: `out/service`. |
| `--aar-bin` | Path to the `aar` binary used for child processes.  Default: current executable. |
| `--common-root` | Shared `common/` tree passed to child cases when requested. |
| `--engine` | Lean engine binary passed to child cases when requested. |
| `--bearer-token` | Optional service bearer token. |
| `--case-startup-timeout` | Startup wait for `/api/v1/cases` child Case API health. |
| `--attested-driver` | Path to `service/attested/arb/run-arb-attested.py` for attested Clerk runs. |
| `--attested-uv` | Optional `uv` executable used as `uv run <attested-driver>`. |
| `--attested-parser` | Optional attestation parser path passed to the attested driver. |
| `--attested-input-prefix` | Default S3 input prefix for attested Clerk runs. |
| `--attested-output-prefix` | Default S3 output prefix for attested Clerk runs. |
| `--attested-output-root` | Default S3 output root for attested Clerk runs. |
| `--attested-exec-ami` | Default exec AMI for attested Clerk runs. |
| `--attested-dev-host` | Default `dev` host used by the attested driver. |
| `--attested-remote-attest-dir` | Default launcher directory on `dev`. |
| `--attested-aws-region` | Default AWS region. |
| `--attested-instance-type` | Default EC2 instance type. |
| `--attested-iam-instance-profile` | Default exec instance profile. |
| `--attested-image-tar-s3` | Default S3 URI for the arb attested workload image tar. |
| `--attested-root-volume-size-gb` | Default exec root volume size in GiB. |
| `--attested-exec-poll-attempts` | Default exec host poll attempts. |
| `--attested-poll-interval-seconds` | Default attested driver poll interval. |
| `--attested-timeout-seconds` | Default attested driver timeout. |
| `--attested-expected-pcr4` | Expected PCR4 for attested Clerk verification. |
| `--attested-expected-pcr7` | Expected PCR7 for attested Clerk verification. |
| `--attested-expected-pcr12` | Expected PCR12 for attested Clerk verification. |

If `--bearer-token` is set, every service request must include `Authorization: Bearer TOKEN`.  This token protects Clerk, case-management, role-proxy, artifact, and evidence routes alike.  The private `aar case` APIs started by child processes do not enforce the service bearer token.

## Clerk API

The Clerk API starts and tracks full `aar run` child processes.  It stores one record in each run output directory as `clerk.json`.  Listing scans immediate child directories under `--out-root` and reads those records.  There is no separate Clerk index.

The service role proxy routes are for direct `/api/v1/cases` records.  A Clerk-started run has its own case process and MCP server inside the child `aar run` process.  Remote lawyers use the MCP URL and generated skill from that run, while operators use Clerk routes to inspect the run record, final result, primary artifacts, and submitted evidence.

Create a case:

```bash
pool="$(pwd)/pool.jsonl"

curl -sS -X POST http://127.0.0.1:19770/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data @- <<EOF
{
    "example": "ex01",
    "openclaw_auth": "codex",
    "openclaw_codex_auth_path": "$HOME/.codex/auth.json",
    "council_pool_path": "$pool"
}
EOF
```

Create a case from an explicit complaint:

```bash
pool="$(pwd)/pool.jsonl"

curl -sS -X POST http://127.0.0.1:19770/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data @- <<EOF
{
    "case_id": "arb-custom-20260603123000",
    "complaint_path": "work/my-case/complaint.md",
    "case_files": ["work/my-case/source-a.pdf", "work/my-case/source-b.txt"],
    "out_dir": "arb-custom-20260603123000",
    "openclaw_auth": "codex",
    "openclaw_codex_auth_path": "$HOME/.codex/auth.json",
    "council_pool_path": "$pool"
}
EOF
```

Create an attested example run:

This section defines the service request shape for attested Clerk runs.  The image build, exec AMI, S3 artifact flow, and verification details live in the [AAR Docker Image Runbook](Dockerfile.md).  The `dev` host, secret-file, IAM, S3 permission, AMI, and PCR requirements live in [Attested AAR Dev Host Requirements](docs/attested-dev-host.md).

```bash
.bin/aar service \
  --listen 127.0.0.1:19770 \
  --out-root out/service \
  --aar-bin .bin/aar \
  --attested-driver "$(pwd)/tools/run-arb-attested.py" \
  --attested-exec-ami ami-REPLACE \
  --attested-output-root s3://agentcourt-data/arbattest/aar-runs \
  --attested-expected-pcr4 PCR4_HEX \
  --attested-expected-pcr7 PCR7_HEX
```

```bash
curl -sS -X POST http://127.0.0.1:19770/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data @- <<EOF
{
    "case_id": "attested-ex03-20260616120000",
    "run_id": "aar-ex03-20260616120000",
    "example": "ex03",
    "execution": {
        "mode": "attested",
        "attestation": {
            "input_prefix": "s3://agentcourt-data/arbattest/aar-inputs/aar-ex03-20260616120000",
            "output_prefix": "s3://agentcourt-data/arbattest/aar-runs/aar-ex03-20260616120000"
        }
    }
}
EOF
```

Create an attested run from an explicit complaint:

```bash
curl -sS -X POST http://127.0.0.1:19770/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data @- <<EOF
{
    "case_id": "attested-custom-20260616123000",
    "run_id": "aar-custom-20260616123000",
    "complaint_path": "work/my-case/complaint.md",
    "case_files": ["work/my-case/source-a.txt", "work/my-case/source-b.pdf"],
    "execution": {
        "mode": "attested",
        "attestation": {
            "input_prefix": "s3://agentcourt-data/arbattest/aar-inputs/aar-custom-20260616123000",
            "output_prefix": "s3://agentcourt-data/arbattest/aar-runs/aar-custom-20260616123000"
        }
    }
}
EOF
```

Attested Clerk execution accepts the same case selectors as local Clerk execution: either `example`, or `complaint_path` with optional `case_files`.  For complaint input, the attested driver calls `aar case-packet` on the service host, uploads `case.tar.gz` and `case-packet.json` under the S3 input prefix through `dev`, and sends packet hashes to the exec AMI.  Attested mode still rejects unsupported runtime overrides such as `policy_path`, `council_pool_path`, OpenClaw settings, Pi settings, and timeout overrides.

The `execution` object is optional for existing local Clerk clients.  If it is present, `execution.mode` is required and must be `local` or `attested`; local mode rejects nested attestation config.  Attested mode requires `execution.attestation`, an S3 `input_prefix`, an exec AMI, expected PCR4, expected PCR7, and the attested driver path, with those values supplied by service flags or by the request.

Attested mode always verifies before completion.  The service passes `--verify` to the attested driver and rejects `verify: false`.  The Clerk record reaches `completed` only after the driver exits successfully, writes `verification.log`, extracts `aar-output/`, and leaves a readable `aar-output/run.json`.

[AAR Docker Image Runbook](Dockerfile.md) and [Attested AAR Dev Host Requirements](docs/attested-dev-host.md) document the image build, S3 layout, dev-host requirements, artifact set, and verification checks for attested execution.  The manual describes the Clerk API shape and service behavior, while those runbooks describe the remote execution environment.  Keep the AMI id, expected PCR values, image tar S3 path, input prefixes, and output prefixes in those runbooks current when rebuilding the exec AMI or attested workload image.

The `out_dir` field, when present, must name an immediate child of the service output root.  If it is omitted, Clerk uses `<out-root>/<case_id>`.  Clerk refuses to start a run in a nonempty output directory.

List Clerk cases:

```bash
curl -sS http://127.0.0.1:19770/clerk/v1/cases
curl -sS 'http://127.0.0.1:19770/clerk/v1/cases?status=running'
```

Inspect one Clerk case:

```bash
curl -sS http://127.0.0.1:19770/clerk/v1/cases/arb-custom-20260603123000
```

Read final result or pending status:

```bash
curl -sS http://127.0.0.1:19770/clerk/v1/cases/arb-custom-20260603123000/result
```

Read live or final attestation events for an attested case:

```bash
curl -sS http://127.0.0.1:19770/clerk/v1/cases/attested-ex03-20260616120000/attestation/events
```

List and read output artifacts:

```bash
curl -sS http://127.0.0.1:19770/clerk/v1/cases/arb-custom-20260603123000/artifacts
curl -sS http://127.0.0.1:19770/clerk/v1/cases/arb-custom-20260603123000/artifacts/digest.md
```

Read submitted evidence by evidence id:

```bash
curl -sS http://127.0.0.1:19770/clerk/v1/cases/arb-custom-20260603123000/evidence/EVIDENCE_ID
```

Kill a Clerk case:

```bash
curl -sS -X POST http://127.0.0.1:19770/clerk/v1/cases/arb-custom-20260603123000/kill
```

Kill sends interrupt, waits 10 seconds, and then kills the child process if it has not exited.  After a service restart, Clerk reads disk records from the output root and reconciles active-looking records before returning them.  If terminal `run.json` exists, Clerk marks the record completed or failed from that artifact; otherwise it marks the record failed with `service restarted and child process is not attached`.

Artifact routes serve only the exact artifact names returned by the artifact list endpoint, such as `run.json`, `certificate.json`, `digest.md`, `transcript.md`, `work-notes.ndjson`, `events.ndjson`, `evidence-manifest.json`, `clerk.stdout`, and `clerk.stderr`.  For attested Clerk records, the same endpoint also lists downloaded top-level attestation files when present: `run.env`, `progress.log`, `launcher.log`, `run.log`, `manifest.json`, `manifest.sha384`, `attestation.b64`, `attestation.txt`, `verification.log`, `case.tar.gz`, `case-packet.json`, `aar-output.tar.gz`, and `aar-partial.tar.gz`.  Artifact routes do not serve arbitrary output files, process logs outside the listed set, generated remote-lawyer skill files, or staged Codex auth directories.  An unlisted artifact name returns `unknown_artifact`; a listed artifact whose file is absent returns `artifact_missing`.

The result route reads terminal `run.json`; the evidence route reads `evidence-manifest.json` and `evidence-store/` from the effective output directory.  Local Clerk runs use the run output directory directly, and the case process writes `evidence-manifest.json` at evidence-registry initialization and after each accepted submitted-evidence item.  An active local run that has not yet written the manifest returns HTTP `409` with error code `evidence_manifest_pending`; a terminal packet without a manifest returns HTTP `404` with error code `manifest_missing`.  Attested Clerk runs use the extracted `aar-output/` directory after verification, or the extracted `aar-partial/` directory for inspection after a failed remote run.

Clerk create request fields mirror `aar run` options in structured JSON:

| JSON field | Meaning |
| --- | --- |
| `example` | Example name under `examples/`.  Clerk checks `examples/EXAMPLE/complaint.md` before starting the child process and returns `unknown_example` when the complaint is missing. |
| `case_id` | Case id override.  Generated form: `arb-YYYYMMDDHHMMSS-RANDOM`. |
| `run_id` | Run id override. |
| `complaint_path` | Complaint file path.  Required unless `example` is set. |
| `case_files` | Initial evidence paths. |
| `out_dir` | Output directory child under `--out-root`. |
| `policy_path` | Policy JSON path. |
| `council_size` | Council size override. |
| `evidence_standard` | Evidence standard override. |
| `attorney_instructions` | Standing lawyer instructions path. |
| `prompt_dir` | Prompt directory override. |
| `attorney_common_prompt` | Attorney common prompt file. |
| `attorney_arguments_prompt` | Attorney arguments prompt file. |
| `attorney_rebuttals_prompt` | Attorney rebuttals prompt file. |
| `common_root` | Shared common root. |
| `council_pool_path` | Council pool JSONL path. |
| `caseapi_addr` | Private Case API address. |
| `mcp_listen` | MCP listen address. |
| `mcp_bearer_token` | MCP bearer token. |
| `council_timeout_seconds` | Council turn timeout. |
| `lawyer_timeout_seconds` | Lawyer turn timeout. |
| `max_response_bytes` | Runtime response byte limit. |
| `invalid_attempt_limit` | Invalid attempt limit. |
| `engine_path` | Lean engine binary. |
| `lawyer_instructions` | OpenClaw lawyer instruction template. |
| `remote_lawyer_skill` | Remote lawyer skill template. |
| `council_instructions` | Pi council instruction template. |
| `auto_lawyers` | `both`, `plaintiff`, or `defendant`. |
| `mcp_public_base_url` | Public MCP base URL for remote lawyers. |
| `docker_command` | Docker command. |
| `podman_command` | Podman command. |
| `openclaw_image` | OpenClaw image. |
| `openclaw_model` | OpenClaw model. |
| `openclaw_thinking` | OpenClaw thinking setting. |
| `openclaw_timeout_seconds` | OpenClaw agent timeout. |
| `openclaw_auth` | `auto`, `codex`, or `api-key`. |
| `openclaw_codex_auth_path` | Codex `auth.json` path. |
| `openclaw_lawyer_start_delay_seconds` | Delay between local OpenClaw lawyer starts. |
| `pi_image` | Pi container image. |
| `pi_mcp_adapter` | Pi MCP adapter path or package source. |
| `council_output_limit_bytes` | Total stdout plus stderr limit per Pi council process. |
| `docker_mcp_host` | Host name Docker containers use to reach MCP. |
| `podman_mcp_host` | Host name Podman containers use to reach MCP. |
| `execution` | Optional execution object.  Omit for local execution, or set `mode` to `local` or `attested`. |

Attested request fields live under `execution.attestation`:

| JSON field | Meaning |
| --- | --- |
| `verify` | Optional verification request.  `false` is rejected. |
| `driver_path` | Attested driver path. |
| `uv` | Optional `uv` executable used as `uv run <driver_path>`. |
| `parser` | Optional attestation parser path. |
| `input_prefix` | S3 prefix containing staged attested inputs. |
| `output_prefix` | S3 prefix for this run's terminal artifacts. |
| `output_root` | S3 parent prefix used when `output_prefix` is omitted. |
| `exec_ami` | Exec AMI. |
| `dev_host` | Host used by the attested driver to start the exec AMI. |
| `remote_attest_dir` | Launcher directory on `dev`. |
| `aws_region` | AWS region. |
| `instance_type` | EC2 instance type. |
| `iam_instance_profile` | Exec instance profile. |
| `image_tar_s3` | S3 URI for the arb attested workload image tar. |
| `root_volume_size_gb` | Exec root volume size in GiB. |
| `exec_poll_attempts` | Exec host poll attempts. |
| `poll_interval_seconds` | Attested driver poll interval. |
| `timeout_seconds` | Attested driver timeout. |
| `expected_pcr4` | Expected PCR4. |
| `expected_pcr7` | Expected PCR7. |
| `expected_pcr12` | Expected PCR12. |

`clerk.json` contains `case_id`, `run_id`, `example`, `pid`, `status`, `out_dir`, `stdout_log`, `stderr_log`, timestamps, exit code, final summary, and error text.  Attested records also contain `execution.mode`, the requested execution object, the resolved attested config after service defaults, and an attestation record with status, S3 prefixes, local archive paths, extracted output path, manifest hash, attestation text path, and verification log path.  `clerk.stdout` captures the child stdout, which is `aar run` for local Clerk cases and the attested driver for attested Clerk cases.

## Direct Case Service API

The `/api/v1/cases` API starts `aar case` children instead of full `aar run` children.  It is useful when the lawyers or council members will be driven through HTTP directly, without the local OpenClaw and Pi agents that `aar run` starts.  It stores case records under `--registry-dir` and can proxy `/lawyerapi/v1` and `/councilapi/v1` calls to the active child by `case_id`.  If the request supplies `out_dir`, that directory must be an immediate child of the service output root.

Create a direct service case:

```bash
curl -sS -X POST http://127.0.0.1:19770/api/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "api-case-1",
    "complaint_path": "examples/ex01/complaint.md",
    "out_dir": "out/service/api-case-1",
    "council_backend": "councilapi"
  }'
```

List and inspect:

```bash
curl -sS http://127.0.0.1:19770/api/v1/cases
curl -sS http://127.0.0.1:19770/api/v1/cases/api-case-1
curl -sS http://127.0.0.1:19770/api/v1/cases/api-case-1/result
```

Cancel:

```bash
curl -sS -X POST http://127.0.0.1:19770/api/v1/cases/api-case-1/cancel
```

Artifact routes serve only listed artifact names from a case output directory, including `certificate.json`, `service-logs/aar.stdout`, and `service-logs/aar.stderr` for service child process logs.  `GET /api/v1/cases/{case_id}/artifacts` lists known artifacts, and `GET /api/v1/cases/{case_id}/artifacts/{name}` serves one exact listed artifact name.  An unlisted artifact name returns `unknown_artifact`; a listed artifact whose file is absent returns `artifact_missing`.  `GET /api/v1/cases/{case_id}/evidence/{evidence_id}` serves accepted evidence by evidence id when the manifest contains a readable file name.

## Output Packet

Every completed or failed case writes a run packet under its output directory.  The exact file set depends on how far the case progressed, but these are the main files:

| File | Contents |
| --- | --- |
| `complaint.md` | Canonical complaint. |
| `policy.json` | Effective policy values. |
| `runtime.json` | Effective runtime limits. |
| `run.json` | Final structured result. |
| `state.json` | Final case state. |
| `certificate.json` | Initialization request, accepted public actions, claimed final state, and final-state hash for replay checking. |
| `council.json` | Council roster and related council metadata. |
| `digest.md` | Human-readable summary. |
| `transcript.md` | Human-readable transcript with filings and council votes. |
| `events.ndjson` | Event log.  Timestamps are UTC. |
| `work-notes.ndjson` | Off-record lawyer work notes. |
| `evidence-manifest.json` | Evidence metadata and custody information. |
| `evidence-store/` | Stored evidence bytes. |
| `submitted-evidence/` | Accepted lawyer-submitted evidence copies. |
| `council-turns/` | Council turn snapshots written before each council member acts. |
| `local-run.json` | `aar run` summary and run-level options. |
| `clerk.json` | Clerk service record when the run was started through Clerk. |

Useful inspection commands:

```bash
jq '{status, phase, resolution, final_reason, failure}' "$out/run.json"
jq '.final_state.case.council_votes' "$out/run.json"
jq '{case_id, run_id, actions:(.actions|length), claimed_final_state_sha256}' "$out/certificate.json"
jq -r '[.timestamp,.role,.phase,.event_type] | @tsv' "$out/events.ndjson"
jq -r '[.timestamp,.role,.phase,(.notes|length)] | @tsv' "$out/work-notes.ndjson"
```

Use `transcript.md` when reading the full procedural record.  Use `digest.md` when checking the final outcome and vote tally.  Use `certificate.json` with `aar verify-certificate` when checking that the recorded accepted actions replay to the packet's final state.  Use `evidence-manifest.json` and `evidence-store/` when exact source bytes, hashes, or evidence custody matter.

## Policy And Limits

The default policy has five council members, a preponderance evidence standard, and three required votes for a decision.  It allows three deliberation rounds, limits lawyer filing character counts by phase, limits offered exhibits and technical reports, and sets evidence upload and evidence-read limits.  A policy JSON file can override those fields.

The policy file controls procedure: council size, evidence standard, vote threshold, deliberation rounds, filing limits, exhibit and report limits, and evidence custody limits.  The complaint controls only the proposition.  Runtime settings such as turn deadlines, response byte limits, invalid-attempt limits, process output limits, and provider credentials belong to command options or service JSON, and `runtime.json` records the effective runtime values.

Policy validation rejects a zero council size, a zero decision threshold, a threshold above the council size, and any threshold that is not a strict majority.  The strict-majority rule prevents one vote distribution from satisfying both substantive outcomes.  The engine enforces rules that change the legal state, including phase order, filing limits, vote thresholds, deliberation rounds, and admitted-material counts.  Go enforces transport limits and byte-transfer budgets before material reaches the engine.

Important default runtime limits are 900 seconds per lawyer turn for `aar run`, 900 seconds per council turn for `aar run`, 128 KiB parsed response size for direct model responses, three invalid attempts per opportunity, and 4096 council output tokens.  `aar case` uses that token cap for direct council model calls.  `aar run` also writes that cap into Pi model configuration when the selected `pool.jsonl` entry does not specify `max_tokens` or `max_output_tokens`.  `aar case` direct council timeout defaults to 240 seconds unless overridden.  `aar run` gives lawyers and council members longer turn windows because OpenClaw and Pi agents may search, analyze, and call several tools.

A lawyer failure fails the case.  Examples include deadline expiration and exhausting invalid attempts.  A council member failure dismisses that member, records the failure, and lets the case continue under council rules.

## Failure And Status

Case status can be `draft`, active phase names, `closed`, or `failed` inside the case state.  Service records use process-oriented statuses such as `starting`, `running`, `completed`, `failed`, `killing`, and `killed`.  A completed service process may still contain a failed case if `run.json` reports `status: "failed"`.

`aar case` exits `0` for a procedural case failure when it has recorded the failure and written the final packet.  It writes a stdout summary with `status: "failed"`, `error`, and a structured `failure` object.  A process-level error, such as an unreadable complaint or unavailable engine, exits nonzero and reports an error.

`aar run` treats lawyer process failure as case failure or run failure depending on where the failure occurs.  It treats council process failure as council-member dismissal when AAR still has the same member opportunity ready.  It kills and reports a council process that writes more than the configured council output limit.

## Running Examples

List available examples:

```bash
find examples -maxdepth 2 -name complaint.md -printf '%h\n' | sort
```

Run `ex01` with local OpenClaw lawyers and Pi council:

```bash
set -a
. path/to/aar-env.sh
set +a

pool="$(pwd)/pool.jsonl"

.bin/aar run \
  --openclaw-auth codex \
  --openclaw-codex-auth "$HOME/.codex/auth.json" \
  --council-pool "$pool" \
  ex01
```

Run `ex04` with a dedicated output directory:

```bash
out="out/ex04-$(date -u +%Y%m%d%H%M%S)"
pool="$(pwd)/pool.jsonl"

.bin/aar run \
  --out-dir "$out" \
  --openclaw-auth codex \
  --openclaw-codex-auth "$HOME/.codex/auth.json" \
  --council-pool "$pool" \
  ex04
```

Run `ex01` through Clerk:

```bash
.bin/aar service \
  --listen 127.0.0.1:19770 \
  --out-root out/service \
  --aar-bin .bin/aar
```

In another terminal:

```bash
curl -sS -X POST http://127.0.0.1:19770/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data @- <<EOF
{
    "example": "ex01",
    "openclaw_auth": "codex",
    "openclaw_codex_auth_path": "$HOME/.codex/auth.json",
    "council_pool_path": "$(pwd)/pool.jsonl"
}
EOF
```

## Troubleshooting

If `aar run` fails before starting agents, check environment variables first.  `OPENROUTER_API_KEY` must be set for Pi council agents.  Codex auth mode needs a readable `auth.json`, and API-key mode needs `OPENAI_API_KEY`.

If OpenClaw containers cannot reach MCP, check the MCP URL from the same network context as the container or remote OpenClaw.  A direct terminal `curl` may not prove that an agent process has the same access.  Test `/health` on the MCP public base URL and fix any VM, NAT, firewall, or local-forward problem before starting the remote lawyer.

If a remote OpenClaw says the MCP health endpoint disappeared after deliberation, check whether `aar run` already finished and shut down MCP.  Final results are in the local output directory, especially `run.json`, `digest.md`, and `transcript.md`.  The remote OpenClaw may not be able to retrieve the final result through MCP after the local run exits.

If a Clerk record reports `service restarted and child process is not attached`, the service found an active-looking `clerk.json` record without a current process handle and without terminal `run.json`.  The service does not reattach to that process.  Inspect the output directory, process table, and recorded `pid` before deciding whether any external cleanup is required.

If a run directory is rejected as nonempty, choose a new output directory.  AAR run packets are intended to be immutable records for one case run.  Reusing an output directory mixes artifacts and makes review unreliable.

If a lawyer fails by deadline or invalid attempts, inspect `events.ndjson`, `work-notes.ndjson`, `logs/mcp.stderr`, and the lawyer process logs under `logs/`.  The failure object in `run.json` identifies the role, phase, opportunity id, reason, and message.  Treat that failure as a case failure, not a council-member dismissal.

If a council member fails, inspect `events.ndjson` for `council_member_removed` and related opportunity events.  Also inspect the corresponding Pi process stdout and stderr logs.  A single dismissed council member can be a valid case path if the remaining council rules produce a final decision.

A completed local `aar run` owns its OpenClaw Docker containers and Pi Podman containers through deterministic container names.  Normal cleanup removes those named containers and removes staged Codex auth homes; `docker ps` should show no `aar-...` OpenClaw containers, and `podman ps` should show no `agentcourt-pi-sandbox` container from the run.  If a run packet has `run.json` with terminal status but a Pi container remains, inspect `events.ndjson` for output-limit or agent-exit events, inspect `logs/pi-MEMBER.stdout`, and treat the leftover container as a local runner cleanup defect rather than a case artifact.

If an attested Clerk run stays `running` or reaches `failed`, inspect the Clerk record before using SSH or EC2 console output.  The record contains the resolved `input_prefix`, `output_prefix`, exec AMI, local output directory, verification state, and driver logs.  Use `/attestation/events` to check whether `aar run` is still writing lifecycle events, then read `progress.log`, `launcher.log`, and the S3 output prefix named by the record.

If an attested run fails before lawyers start, check the exact S3 input prefix first.  The prefix must contain `auth.json` and `keys.sh`, and complaint-packet mode also needs `case.tar.gz` and `case-packet.json` written by the driver.  Missing secrets, stale Codex auth, an old attested workload image, or an OpenClaw container that lacks host networking will fail before lawyer filings begin.

If attestation verification fails, treat the run as unverified even when `aar-output.tar.gz` exists.  Compare `manifest.json`, `manifest.sha384`, `attestation.txt`, and `verification.log`, then check the expected PCR values in the AAR Docker runbook before accepting any AMI or image change.  A completed AAR output packet without verified attestation can support debugging, but the Clerk record should not be treated as an attested completion.
