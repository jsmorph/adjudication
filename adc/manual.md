# Agent District Court Manual

## Overview

Agent District Court, or ADC, runs a civil case through a Lean rule engine and a Go runtime.  A complaint becomes a single-claim case packet, the case proceeds through pleadings, motions, discovery, trial, verdict, and judgment, and the runtime records the resulting case state.  The current external-agent path uses a case-owned HTTP Role API and an MCP adapter, while judge and clerk work remain internal direct-model work.

ADC has four main operating paths.  `adc case` starts from a complaint, prepares a normalized case, and runs the case with direct or external live roles.  `adc scenario` runs an existing scenario JSON without preparing a complaint.  `adc run` is the local full-run command that starts the case API, starts MCP, starts OpenClaw lawyers, and starts Pi jurors for active juror opportunities.  `adc service` is a long-running HTTP service that creates and manages child case processes, defaulting to full `adc run` cases.

All commands in this document assume the working directory is `adc/` unless a command says otherwise.  Build outputs go under `.bin/`, generated case output usually goes under `out/`, and the Lean engine binary is `.bin/adcengine`.

## Operating Model

The case process owns the litigation.  It owns the Lean state, current phase, current opportunity, case-file visibility, decision validation, turn deadlines, invalid-attempt limits, juror replacement or dismissal behavior, work-note logging, event logging, and final output.  Lawyers and jurors act as clients of that process through HTTP or MCP, and they do not need filesystem access to the run output directory.

ADC exposes live role work at the boundary where Lean returns an opportunity.  If the opportunity belongs to an internal role, the Go runtime calls a model directly.  If the opportunity belongs to an external role, the runtime publishes the opportunity through `/roleapi/v1` and waits for that role to submit a decision or report failure.  `adc run` marks plaintiff, defendant, and juror as external roles.

MCP is an adapter over the Role API.  An MCP session binds to one case id and one role id, with `principal_id` required for a juror.  The MCP tool set stays stable during the session; each opportunity tells the agent which legal tools Lean currently permits and how much time and attempt budget remains.

## Key Capabilities

`adc run` can run local OpenClaw lawyers with Codex OAuth-derived credentials from `auth.json`.  In `--openclaw-auth codex` mode, ADC copies the selected auth file into a per-lawyer private directory under the case output directory, mounts that directory as the container's `CODEX_HOME`, and unsets `OPENAI_API_KEY` inside the OpenClaw command.  The lawyer receives MCP configuration and assignment text, then talks to the case through MCP tools backed by the case HTTP Role API.

`adc run` can run Pi jurors through the same MCP and HTTP path.  When a juror receives an active opportunity, ADC creates a fresh Pi home for that juror and opportunity, writes `.mcp.json` with the juror MCP session URL, and writes `.pi/agent/settings.json` plus `.pi/agent/models.json` from the selected JSONL pool record.  The Pi process handles that one opportunity and stops after a successful submission.  At deliberation, the fresh juror prompt includes the trial transcript from openings through closings, the jury instructions, and directions to inspect admitted exhibits and visible case files through MCP.

`adc service` exposes the same full-run behavior through `/clerk/v1/cases`.  A create request with omitted `mode` or `mode: "run"` starts `adc run`, so the child case gets the case API, MCP adapter, OpenClaw lawyers, and Pi jurors.  `mode: "direct"` starts `adc case` or `adc scenario`, which is useful when the caller wants only the Role API and will manage external agents separately.

## Operator Guidance

Select the command by the boundary under test.  Use `adc case` or `adc scenario` for the legal state machine, Role API, and direct model behavior.  Use `adc run` for local agent execution, including OpenClaw lawyers, Pi jurors, MCP, container credentials, and process supervision.  Use `adc service` for HTTP creation, status, artifacts, evidence, kill, and attestation routes.

Treat each output directory as the record for one case.  Preserve `run.json`, `state.json`, `certificate.json`, `events.ndjson`, `run.db`, transcripts, digests, work notes, and service records together.  Use `events.ndjson` for lifecycle reconstruction, `run.json` for the machine-readable result, `state.json` for the terminal Lean state, `certificate.json` for replay checking, `digest.md` for a short written account, and `work-notes.ndjson` when evaluating agent planning and evidence strategy.

## Choosing A Command

| Goal | Command |
| --- | --- |
| Draft a complaint from a situation file. | `adc complain --situation FILE` |
| Prepare and run one complaint-driven case with direct internal roles unless external roles are named. | `adc case --complaint FILE` |
| Build a deterministic complaint packet for attested input. | `adc case-packet --complaint FILE --packet case.tar.gz --manifest case-packet.json` |
| Run an existing scenario JSON without starting OpenClaw or Pi agents. | `adc scenario --scenario FILE` |
| Run a local full case with OpenClaw lawyers and Pi jurors. | `adc run --complaint FILE` or `adc run --scenario FILE` |
| Run a local case where one lawyer is an independently running OpenClaw. | `adc run --auto-lawyers defendant` for a remote plaintiff, or `adc run --auto-lawyers plaintiff` for a remote defendant. |
| Run a standalone MCP adapter for an existing case API or service role proxy. | `adc mcp --caseapi-base URL` |
| Create and manage child cases over HTTP. | `adc service` |
| Validate an existing scenario JSON. | `adc validate --scenario FILE` |
| Replay-check a completed packet against its final state. | `adc verify-certificate --dir DIR` |
| Sample a juror pool from persona clusters. | `adc pool --size N` |
| Query the run database as PACER-style documents. | `adc pacer --db FILE` |
| Send one prompt through the model client for development checks. | `adc llm --prompt TEXT` |

## Repository Layout

| Path | Meaning |
| --- | --- |
| `runtime/cmd/adc/` | Go command-line package for `adc`. |
| `runtime/cli/` | CLI parsers for all subcommands. |
| `runtime/runner/` | Case runner, Lean opportunity loop, Role API, case-file actions, turn execution, reports to storage. |
| `runtime/mcp/` | MCP server that forwards tool calls to `/roleapi/v1`. |
| `runtime/localrun/` | `adc run`: starts the case, MCP, OpenClaw lawyers, and Pi jurors. |
| `runtime/service/` | Long-running HTTP service for creating, listing, killing, and inspecting child cases. |
| `runtime/casegen/` | Complaint intake, strategy planning, and scenario generation. |
| `runtime/courts/` | Court profile resolution and validation. |
| `runtime/spec/` | Scenario JSON types and loader. |
| `runtime/store/` | SQLite storage and PACER-style document view. |
| `engine/` | Lean rule engine and proof project. |
| `agent-instructions/` | Templates given to OpenClaw lawyers and Pi jurors by `adc run`. |
| `examples/` | Example civil cases and source documents. |
| `docs/` and `analysis/` | Rules, technical references, diagrams, and procedure notes. |

## Build And Environment

Build from `adc/`.  `make build` builds the Lean engine and the Go CLI, then writes `.bin/adcengine` and `.bin/adc`.  Use this build before a real run because the Go runtime expects the engine command to exist.

```bash
make build
```

The Go runtime tests run from `adc/runtime` or through the Makefile.  The Makefile target uses the current module and package layout.  The Lean proof build is separate and can take longer than the Go tests.

```bash
make test
make prove
```

`adc run` uses Docker for OpenClaw lawyers and Podman for Pi jurors.  The default OpenClaw image is `ghcr.io/openclaw/openclaw:latest`; the default OpenClaw model is `gpt-5.5` with thinking set to `low`.  The default Pi image is `agentcourt-pi-sandbox`, unless `PI_CONTAINER_IMAGE` is set and `--pi-image` is omitted.  The default Pi MCP adapter path is `/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter`, which the shared Pi image builds from pinned `pi-mcp-adapter@2.11.0`.

Pi jurors require `OPENROUTER_API_KEY`.  The juror model request comes from a JSONL request-spec pool, and `adc run` requires a readable pool file even if the selected scenario reaches jurors late.  Request-spec records must contain an OpenRouter endpoint and model.  ADC rejects Pi juror request specs that require temperature or top-p settings because the current Pi config writer cannot enforce those parameters.

OpenClaw lawyers can use Codex auth or `OPENAI_API_KEY`.  With `--openclaw-auth auto`, ADC first tries a readable Codex auth file and then falls back to `OPENAI_API_KEY`.  The default Codex auth path is `$CODEX_HOME/auth.json` when `CODEX_HOME` is set, otherwise `$HOME/.codex/auth.json`.

```bash
export OPENROUTER_API_KEY=REPLACE_WITH_KEY
```

Use explicit paths for auth files and pools in repeatable runs.  Do not put local machine paths into checked-in documentation or example files.  The usual OpenClaw auth form is:

```bash
.bin/adc run \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-local \
  --openclaw-auth codex \
  --openclaw-codex-auth PATH/TO/auth.json
```

## Complaint And Setup Files

`adc complain` drafts a complaint markdown file from a situation markdown file.  It resolves a court profile, reads linked local files for context, and writes `complaint.md` beside the situation file unless `--out` is set.  The command uses the planner model and therefore requires model credentials through the normal OpenAI-compatible client environment.

```bash
.bin/adc complain \
  --situation examples/ex1/situation.md \
  --out examples/ex1/complaint.md
```

`adc case --complaint` and `adc run --complaint` both perform the same internal setup stage before the live case starts.  The setup stage loads the complaint, stages linked markdown attachments into the output directory, asks the planner for a normalized one-claim case packet, asks for private plaintiff and defense strategy memos, and writes `generated-scenario.json`.  The live case then runs from that generated scenario.

The generated setup files are part of the case output.  `normalized-case.json` is the structured case packet.  `plaintiff-strategy.md` and `defense-strategy.md` are private strategy memos used as role prompt preambles.  `generated-scenario.json` is the scenario JSON passed to the runner.

## Scenario Files

A scenario JSON describes the case without running complaint setup.  It contains the court, initial case metadata, claims, roles, optional deterministic turns, optional `loop_policy`, and assertions.  A generated complaint-based scenario uses `loop_policy.type = "autopilot_trial"`, which asks Lean for the next opportunity until the case reaches the configured stop status.

`adc validate` checks a scenario JSON before a run.  It reports unknown roles, missing deterministic action types, unsupported actions, and whether the scenario requires LLM turns.  It returns an error when the scenario is invalid.

```bash
.bin/adc validate --scenario out/ex1-local/generated-scenario.json
```

`adc scenario` runs an existing scenario JSON.  It can run deterministic scenarios offline when `--offline` is set, and it can expose selected roles through the Role API with repeated `--external-role` flags.  It writes `run.json`, `state.json`, `certificate.json`, `runtime.json`, `events.ndjson`, `run.db`, and optional transcript or digest files at the paths supplied by flags.

```bash
.bin/adc scenario \
  --scenario out/ex1-local/generated-scenario.json \
  --output out/scenario/run.json \
  --runtime out/scenario/runtime.json \
  --events out/scenario/events.ndjson \
  --db out/scenario/run.db \
  --transcript out/scenario/transcript.md \
  --digest out/scenario/digest.md
```

## Jury Configuration

Jury configuration lives in scenario policy and is applied by the clerk through `set_jury_configuration` when a jury case reaches trial setup.  The policy keys are `jury_juror_count`, `jury_unanimous_required`, and `jury_minimum_concurring`.  Direct commands expose those values as `--juror-count`, `--unanimous-required true|false`, and `--minimum-concurring`; `adc case`, `adc scenario`, and `adc run` all accept those flags.

For complaint-based runs, ADC writes the selected jury policy into `generated-scenario.json` before the live case starts.  For scenario-based runs, the same flags override the scenario policy at startup without editing the scenario file.  The engine validates the final clerk action, requiring 6 through 12 jurors and a minimum-concurring value between 6 and the configured jury size.

The Clerk service accepts the same values as create-request JSON fields: `juror_count`, `unanimous_required`, and `minimum_concurring`.  These fields apply to omitted `mode`, `mode: "run"`, and `mode: "direct"` child cases.  If the fields are omitted, ADC uses the scenario policy or the court defaults: six jurors, unanimity required, and minimum concurring six.

## `adc case`

`adc case` starts from a complaint and runs one case.  It prepares the complaint-driven scenario, opens the SQLite store, starts the Lean-backed runner, and writes a JSON summary to stdout when the case ends.  If `--caseapi-addr` is set, the process also exposes `/health` and `/roleapi/v1`; with no external roles, the Role API still reports status but live opportunities are handled internally.

Important flags:

| Flag | Meaning |
| --- | --- |
| `--complaint` | Complaint markdown path.  Required. |
| `--court` | Court profile name or JSON path. |
| `--out-dir` | Output directory for staged inputs and run artifacts. |
| `--model` | Default runtime model for generated scenario roles. |
| `--non-juror-model` | Model for judge, clerk, plaintiff, and defendant unless role-specific model flags override it. |
| `--plaintiff-model`, `--defendant-model`, `--judge-model`, `--clerk-model` | Role-specific non-juror model overrides. |
| `--planner-model` | Model for normalized case packet and strategy planning. |
| `--report-model` | Model for digest generation. |
| `--temperature`, `--non-juror-temperature`, `--juror-temperature` | Optional sampling settings. |
| `--juror-personas` | JSONL juror request-spec pool. |
| `--trial-mode` | `auto`, `jury`, or `bench`. |
| `--skip-voir-dire` | Empanel randomly from the candidate panel after setup. |
| `--juror-count` | Jury size for jury trials, 6 through 12. |
| `--unanimous-required` | `true` or `false`.  Omit to use the scenario or court default. |
| `--minimum-concurring` | Minimum concurring jurors needed for a verdict. |
| `--online` | Enable web search for internal direct model calls. |
| `--timeout-seconds` | HTTP timeout for model calls. |
| `--roleapi-timeout-seconds` | Timeout for each external opportunity. |
| `--external-role` | Role served through the Role API.  Repeat for `plaintiff`, `defendant`, or `juror`. |
| `--caseapi-addr` | Role API listen address. |
| `--case-id`, `--run-id` | Identifiers used in API requests and output. |
| `--engine` | Lean engine command. |

Example:

```bash
.bin/adc case \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-direct \
  --trial-mode jury
```

## `adc run`

`adc run` is the local full-run command.  It accepts exactly one of `--complaint` or `--scenario`, starts the case API in-process, starts an MCP server for that case, starts OpenClaw lawyers according to `--auto-lawyers`, and starts Pi juror processes for active juror opportunities.  It writes the runner result as JSON to stdout and writes run artifacts under `--out-dir`.

The command always configures plaintiff, defendant, and juror as external roles.  Judge and clerk remain internal direct-model roles.  Complaint-based runs first execute the same setup stage as `adc case`; scenario-based runs skip that setup and use the provided scenario JSON.

`adc run` also accepts the common jury-configuration flags: `--juror-count`, `--unanimous-required`, and `--minimum-concurring`.  Those flags affect the case policy used by the clerk's internal jury-configuration step.  They do not change Pi pool size directly; Pi jurors are started when the case creates juror opportunities from the configured jury.

OpenClaw lawyers use MCP.  ADC gives each OpenClaw container a server entry whose URL includes the case id and role id, then starts `openclaw agent` with assignment text from `agent-instructions/openclaw-lawyer.md.tmpl`.  The container does not need the case output directory or case files mounted, because `list_case_files`, `read_case_text_file`, `request_case_file`, and `read_case_file_bytes` expose the visible record through MCP.

Codex auth is the preferred OpenClaw credential path.  `--openclaw-auth codex --openclaw-codex-auth PATH/TO/auth.json` stages that file into per-role secret directories in the output tree.  `--openclaw-auth auto` chooses the same path when the auth file is readable, and uses `OPENAI_API_KEY` only when no readable auth file is available.

Pi jurors also use MCP.  ADC waits until Lean produces an active juror opportunity, reads that juror's request spec from the sampled pool, writes Pi config files for that exact request spec, and starts one Pi process for that principal id and opportunity id.  The generated config uses OpenRouter completions, carries provider routing through `compat.openRouterRouting`, and points the juror to the MCP session for `role_id=juror&principal_id={principal_id}`.  The case API prompt supplies the selected juror persona, and `agent-instructions/pi-juror.md.tmpl` tells the process to handle the active opportunity and stop.  ADC starts a new process if the same juror later receives another opportunity.

Important local-agent flags:

| Flag | Meaning |
| --- | --- |
| `--auto-lawyers` | `both`, `plaintiff`, or `defendant`.  The omitted role must be handled by a remote lawyer. |
| `--mcp-listen` | MCP listen address for local and remote agents. |
| `--mcp-public-base-url` | Public MCP base URL written into remote lawyer instructions.  Required for manual lawyer mode when MCP listens on a wildcard host. |
| `--mcp-bearer-token` | Bearer token expected from MCP clients.  A token is generated when this is omitted. |
| `--openclaw-auth` | `auto`, `codex`, or `api-key`. |
| `--openclaw-codex-auth` | Codex `auth.json` path for OpenClaw containers. |
| `--openclaw-image` | OpenClaw container image. |
| `--openclaw-model` | OpenClaw model name. |
| `--openclaw-thinking` | OpenClaw thinking setting. |
| `--openclaw-timeout-seconds` | Timeout passed to `openclaw agent`. |
| `--openclaw-lawyer-start-delay-seconds` | Delay between plaintiff and defendant container startup.  The default is 15 seconds. |
| `--openclaw-network` | Docker network for OpenClaw lawyer containers.  The supported non-empty value is `host`. |
| `--pi-image` | Pi container image. |
| `--pi-mcp-adapter` | Pi MCP adapter path or package source. |
| `--juror-output-limit-bytes` | Total stdout plus stderr byte cap per Pi juror process.  The default is 128 MiB. |
| `--docker-mcp-host` | Host name OpenClaw containers use to reach MCP. |
| `--podman-mcp-host` | Host name Pi containers use to reach MCP. |

Example local-agent run:

```bash
.bin/adc run \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-openclaw-pi \
  --openclaw-auth codex \
  --openclaw-codex-auth PATH/TO/auth.json
```

Example remote plaintiff and local defendant:

```bash
.bin/adc run \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-remote-plaintiff \
  --auto-lawyers defendant \
  --mcp-listen 0.0.0.0:8001 \
  --mcp-public-base-url http://HOST:8001 \
  --openclaw-auth codex \
  --openclaw-codex-auth PATH/TO/auth.json
```

When a lawyer role is manual, `adc run` writes `openclaw-plaintiff-lawyer-skill.md` or `openclaw-defendant-lawyer-skill.md` into the output directory.  Give that file to the remote OpenClaw, or paste the complete instructions into that OpenClaw session.  The instructions include the MCP URL, MCP server JSON, case id, role id, and the required loop: call `wait_for_opportunity`, act when ready, and stop when the case returns done or failed.

## Role API

The Role API lives under `/roleapi/v1` on a case API listener.  Every request includes `case_id`; lawyer requests use `role_id=plaintiff` or `role_id=defendant`; juror requests use `role_id=juror` and `principal_id=J1` or another juror id.  The read-only observer role uses `role_id=observer`.

| Method | Path | Purpose |
| --- | --- | --- |
| `GET` | `/health` | Report that the case API is listening. |
| `GET` or `POST` | `/roleapi/v1/status` | Return case status, current turn, and active opportunity if it belongs to the caller. |
| `GET` or `POST` | `/roleapi/v1/get` | Return the current prompt and opportunity for the caller without long waiting. |
| `GET` or `POST` | `/roleapi/v1/wait_for_opportunity` | Wait up to 30 seconds for a role opportunity or terminal status. |
| `GET` or `POST` | `/roleapi/v1/result` | Return final result, failed status, or pending status. |
| `POST` | `/roleapi/v1/do` | Execute `case_status`, support tools, `send_work_notes`, or `submit_decision`. |
| `POST` | `/roleapi/v1/fail` | Report external-agent failure for the active opportunity. |

`status`, `get`, and `wait_for_opportunity` return `status` values such as `waiting`, `active`, `done`, and `failed`.  Active opportunity responses include `opportunity_id`, `phase`, `kind`, `remaining_time_ms`, attempts remaining, support-tool budget, the current prompt, the role's visible case view, allowed legal tools, legal tool schemas, and support tool specs.  A role should use the `opportunity_id` from that response when submitting work notes or a decision.

`POST /roleapi/v1/do` uses this JSON shape:

```json
{
  "case_id": "adc-CASE",
  "role_id": "plaintiff",
  "principal_id": "",
  "opportunity_id": "OPPORTUNITY",
  "tool": "submit_decision",
  "arguments": {}
}
```

`case_status` reports the case and current turn and does not require an opportunity id.  `send_work_notes` writes private work notes outside the case record to `work-notes.ndjson`.  Support tools such as `get_case`, `list_case_files`, `read_case_text_file`, `request_case_file`, `read_case_file_bytes`, `explain_decisions`, and `get_juror_context` let a role inspect the record and visible files before acting.

Legal acts go through `submit_decision`.  A legal tool decision uses `kind=tool`, `tool_name`, and `payload`; a pass decision uses `kind=pass` and `reason`, but only when the active opportunity says passing is allowed.  Lean validates the decision against the active opportunity id, state version, role, allowed tools, and payload defaults.

Example wait request:

```bash
curl -sS \
  'http://127.0.0.1:9001/roleapi/v1/wait_for_opportunity?case_id=adc-CASE&role_id=plaintiff&timeout_ms=30000'
```

Example work notes:

```bash
curl -sS -X POST 'http://127.0.0.1:9001/roleapi/v1/do' \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "adc-CASE",
    "role_id": "plaintiff",
    "opportunity_id": "OPPORTUNITY",
    "tool": "send_work_notes",
    "arguments": {
      "notes": "Plan: read the complaint attachments, identify the strongest exhibit path, and decide whether to import a technical report before the next trial act."
    }
  }'
```

Example legal decision:

```bash
curl -sS -X POST 'http://127.0.0.1:9001/roleapi/v1/do' \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "adc-CASE",
    "role_id": "plaintiff",
    "opportunity_id": "OPPORTUNITY",
    "tool": "submit_decision",
    "arguments": {
      "kind": "tool",
      "tool_name": "record_opening_statement",
      "payload": {
        "party": "plaintiff",
        "summary": "Plaintiff will prove the pleaded claim through the complaint attachments, discovery responses, and admitted exhibits."
      }
    }
  }'
```

Failure behavior differs by role.  Lawyer failure fails the case because the party cannot continue the active opportunity.  Juror failure uses the existing juror timeout and dismissal path, including candidate replacement during voir dire when available and deliberating-juror removal when the remaining jury can still continue.

## MCP Adapter

`adc mcp` runs a Streamable HTTP MCP server over the Role API.  Start it with the case API base URL or service proxy URL.  The server accepts MCP requests at `/mcp`, has a health endpoint at `/health`, and creates one MCP session per `case_id`, `role_id`, and optional `principal_id`.

```bash
.bin/adc mcp \
  --caseapi-base http://127.0.0.1:9001 \
  --listen 0.0.0.0:8001 \
  --bearer-token TOKEN
```

MCP clients connect with query parameters:

```text
http://HOST:8001/mcp?case_id=adc-CASE&role_id=plaintiff
http://HOST:8001/mcp?case_id=adc-CASE&role_id=juror&principal_id=J1
http://HOST:8001/mcp?case_id=adc-CASE&role_id=observer
```

After `initialize`, the client must include the returned `Mcp-Session-Id` header on later requests.  Idle sessions expire after 30 minutes by default; `adc run` disables session expiry for its embedded MCP server.  `DELETE /mcp` with `Mcp-Session-Id` deletes a session.

The MCP tools are stable.  Every session has `get_current_opportunity`, `wait_for_opportunity`, `case_status`, and `get_case_result`.  Non-observer sessions also have `get_case`, `explain_decisions`, `list_case_files`, `read_case_text_file`, `request_case_file`, `read_case_file_bytes`, `get_juror_context`, `send_work_notes`, `submit_decision`, and `report_failure`.

The agent loop is mechanical.  Call `wait_for_opportunity` with a timeout of at most 30000 milliseconds.  If it returns `state=waiting`, call it again.  If it returns `state=ready`, read the prompt and opportunity, use support tools as needed, send work notes, and submit one decision.  If it returns `state=done` or `state=failed`, stop acting for that role.

## Legal Tools

ADC legal tools are the actions Lean recognizes for the current opportunity.  The Role API returns `allowed_legal_tools` and `legal_tool_specs` for each opportunity, and an agent should treat those fields as the authority for that turn.  The scenario role definitions define the broad role capability, but Lean decides the current subset based on phase, state, and procedural rules.

Plaintiff and defendant tools cover pleading, discovery, motions, trial presentation, exhibits, objections, closings, and post-verdict items.  Examples include `file_amended_complaint`, `file_answer`, `file_rule12_motion`, `serve_interrogatories`, `respond_interrogatories`, `serve_request_for_production`, `respond_request_for_production`, `file_rule56_motion`, `import_case_file`, `produce_case_file`, `offer_case_file_as_exhibit`, `submit_technical_report`, `record_opening_statement`, `submit_trial_theory`, `offer_exhibit`, `rest_case`, and `deliver_closing_argument`.  Jury-specific party tools include `record_voir_dire_question`, `challenge_juror_for_cause`, `strike_juror_peremptorily`, `propose_jury_instruction`, and `object_jury_instruction`.

Judge and clerk tools remain internal for the current full-run path.  The clerk can handle administrative acts such as service dates, jury demand, jury configuration, and adding jurors.  The judge can decide motions, control trial phase, resolve trial mode, handle voir dire rulings, settle and deliver jury instructions, enter judgment, and write bench opinions in bench trials.

Juror tools are limited.  Jurors answer questionnaires, answer voir dire questions, and submit one vote when deliberation reaches them.  A juror vote includes `juror_id`, `vote` as `plaintiff` or `defendant`, damages, confidence, and explanation.

Deliberating juror failure changes the effective vote threshold.  The nominal jury configuration remains in the case record, including `juror_count`, `unanimous_required`, and `minimum_concurring`.  Verdict derivation caps the required votes at the number of sworn jurors still eligible to deliberate, so five agreeing jurors can return a verdict after one six-person juror agent fails.  If no sworn jurors remain eligible, ADC records a hung jury.

## Juror Pools And Pi Agents

Juror pools use JSONL request-spec records.  The active full-run path expects records that can be parsed by `common/modelrequest`, with endpoint, model, persona, provider constraints, and request settings.  ADC writes each selected juror's Pi home with `.pi/agent/settings.json`, `.pi/agent/models.json`, and `.mcp.json`.  That generated Pi home is the source of truth for the juror process started by `adc run`.

The pool record is a request spec, not a short model string.  ADC reads the upstream OpenRouter model and applies provider routing and quantization settings through Pi's OpenRouter compatibility field.  The runner binds the same pool record's persona text to the juror opportunity prompt.  A pool record that requires temperature or top-p fails before the juror starts, because the Pi config produced here cannot enforce those settings.

The pool command samples records from `../common/data/personas/persona-clusters.csv` relative to the `adc/` working directory.  It emits JSONL records to stdout.  Save the result into a file and pass that file through `--juror-personas` when a run should use that pool.

```bash
.bin/adc pool --size 50 > ../common/data/personas/pool.jsonl
```

`adc run` starts a Pi juror process only when that juror first appears in the active opportunity.  It does not restart a juror process after it exits.  If the same juror receives an active opportunity after its process exited, `adc run` reports failure to the case API and lets the case owner apply the juror failure rule.  During deliberation, that rule removes the failed juror from the effective concurrence count.

## Utility Commands

ADC includes utility commands that produce or inspect inputs and outputs without starting local agents.  They prepare deterministic inputs, check scenario shape, sample juror pools, inspect a run database, and make a single model-client call during development.  They still use the same repository-relative defaults as the main commands, so run them from `adc/` unless a command supplies every path explicitly.

| Command | Purpose |
| --- | --- |
| `adc case-packet` | Build `case.tar.gz` and `case-packet.json` from a complaint for attested complaint input. |
| `adc validate` | Validate an existing scenario JSON. |
| `adc pool` | Sample a JSONL juror request-spec pool from shared persona-cluster data. |
| `adc pacer` | Read PACER-style documents from a run SQLite database. |
| `adc llm` | Send one prompt or prompt file through the model client. |

`adc case-packet` packages the complaint and linked local files into the deterministic packet format used by the attested ADC driver.  The packet contains the complaint and linked files with relative paths preserved, while the manifest records hashes for later verification.  Run this command when an attested complaint run fails before launch because a linked file is outside the complaint directory or cannot be resolved.

`adc pacer` reads `run.db` and returns structured document JSON, either for the latest case in the database or for the requested case and document id.  `adc llm` is a narrow model-client check that can use a literal prompt, a prompt file, a persona record, and a timeout.  `adc pool` writes JSONL to stdout; redirect that output when a run needs a repeatable pool file.

## Service API

`adc service` runs a long-lived HTTP service.  It creates, lists, kills, and inspects child cases, stores one `service-case.json` record in each output directory, and proxies `/roleapi/v1` calls to active child case APIs.  A create request with omitted `mode` or `mode: "run"` starts `adc run`, which starts the case API, MCP, OpenClaw lawyers, and Pi jurors.  A create request with `mode: "direct"` starts `adc case` or `adc scenario` without local OpenClaw or Pi agent startup.

Start the service:

```bash
.bin/adc service \
  --listen 127.0.0.1:19870 \
  --output-root out/adc-service \
  --adc-bin .bin/adc \
  --engine .bin/adcengine
```

Endpoints:

| Method | Path | Purpose |
| --- | --- | --- |
| `POST` | `/clerk/v1/cases` | Create a child case. |
| `GET` | `/clerk/v1/cases` | List known cases, optionally filtered by `status`. |
| `GET` | `/clerk/v1/cases/{case_id}` | Inspect one case record. |
| `POST` | `/clerk/v1/cases/{case_id}/kill` | Stop a child process. |
| `GET` | `/clerk/v1/cases/{case_id}/result` | Return final result, failed status, or pending status. |
| `GET` | `/clerk/v1/cases/{case_id}/artifacts` | List primary artifacts. |
| `GET` | `/clerk/v1/cases/{case_id}/artifacts/{name}` | Fetch one listed artifact from the case output directory. |
| `GET` | `/clerk/v1/cases/{case_id}/evidence/{evidence_id}` | Fetch submitted evidence by evidence id when the manifest maps it to a file. |
| `GET` | `/clerk/v1/cases/{case_id}/attestation/events` | Fetch live or downloaded NDJSON events for an attested child case. |
| any | `/roleapi/v1/{path}` | Proxy Role API calls based on `case_id`. |

The `/api/v1/cases` paths use the same implementation as `/clerk/v1/cases`.  They exist as service API aliases.  A bearer token can protect all service routes when `--bearer-token` is set.

Artifact routes serve only the exact artifact names returned by the artifact list endpoint, such as `run.json`, `state.json`, `certificate.json`, `digest.md`, `transcript.md`, `work-notes.ndjson`, `events.ndjson`, `evidence-manifest.json`, `service-logs/adc.stdout`, and `service-logs/adc.stderr`.  They do not serve arbitrary output files, process logs outside the listed set, generated remote-lawyer instruction files, or staged Codex auth directories.  An unlisted artifact name returns `unknown_artifact`; a listed artifact whose file is absent returns `artifact_missing`.  The evidence route reads `evidence-manifest.json` and serves submitted evidence by evidence id when the manifest maps that id to a readable file.  Local case processes write the manifest when the runner initializes and after case-file state changes, so active cases can serve evidence after the corresponding manifest update.  An active case that has not yet written the manifest returns HTTP `409` with error code `evidence_manifest_pending`; a terminal output packet without a manifest returns HTTP `404` with error code `manifest_missing`.

The create request is structured JSON.  Common fields include `case_id`, `run_id`, exactly one of `complaint_path` or `scenario_path`, `out_dir`, `model`, `juror_personas`, `engine_path`, `timeout_seconds`, `invalid_attempt_limit`, and `max_response_bytes`.  Jury configuration fields are `juror_count`, `unanimous_required`, and `minimum_concurring`; the service passes them to the child case process for local-agent and direct runs.  If `out_dir` is supplied, it must be an immediate child of the service `--output-root`; when it is omitted, the service uses `OUTPUT_ROOT/CASE_ID`.  Complaint-based runs also accept setup fields such as `court`, `non_juror_model`, `plaintiff_model`, `defendant_model`, `judge_model`, `clerk_model`, `planner_model`, `report_model`, `trial_mode`, and `skip_voir_dire`.

For `mode: "run"`, the create request also accepts the local-agent fields used by `adc run`: `mcp_listen`, `mcp_public_base_url`, `mcp_bearer_token`, `lawyer_instructions`, `remote_lawyer_skill`, `juror_instructions`, `auto_lawyers`, `docker_command`, `podman_command`, `openclaw_auth`, `openclaw_codex_auth_path`, `openclaw_image`, `openclaw_model`, `openclaw_thinking`, `openclaw_timeout_seconds`, `openclaw_lawyer_start_delay_seconds`, `pi_image`, `pi_mcp_adapter`, `juror_output_limit_bytes`, `docker_mcp_host`, and `podman_mcp_host`.  `roleapi_timeout_seconds` can set both lawyer and juror opportunity timeouts unless `lawyer_timeout_seconds` or `juror_timeout_seconds` is provided.

For `mode: "direct"`, the create request accepts `external_roles` to expose selected roles through the Role API while leaving agent startup to the caller.  Direct mode uses `roleapi_timeout_seconds` for external opportunities.  It does not start MCP, OpenClaw, or Pi processes.

Attested ADC runs use the same `POST /clerk/v1/cases` shape for case input: the request supplies `complaint_path`, optional `case_id`, optional `run_id`, and optional `out_dir`.  The request adds `execution.mode: "attested"` and an `execution.attestation` object, while the service supplies any defaults configured through `adc service --attested-*` flags.  The first attested ADC path supports complaint input only and rejects `scenario_path` and local runtime override fields until those fields have explicit attestation support.

The attested driver packages the complaint and linked local files into a deterministic case packet before it starts the exec AMI.  The exec container downloads `auth.json`, `keys.sh`, `case.tar.gz`, and `case-packet.json` from `INPUT_PREFIX`, verifies the packet hashes, runs `adc-run` inside the attested workload image, uploads live `events.ndjson`, and writes terminal artifacts to `OUTPUT_PREFIX`.  The exec entrypoint runs OpenClaw lawyer containers with `--openclaw-network host`, matching the verified ARB and AARD exec topology.  The service marks an attested case `completed` only after the driver verifies the attestation and extracts a readable `adc-output/run.json`.

Start the service with attested defaults when callers should not repeat the driver path, S3 roots, AMI id, and PCR values in every request.  The service flags correspond to the lower-level `service/attested/adc/run-adc-attested.py` options, and request-level attestation fields can override them when needed.  [ADC Docker Image Runbook](../service/attested/adc/Dockerfile.md) and [Attested ADC Dev Host Requirements](../service/attested/adc/attested-dev-host.md) document the image build, S3 layout, Clerk service sequence, verification procedure, and troubleshooting table.

```bash
adc-service \
  --listen 127.0.0.1:19870 \
  --output-root out/adc-service \
  --adc-bin .bin/adc \
  --adc-run-bin adc-run \
  --adc-working-dir "$(pwd)" \
  --engine .bin/adcengine \
  --attested-driver "$(pwd)/../service/attested/adc/run-adc-attested.py" \
  --attested-uv uv \
  --attested-input-prefix s3://agentcourt-data/arbattest/adc-inputs/adc-REPLACE_WITH_STAMP \
  --attested-output-root s3://agentcourt-data/arbattest/adc-runs \
  --attested-exec-ami ami-011f957fe91cf7b81 \
  --attested-expected-pcr4 83AC49DFAA5D76939970E1568472FF463FBE90C4038D000D31F6C0520F583D1DD51CE0C103CEB26E4B773AAD99A4B3B4 \
  --attested-expected-pcr7 98441C7F7625D10058C47683AEC486CE311C633235EB555593A7EE791121E3578AE72D04ECEF661F272D59058B77AF35
```

Create an attested complaint-based child case with verification required.  The artifact and result endpoints read from the extracted `adc-output/` directory after completion.  The attestation events endpoint reads the live S3 event object while the driver is still running when no local event file exists.

```bash
curl -sS -X POST http://127.0.0.1:19870/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "mode": "run",
    "case_id": "adc-attested-ex1",
    "complaint_path": "examples/ex1/complaint.md",
    "out_dir": "out/adc-service/adc-attested-ex1",
    "execution": {
      "mode": "attested",
      "attestation": {
        "verify": true
      }
    }
  }'
```

`POST /clerk/v1/cases/{case_id}/kill` applies only while the service has an attached active child process for that case.  Completed, failed, killed, or detached cases return a conflict response and keep their existing status.  The endpoint records the case as `killing` first, stops the child process, and lets the child watcher record the final `killed` status.

Create a complaint-based local-agent child case:

```bash
curl -sS -X POST http://127.0.0.1:19870/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "adc-service-ex1",
    "complaint_path": "examples/ex1/complaint.md",
    "out_dir": "out/adc-service/adc-service-ex1",
    "juror_count": 6,
    "unanimous_required": true,
    "minimum_concurring": 6,
    "openclaw_auth": "codex",
    "openclaw_codex_auth_path": "PATH/TO/auth.json",
    "juror_personas": "../common/data/personas/pool.jsonl"
  }'
```

Create a direct scenario-based child case:

```bash
curl -sS -X POST http://127.0.0.1:19870/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "mode": "direct",
    "case_id": "adc-service-scenario",
    "scenario_path": "out/ex1-local/generated-scenario.json",
    "out_dir": "out/adc-service/adc-service-scenario"
  }'
```

## Output Artifacts

Case output depends on the command, but the main files are stable.  Complaint-driven commands write setup files before the run begins.  `adc run` also writes process logs, PID files, remote lawyer instruction files when needed, and `local-run.json`.

| File | Meaning |
| --- | --- |
| `complaint.md` | Staged complaint text for complaint-driven runs. |
| `input-files/` | Staged linked complaint attachments. |
| `normalized-case.json` | Planner-produced one-claim case packet. |
| `plaintiff-strategy.md` | Private plaintiff plan used in the plaintiff prompt preamble. |
| `defense-strategy.md` | Private defense plan used in the defense prompt preamble. |
| `generated-scenario.json` | Scenario JSON generated from complaint setup. |
| `runtime.json` | Normalized timeout, response-size, and invalid-attempt limits. |
| `events.ndjson` | Runtime event log. |
| `run.db` | SQLite store. |
| `run.json` | Authoritative machine-readable result. |
| `state.json` | Terminal Lean state copied from `run.json` for certificate and artifact review. |
| `certificate.json` | Initial state, optional `initialize_case` request, accepted engine transitions, claimed final state, and final-state hash. |
| `transcript.md` | Human-readable transcript. |
| `digest.md` | Human-readable digest. |
| `work-notes.ndjson` | Private role work notes sent through `send_work_notes`. |
| `local-run.json` | `adc run` summary for local agent settings and run counts. |
| `logs/` | `adc run` logs for MCP, OpenClaw, and Pi processes. |
| `service-case.json` | Service record for service-created cases. |
| `service-logs/` | Child stdout and stderr logs for service-created cases. |

Use `run.json` for machine inspection and `state.json` when a tool needs the terminal state without the result envelope.  Use `certificate.json` with `adc verify-certificate` when checking that the accepted engine transitions replay to the packet's final state.  Use `digest.md` for a concise written account, `events.ndjson` to trace actions and agent events, and `work-notes.ndjson` when evaluating external-agent planning and work logs.

## `adc verify-certificate`

`adc verify-certificate` checks a completed packet's replay certificate.  The command reads `certificate.json`, replays the recorded initialization and accepted engine transitions through the configured Lean engine, and compares the replayed final state to the certificate's claimed final-state hash.  It also reads `state.json` from the same packet and requires that file to match the certificate hash.

The name "certificate" overstates what this file is.  It is a package of the run's input, its accepted-transition record, and its claimed final state, with hashes tying the package to the packet.  It carries no signature and no endorsement.  The word is borrowed from complexity theory, where a certificate is a witness that makes a claim checkable without search; here the check is a full re-execution of every engine transition, and it saves work only because the recorded actions remove any search and the model calls are not repeated.  A passing verification shows that the claimed outcome follows from the recorded history under the engine's rules.  It does not show that the recorded history is what actually happened: any internally legal history yields a passing package.  Establishing that the record is genuine requires attested execution or records held by the participants themselves.

```bash
.bin/adc verify-certificate --dir out/ex1-direct
```

The certificate contains the engine-visible transition record.  `initialize_request` contains the initial court state and, when the scenario used seeded complaint initialization, the exact `initialize_case` request fields.  `transitions` contains accepted `step` transitions and accepted pass decisions; rejected tool attempts, support-tool reads, work notes, and logs stay outside the certificate.

## Example Flows

The Makefile demo builds the binaries, signs the example source material, drafts `examples/ex1/complaint.md`, and runs `adc case`.  That path exercises complaint setup and the internal runtime.  It does not start OpenClaw lawyers or Pi jurors.

```bash
make demo
```

Run a local full case with OpenClaw lawyers and Pi jurors:

```bash
make build
export OPENROUTER_API_KEY=REPLACE_WITH_KEY
.bin/adc run \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-openclaw-pi \
  --openclaw-auth codex \
  --openclaw-codex-auth PATH/TO/auth.json
```

Run an existing generated scenario with direct internal roles:

```bash
.bin/adc scenario \
  --scenario out/ex1-openclaw-pi/generated-scenario.json \
  --output out/ex1-scenario/run.json \
  --runtime out/ex1-scenario/runtime.json \
  --events out/ex1-scenario/events.ndjson \
  --db out/ex1-scenario/run.db
```

Run a direct case with the plaintiff and defendant exposed through the Role API:

```bash
.bin/adc case \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-roleapi \
  --caseapi-addr 127.0.0.1:9001 \
  --external-role plaintiff \
  --external-role defendant
```

In another process, start MCP for those external roles:

```bash
.bin/adc mcp \
  --caseapi-base http://127.0.0.1:9001 \
  --listen 127.0.0.1:8001
```

## Troubleshooting

If `adc run` exits before starting agents, first check the required files and credentials.  It requires a scenario path or complaint path, an output directory, a case id, a juror pool path, `OPENROUTER_API_KEY`, instruction templates, and either Codex auth or `OPENAI_API_KEY` for OpenClaw.  Manual lawyer mode also requires an MCP public base URL when MCP listens on a wildcard host.

If complaint setup or `adc case-packet` fails, inspect the complaint path and linked files before changing runtime settings.  Linked local files must resolve under the complaint directory, and missing or external links prevent deterministic packet construction.  The generated `normalized-case.json`, `generated-scenario.json`, `case.tar.gz`, and `case-packet.json` identify whether the failure occurred during intake, planning, scenario generation, or packet writing.

If an OpenClaw container fails before a lawyer turn, inspect that lawyer's stderr log and its staged Codex auth directory under the output directory.  In Codex auth mode, ADC must be able to read and decode the host `auth.json`, write the staged copy, mount that directory as the container's `CODEX_HOME`, and import the staged access token into OpenClaw with `openclaw models auth paste-token --provider openai --profile-id openai:codex`.  In API-key mode, `OPENAI_API_KEY` must be present in the environment used to start `adc run`.

If a remote OpenClaw cannot connect, check the MCP health endpoint from the remote machine.  The URL is `http://HOST:PORT/health`, and it should return HTTP `204`.  Also check that the MCP URL given to the remote OpenClaw includes the correct `case_id`, `role_id`, and bearer token.

If a role reports `waiting`, check `current_turn` in the observer status response.  The case may be waiting on another role, a different juror principal, or an internal judge or clerk turn.  The observer request is:

```bash
curl -sS 'http://127.0.0.1:9001/roleapi/v1/status?case_id=adc-CASE&role_id=observer'
```

If a Pi juror fails at startup, inspect `logs/pi-JUROR.stderr`, `logs/pi-JUROR.stdout`, and that juror's generated `.pi/agent/models.json`.  The selected request spec must be OpenRouter-based and must use parameters Pi can enforce through the current config file.  If the process exceeds the output byte cap, `adc run` reports that failure through the Role API and the case owner applies the juror failure rule.  A failed deliberating juror should produce a timeout or failure event, and the remaining eligible jurors can still return a verdict when they reach the effective threshold.

If service-created cases remain in `starting`, check the service child logs and the case API health check.  The service polls `/health` for the configured startup timeout, then marks startup failure if the child case API never becomes healthy.  For local-agent cases, confirm that the create request used omitted `mode` or `mode: "run"` and supplied the OpenClaw and Pi settings needed by `adc run`.

For attested service-created cases, start diagnosis from the runbook's attestation troubleshooting table.  The service record shows the resolved input prefix, output prefix, exec AMI, and verification state.  The driver logs under the service case directory show staging, EC2 launch, S3 polling, artifact download, extraction, and verification failures.
