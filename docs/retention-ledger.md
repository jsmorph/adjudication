# Retention Ledger

## Use

This ledger assigns the current repository contents during extraction.  “Carve” and “Service” identify the final owner approved in the branch plan, while “Remove” identifies material that will leave both branches.  “Review” marks an unresolved ownership question already named in the plan and does not authorize deletion.

A component can remain temporarily on both branches while its replacement and compatibility tests are incomplete.  The service branch may retain core source during extraction, and the carve branch may retain operational source until the service copy passes.  Each temporary copy leaves its source branch only after the destination checkpoint succeeds.

## Top-Level Contents

| Current path | Final disposition | Extraction condition |
| --- | --- | --- |
| `adc/` | Carve keeps the engine, proofs, one-case runtime, Role API, records, verifier, rules, and small acceptance fixture.  Service receives selected operational ADC code under service-owned paths. | Remove each operational copy from carve after its service replacement passes; remove core ADC source from service after all retained consumers use the process interface. |
| `arb/` | Carve keeps the engine, proofs, one-case runtime, Lawyer and Council APIs, records, verifier, rules, and small acceptance fixture.  Service receives selected operational ARB code under service-owned paths. | Apply the same destination-first sequence used for ADC. |
| `arbd/` | Carve keeps the engine, proofs, one-case runtime, Lawyer and Council APIs, records, verifier, rules, and small acceptance fixture.  Service receives selected operational AARD code under service-owned paths. | Apply the same destination-first sequence used for ADC. |
| `common/` | Split by package dependency. | Keep core packages on carve, move operational packages and data to service-owned paths, then remove unused ACP, xproxy, submodule, persona, container, and tool material. |
| `docs/` | Split by subject. | Keep procedure and proof documents on carve; keep service interface, operation, deployment, and compatibility documents on service; remove obsolete repository-wide notes. |
| `evals/` | Remove after preserving required procedure assertions as ordinary core tests. | Review every retained assertion before deleting its fixture or scorer. |
| `scratch/` | Remove. | Move current design rationale into a manual or development journal before deletion. |
| `skills/` | Remove. | Preserve any current proof rationale in the applicable procedure documents before deletion. |
| `vmcp/` | Remove. | The retained MCP adapters use the procedure Role APIs rather than this separate experiment. |
| `web/` | Service. | Update imports to service-owned packages and test all three web commands before removing the carve copy. |
| `README.md`, `CHANGES.md`, and `docs/README.md` | Rewrite separately on each branch. | Complete after the retained command and directory sets stabilize. |
| `go.mod` and `go.sum` | Retain independently on each branch. | Run `go mod tidy` only after package extraction and inspect every dependency change. |
| `.gitmodules` and `common/submodules/pi-acp` | Service while a retained launcher requires Pi ACP; otherwise remove. | Decide from the final launcher dependency graph. |
| `AGENTS.md`, `.gitignore`, `LICENSE`, and `NOTICES.md` | Retain on both branches, with branch-specific ignore rules where required. | Review at final inventory. |
| `example.sh` | Service if it becomes a small service acceptance example; otherwise remove. | Replace its dependency on `aar run` before retention. |

## Procedure Commands

| Current command | Final disposition | Required replacement or review |
| --- | --- | --- |
| `adc case` | Carve. | Preserve complaint preparation, one-case execution, Role API startup, durable records, and JSON summary behavior. |
| `adc scenario` | Carve. | Preserve direct execution of a prepared scenario because the extracted service currently uses this path. |
| `adc validate` and `adc verify-certificate` | Carve. | Retain as command-line validation and replay tools. |
| `adc run` | Service. | Moved to `adc-run` at service commit `aaec158d94981e26e9979841b3f7f8ffca17e454`. |
| `adc mcp` and `adc service` | Service. | Moved at service commits `6eaed038b468add7099b77edb766b987ba053dcd` and `4b4fa1751fa4b8a1e709b3f80ad1cbcbc6eaa581`. |
| `adc case-packet` | Carve. | Retain deterministic complaint and case-file selection as the service-facing core input interface. |
| `adc complain` and `adc pacer` | Carve. | Retain complaint drafting for the acceptance path and PACER-style inspection of the approved `run.db` record. |
| `adc eval`, `adc juror`, `adc llm`, and `adc pool` | Remove after preserving required assertions. | Keep no experimental command solely as an archive. |
| `aar case` | Carve. | Preserve one-case execution, Lawyer and Council APIs, durable records, and JSON summary behavior. |
| `aar validate` and `aar verify-certificate` | Carve. | Retain as command-line validation and replay tools. |
| `aar run` | Service. | Moved to `aar-run` at service commit `19b9254442e90c25c6cac21460d80eadb04ba7f3`. |
| `aar mcp` and `aar service` | Service. | Moved at service commits `6eaed038b468add7099b77edb766b987ba053dcd` and `4b4fa1751fa4b8a1e709b3f80ad1cbcbc6eaa581`. |
| `aar case-packet` | Carve. | Retain deterministic complaint and case-file selection as the service-facing core input interface. |
| `aar complain` | Carve. | Retain complaint drafting as a core input-preparation command. |
| `aar council-replay` and `aar juror-replay` | Remove unless a selected service acceptance test requires a defined operational use. | Preserve procedure assertions as ordinary tests. |
| `aard case` | Carve. | Preserve one-case execution, Lawyer and Council APIs, durable records, and JSON summary behavior. |
| `aard validate` and `aard verify-certificate` | Carve. | Retain as command-line validation and replay tools. |
| `aard run` | Service. | Moved to `aard-run` at service commit `25dac0e20c08ffa730a661eb4080677bd3bdfaa7`. |
| `aard mcp` and `aard service` | Service. | Moved at service commits `6eaed038b468add7099b77edb766b987ba053dcd` and `4b4fa1751fa4b8a1e709b3f80ad1cbcbc6eaa581`. |
| `aard case-packet` | Carve. | Retain deterministic complaint and case-file selection as the service-facing core input interface. |
| `aard complain` | Carve. | Retain complaint drafting as a core input-preparation command. |

## Operational Programs

| Current program group | Final disposition | Extraction condition |
| --- | --- | --- |
| `web/cmd/adjudication-web`, `adjudication-manage`, and `adjudication-report` | Service. | Update imports and tests after the three service packages have stable service-owned paths. |
| Procedure attested drivers, entrypoints, Dockerfiles, and attested run scripts | Service. | Consume a pinned core artifact or source revision and pass packet, container, and driver tests. |
| `common/pi-container` and local OpenClaw or Pi instruction templates | Service when required by retained launchers. | Refactor launchers to the process and Role API boundary before pruning common code. |
| `common/tools/gendiagram.sh`, `gentheorems.py`, and `proofstats.sh` | Carve. | Maintain the retained diagrams, theorem catalogs, and proof statistics. |
| `common/tools/llm_graph.py` and model-pool programs | Remove. | Preserve no provider experiment without a retained service acceptance role. |
| Procedure `tools/run-*.sh` wrappers | Split by behavior. | Keep small core acceptance wrappers on carve and move deployment or local-agent wrappers to service. |
