# Core Process Interface

## Scope

This document defines the interface by which operational services execute and inspect the core ADC, ARB, and AARD procedures.  Core owns each case's procedural state, participant opportunities, evidence custody, durable record, and terminal result.  Service owns multi-case admission, process supervision, public routing, deployment, and record presentation.

The initial interface version is tied to the split base `1f62a56f66da3a476a7f4064a86a580a2970fadc`.  Compatibility records identify a tested `carve` commit and a tested `service` commit.  An interface change requires paired tests and an update to this document before either branch depends on the new behavior.

## Executables and Process Behavior

Service invokes installed `adc`, `aar`, and `aard` executables.  Each invocation receives an explicit output directory and, for a live participant API, an explicit loopback listen address chosen by service.  Service captures standard output and standard error in the case output directory, sets an explicit working directory when the core installation still resolves resource defaults there, and supervises the process until exit.

A core process returns a nonzero exit status for startup, configuration, input, engine, storage, or other process failures.  A procedure that records an opportunity failure may return zero after writing a terminal failed case record.  The service parses the last nonempty JSON object on standard output as the process summary and reconciles the final status from `run.json`.

| Procedure | Direct one-case invocation | Required service-facing flags |
| --- | --- | --- |
| ADC complaint | `adc case` | `--complaint`, `--out-dir`, `--case-id`, `--run-id`, `--caseapi-addr`, and requested runtime overrides. |
| ADC scenario | `adc scenario` | `--scenario`, `--output`, `--runtime`, `--events`, `--db`, `--transcript`, `--digest`, `--allow-assertion-failures`, `--case-id`, `--run-id`, `--caseapi-addr`, and requested runtime or report overrides. |
| ARB | `aar case` | `--case-id`, `--run-id`, `--complaint`, `--out-dir`, `--caseapi-addr`, `--council-backend`, and any requested policy or runtime override. |
| AARD | `aard case` | `--case-id`, `--run-id`, `--complaint`, `--out-dir`, `--caseapi-addr`, `--council-backend`, and any requested policy or runtime override. |

The service-owned `adc-run`, `aar-run`, and `aard-run` commands start a direct core case through this interface and use the corresponding service-owned MCP adapter.  `adc-run` selects `adc case` for a complaint and `adc scenario` for a prepared scenario.  Each launcher preserves the complete core `run.json` object, records core standard streams beneath `logs/`, and rejects a result file that the new process did not replace.

The core branch retains `validate`, `verify-certificate`, and deterministic `case-packet` construction for operator and service use.  Attested drivers live on service, invoke the installed core packet command, and identify the exact core source or artifacts placed in a workload image.  This keeps complaint and case-file selection under the procedure that later validates and runs those inputs.

## Private Case APIs

Service may reach a private case API only through its configured loopback address.  HTTP 204 from `/health` marks a child ready for participant traffic.  A direct-case startup-health timeout or direct-case record persistence failure marks the case failed and stops its attached child process.

Service may proxy the procedure-specific Role API without interpreting or changing procedural requests and responses.  A direct-case cancellation request records the transition before signaling the child.  A direct-case persistence, interrupt, or kill failure produces an error response and a failed in-memory service record.

| Procedure | Paths owned by core |
| --- | --- |
| ADC | `/health`; `/roleapi/v1/get`; `/roleapi/v1/wait_for_opportunity`; `/roleapi/v1/status`; `/roleapi/v1/result`; `/roleapi/v1/do`; `/roleapi/v1/fail`. |
| ARB | `/health`; `/lawyerapi/v1/get`; `/lawyerapi/v1/wait`; `/lawyerapi/v1/status`; `/lawyerapi/v1/result`; `/lawyerapi/v1/do`; `/councilapi/v1/get`; `/councilapi/v1/wait`; `/councilapi/v1/do`; `/councilapi/v1/fail`. |
| AARD | `/health`; `/lawyerapi/v1/get`; `/lawyerapi/v1/wait`; `/lawyerapi/v1/status`; `/lawyerapi/v1/result`; `/lawyerapi/v1/do`; `/councilapi/v1/get`; `/councilapi/v1/wait`; `/councilapi/v1/do`; `/councilapi/v1/fail`. |

Core validates case identifiers, principal identifiers, opportunity identifiers, legal tool calls, attempts, deadlines, file visibility, and evidence access.  Service selects a case process and forwards bytes, status, and relevant HTTP headers.  MCP adapters translate MCP requests to these APIs but hold no procedural state.

## Durable Record

Core writes the durable adjudication record beneath the selected output directory.  Service may list, read, range-serve, and render documented files without changing them.  The certificate verifier on core remains the authority for replaying accepted actions and comparing the replayed terminal state with the recorded state.

| File or directory | Owner and use |
| --- | --- |
| `run.json` | Core terminal result and run metadata consumed by service status reconciliation. |
| `state.json` | Core terminal state consumed by verification and reporting. |
| `certificate.json` | Core accepted-action replay certificate. |
| `events.ndjson` | Core append-only case event stream used for monitoring. |
| `work-notes.ndjson` | Core off-record participant work notes when the procedure enables them. |
| `evidence-manifest.json` and `evidence-store/` | Core evidence identifiers, metadata, hashes, and stored bytes. |
| `transcript.md` and `digest.md` | Core human-readable record and summary. |
| `runtime.json` and `run.db` | ADC runtime configuration and database when the selected ADC path writes them. |
| `local-run.json` | Service-owned local-agent orchestration record after launcher extraction. |
| `service-logs/` and `clerk.json` | Service-owned process logs and multi-case record. |

A service must treat an unreadable or missing `run.json` after process exit as a failed or incomplete execution.  It may reconcile a detached service record from a readable terminal `run.json`.  Artifact access must confine paths to the recorded output directory and expose only the service's explicit allowlist.

## Compatibility Verification

Service unit tests use fake core executables to verify argument construction, startup, failure, process cleanup, record reconciliation, proxying, and artifact access.  Paired tests use built core executables from a specified `carve` commit to verify command help, required flags, private API startup, one direct case per procedure, and terminal record consumption.  Release notes record the two full commit IDs and the compatibility test result.

The `service/compat/adc`, `service/compat/arb`, and `service/compat/arbd` packages start the standalone Clerk and MCP executables against selected core binaries.  The ADC package completes a bench case with external parties, an internal judge, digest generation, terminal record reconciliation, and certificate replay.  The ARB and AARD packages cover participant failures, deadlines, complete MCP cases, terminal records, and service reconciliation.  All three packages accept explicit service binary, core binary, and core checkout paths through test flags.

The tested code pair `service@46b2d7c92ebf6a82ae1ea3d6d7eaabd170d15952` and `carve@0c4162fcd985fa0888893f1e25088e9600bdb207` passes the complete compatibility suite.  The service revision requires a readable terminal `run.json`, passes requested ADC report settings through prepared-scenario paths, and contains no copied procedure source.  The selected core revision builds ADC, ARB, and AARD with Lean 4.32.0.  This pair tests the command, private HTTP, and artifact boundary after the branch split and service pruning.

Changes to command names, required flags, private routes, request or response fields used by service, exit behavior, or record names require coordinated edits.  Additive fields remain acceptable when existing meanings and required fields remain unchanged.  Removing or changing an interface element requires a new compatibility decision and a paired update.
