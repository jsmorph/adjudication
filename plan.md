# Core and Service Branch Plan

## Goal

The split should produce two maintained branches from the current common commit.  `carve` should contain the three adjudication procedures in `adc/`, `arb/`, and `arbd/`, together with repository metadata and the build files they require.  `service` should contain the multi-case Clerk services and the operational programs selected below, depending on installed core binaries through documented process and data interfaces.

Each core procedure should retain its governing Lean engine, proofs, a command-line execution path for one case, durable result records, certificate verification, tests, and current procedural documentation.  The service branch should retain only code required to start, supervise, expose, deploy, or inspect those procedure processes.  Experimental and historical material should enter neither branch unless a retained build or test requires it.

The extraction order should preserve and test service code on `service` before deleting its source from `carve`.  Each branch should build and test in its own worktree after every stage.  A paired compatibility test should then run a specified `service` commit against a specified `carve` commit.

## Findings

The repository tracks 1,376 files, of which 942 live under the three procedure directories.  The multi-case service packages contain 12,491 lines of Go, and `web/` adds 6,840 lines that consume those service APIs and run records.  The example trees occupy about 18 MiB, primarily because ARB commits source captures, PDFs, and saved web pages.

The multi-case service packages already have a narrow dependency on the one-case runtimes.  ADC's service package imports only the Go standard library, while ARB and AARD import their `runtime/proceeding` packages for `DefaultCouncilBackend` and `DefaultCaseAPIAddr`.  All three services otherwise launch procedure binaries, call private HTTP APIs, read result records, and serve stored artifacts.

That process boundary includes more than executable names.  A service depends on core subcommands and flags, stdout summary JSON, exit behavior, private health and Role API routes, artifact names, record schemas, event formats, and evidence manifests.  Extracting service code therefore requires a versioned compatibility specification and paired tests rather than source duplication.

Attested execution crosses the current core and service directories.  It adds each `case-packet` command and packet builder, Dockerfiles, `attest/`, attested-run scripts under `tools/`, runbooks, S3 fields, and service artifact routes.  ARB and AARD place their packet builders inside `runtime/proceeding`, while ADC uses `runtime/casepacket`.

The one-case Go runtimes implement substantive procedural behavior outside Lean.  They enforce opportunity deadlines and invalid-attempt limits, manage evidence bytes and visibility, assemble prompts, supervise role failures, write transcripts and event records, and create replay certificates.  The Lean executables enforce transitions and accept JSON on standard input, but they do not perform those runtime functions.

The word *Clerk* names two different components.  `adc/runtime/service` is a multi-case process manager with `/clerk/v1` routes, while the ADC Lean engine defines a procedural `clerk` actor that records service dates, configures a jury, adds jurors, and performs other court acts.  Removing the procedural actor would change ADC itself and therefore requires a separate decision from moving the multi-case service to `service`.

| Layer | `carve` destination | `service` destination |
| --- | --- | --- |
| Procedural state machines and proofs | Retain `adc/engine`, `arb/engine`, and `arbd/engine`. | Depend on built core executables and documented schemas. |
| One-case execution and records | Retain the approved `runner` or `proceeding` path, Lean clients, specifications, storage, reports, and certificate code. | Keep compatibility fixtures and clients, without copies of the procedure implementation. |
| Multi-case process management | Remove each `runtime/service` package and `service` subcommand after extraction. | Retain as standalone service packages and commands. |
| Service web applications | Remove `web/`. | Retain the service console, ARB management program, and run report. |
| Attested and cloud execution | Remove service-specific packet, Docker, S3, AMI, and attestation code after extraction. | Retain if D7 includes attested operation, with an explicit core artifact input. |
| Local participant launchers | Retain only if D1 selects an autonomous core run. | Otherwise retain if D7 includes managed local agents, after replacing Go imports of core procedure packages with the process interface. |
| MCP adapters and per-case Role APIs | Retain case-owned Role APIs if D1 keeps the one-case runtime. | Retain MCP adapters if D3 assigns participant transport to the operational branch. |
| Evals and experimental commands | Remove after preserving procedure assertions as ordinary tests. | Retain only tests that verify a selected service component. |
| Archives and research material | Remove `scratch/`, `skills/`, most source-capture examples, and historical analysis. | Exclude unless a service acceptance test requires a small fixture. |
| Separate verified MCP experiment | Remove `vmcp/`. | Exclude because it does not implement the current service adapters. |
| Shared code and data | Reduce to packages and inputs required by the approved one-case path. | Copy or reimplement only operational utilities selected by D7, then give them service-owned package paths. |

## Decisions Required Before Implementation

The first implementation review should resolve these questions and record the answers in the applicable development journals.  Several answers affect dependency direction, package ownership, and test design, so resolving them during deletion would create rework.  Each option below describes a coherent end state.

The user approved the following boundary on August 2, 2026.  These decisions govern the extraction unless later evidence requires another review.  Any change to them should be recorded here and in the applicable development journals before implementation continues.

| Decision | Approved boundary |
| --- | --- |
| D1 | Keep the one-case Go runtime and its command-line entry point on `carve`. |
| D2 | Move the multi-case Clerk services to `service` and retain ADC's procedural `clerk` actor on `carve`. |
| D3 | Keep case-owned HTTP Role APIs on `carve`; move MCP adapters, OpenClaw and Pi launchers, agent templates, and related operational support to `service`. |
| D4 | Keep a reduced `common/` on `carve` during extraction; give retained service utilities service-owned package paths and review final core placement after dependency reduction. |
| D5 | Keep the current durable adjudication records and certificate verification on `carve`; allow `service` to read those documented formats. |
| D6 | Use a process boundary: `service` launches installed core binaries and imports no core implementation package. |
| D7 | Retain multi-case services, web programs, MCP adapters, local agent launchers, attested execution, Docker deployment, agent templates, run reporting, and the support files required to operate or test them on `service`. |
| D8 | Record and test immutable `carve` and `service` commit pairs initially; add explicit API-version negotiation when an interface change requires it. |

### D1: Minimum Core Command-Line Execution Path

| Option | Retained behavior | Consequence |
| --- | --- | --- |
| Engine protocol | Keep each Lean executable and add or retain a thin JSON command-line driver for initialize, next opportunity, step, view where supported, and certificate replay. | This produces the smallest core.  The caller must manage state, evidence, role visibility outside the engine, deadlines, and records. |
| One-case runtime | Keep each current `case` process, its Role API, evidence handling, records, certificates, and deterministic runtime behavior. | This preserves Go-level procedure semantics.  Participants must use HTTP, an adapter, or a small command-line client. |
| Autonomous local run | Keep `case` plus `run`, MCP, OpenClaw launch, Pi launch, model pools, and participant templates. | This preserves the current one-command autonomous case.  It also retains container runtimes, credential handling, process supervision, model configuration, and most of `common/` on `carve`. |

### D2: Meaning of Clerk Removal

One option moves the multi-case Clerk services to `service` and preserves ADC's procedural `clerk` actor on `carve`.  The other option also removes or replaces the procedural actor, which requires new ADC rules for service dates, jury configuration, juror creation, and related actions.  The second option belongs in a separate procedure-design plan because it changes the ADC engine and proofs.

### D3: Participant Interface

If D1 retains the one-case runtime, the current HTTP Role APIs can remain as the case-owned participant boundary on `carve`.  MCP can move to `service` as an adapter over those APIs, or a command-line client can replace it for interactive and scripted use.  Local OpenClaw and Pi launchers form another independent choice because the Role APIs can operate without those launchers.

### D4: Core Shared Code Layout

Keeping a reduced `common/` avoids copying model request, provider client, and persona code.  Moving shared core code to a root `internal/` directory gives it an implementation-only name but leaves a fourth code directory.  Copying shared code into all three procedures produces three self-contained trees at the cost of duplication, while the engine-protocol choice in D1 may eliminate the shared runtime code altogether.

### D5: Required Core Records

The current one-case runtimes write state, events, transcripts, evidence manifests, summaries, and replay certificates.  A reduced packet could retain state, accepted actions, evidence metadata and bytes, terminal result, and certificate while deriving human-readable reports on demand.  This choice should identify which files constitute the durable adjudication record before report and storage code is divided between the branches.

### D6: Relationship Between the Branches

| Option | Structure | Consequence |
| --- | --- | --- |
| Process boundary | `service` contains operational code only and launches installed `adc`, `aar`, and `aard` binaries from a specified `carve` revision. | This matches the requested complementary split.  It requires stable CLI, HTTP, and artifact specifications but only small changes to the imports in the current multi-case service packages. |
| Go module dependency | `service` imports versioned Go packages published from `carve`. | This permits library calls but requires separate module identities, releases, and compatibility rules for two branches of one repository. |
| Overlay | `service` contains the entire core plus service additions. | This preserves current imports and builds.  The branch would duplicate the core and would not contain only service-related code. |

### D7: Operational Components That Should Survive

The multi-case services, their ordinary tests, and the service-facing web programs are the definite contents of `service`.  Attested execution, Docker deployment, MCP adapters, local OpenClaw and Pi launchers, agent templates, run reporting, and service-specific examples are separate candidates.  Approval should identify each retained candidate so that `service` does not become an archive of every file removed from `carve`.

### D8: Cross-Branch Versioning

One option records supported pairs of immutable `carve` and `service` commit IDs and tests each pair.  Another option adds explicit core and service API versions, rejects unsupported pairs at startup, and maintains a compatibility table.  Tags may identify tested releases under either option, but moving branch names should never define production compatibility by themselves.

## Branch Creation and Work Order

Both branches should begin at the current common source commit, recorded by exact object ID before any extraction.  If `plan.md` is committed first on `carve`, create `service` from the recorded pre-carve source commit rather than from the later planning commit.  Use separate worktrees for the two branches so that extraction, tests, and status checks remain isolated.

The recorded split base is `1f62a56f66da3a476a7f4064a86a580a2970fadc`.  Local branches `carve`, `main`, and `service` pointed to that commit when Stage 0 began.  Later compatibility records should use full commit IDs for both branches.

The completed service checkpoints are `4b4fa1751fa4b8a1e709b3f80ad1cbcbc6eaa581` for the multi-case services, `6eaed038b468add7099b77edb766b987ba053dcd` for the MCP adapters, `19b9254442e90c25c6cac21460d80eadb04ba7f3` for the ARB launcher, `25dac0e20c08ffa730a661eb4080677bd3bdfaa7` for the AARD launcher, `aaec158d94981e26e9979841b3f7f8ffca17e454` for the ADC launcher, and `48d19263fde43f010312cb446cd4d6970a019c4f` for the ARB and AARD cross-branch service tests.  Their service-owned package tests pass, and all three launcher checkpoints pass paired private-API tests against core binaries built from `carve`.  The cross-branch tests run the standalone ARB and AARD Clerk and MCP programs against those core binaries, so the corresponding service cases can now leave `carve`.

The first recorded compatibility pair is `service@48d19263fde43f010312cb446cd4d6970a019c4f` with `carve@e1e0c9d54783e04e30391d628c892507498007d4`.  The complete service compatibility suite passes against binaries built after `carve` removed the multi-case services, MCP adapters, local-agent launchers, and replay experiments.  The pair establishes the process boundary for the current interface version.

Every moved component should follow one order: preserve it on `service`, make it build there, add compatibility tests, and then remove it from `carve`.  Git history can recover deleted files, but a tested destination proves that the extracted component still works under its new ownership.  Each extraction commit on `service` should identify the corresponding removal commit on `carve` in its development notes.

## Implementation Stages

### 0. Establish the Branches, Approved Boundary, and Baseline

- [x] Record the exact current common commit as the split base.
- [x] Create `service` at that split base before any deletion commit reaches `carve`.
- [x] Create separate `carve` and `service` worktrees and verify their branch heads before extraction changes.
- [x] Resolve D1 through D8 and record the approved boundary in this plan.
- [x] Create a service-owned `devnotes.md` for references, decisions, corresponding extraction commits, and verification results.
- [x] Create a retention ledger that assigns every top-level directory and every command to `carve`, `service`, removal, or a named review.
- [x] Inventory the CLI flags, HTTP routes, output files, documentation, and tests in the approved cross-branch interface; schema details remain in Stage 1.
- [ ] Run the current Go test suites, the three Lean proof builds, and the three engine builds before extraction.
- [ ] Run TCP-dependent Go tests in an environment that permits loopback listeners.  The current restricted environment reports `socket: operation not permitted` in MCP, local-run, service, web, ACP, and xproxy tests, while the non-listener packages complete.
- [ ] Save one small input and expected terminal record for each procedure as the acceptance fixtures used by both branches.

### 1. Define the Core-to-Service Compatibility Specification

- [ ] Document the core executable names, required subcommands, flags, stdout summary schema, exit statuses, startup behavior, and signal handling used by service code.
- [ ] Document the private health and Role API routes, request and response schemas, wait behavior, authentication assumptions, and terminal result behavior.
- [ ] Document the durable artifact names and schemas consumed by the services and web programs, including run records, events, evidence manifests, transcripts, summaries, and certificates.
- [x] Replace ARB and AARD imports of `DefaultCouncilBackend` and `DefaultCaseAPIAddr` with service-owned configuration defaults or values obtained from the compatibility specification.
- [x] Preserve fake-core tests for service process management and add an opt-in paired test that checks real core command interfaces from the selected `carve` commit.
- [x] Apply D8 initially by recording the tested immutable pair `service@48d19263fde43f010312cb446cd4d6970a019c4f` and `carve@e1e0c9d54783e04e30391d628c892507498007d4`.  Add explicit version negotiation and a precise startup error when an interface change requires it.

### 2. Extract the Multi-Case Services

- [x] On `service`, move the ADC, ARB, and AARD service packages into service-owned package paths that import no procedure implementation package.
- [x] Add standalone `adc-service`, `aar-service`, and `aard-service` commands.
- [x] Preserve the remaining service variants from the core command black-box tests.  Service commit `48d19263fde43f010312cb446cd4d6970a019c4f` retains the ARB and AARD service and MCP variants as cross-branch tests.
- [x] Retain `web/` on `service`; its programs use the service HTTP APIs without importing service or procedure packages, and all web tests pass there.
- [ ] Verify all service packages with fake core binaries and then with built `adc`, `aar`, and `aard` binaries from `carve`.  The service package suite, all three paired launcher tests, and the ARB and AARD Clerk/MCP tests pass; a complete ADC Clerk/MCP case remains.
- [x] On `carve`, delete the three `runtime/service` packages and the three `service` subcommands after the extracted commands and paired tests pass.
- [x] Remove service variants from core black-box tests while preserving direct one-case tests for lawyer attempt exhaustion, lawyer deadline expiration, and runtime failure exit behavior.
- [ ] Remove Clerk routes, process registries, service artifact routes, and service examples from the `carve` documentation.

This stage should preserve the private listener owned by one running case if D1 selects the one-case runtime.  That listener carries participant opportunities and belongs to the core case process, while the public service may proxy it.  Naming in both branches should distinguish the case-owned Role API from the multi-case Clerk service.

### 3. Extract Attested and Deployment Execution

- [ ] If D7 retains attested operation, move the attested Python and shell programs, Docker definitions, S3 configuration, AMI and PCR handling, service routes, tests, and runbooks to `service`.
- [x] Keep deterministic case-packet construction in the core input interface.  Service invokes the installed `adc`, `aar`, or `aard` `case-packet` command so complaint and case-file selection continue to use the procedure implementation.
- [ ] Change service container builds to consume explicit core source or prebuilt artifacts from a pinned `carve` revision.  ARB now consumes full `CORE_COMMIT` and `SERVICE_COMMIT` values; ADC and AARD remain.
- [x] Verify one local packet build, one container build, and one attested-driver test before deleting the original files from `carve`.  ARB passed these checks at `service@dc7c61d61b478dd2bf24fdc7e1e4924d80b37443` against `carve@a4cc40d99899721d957c4f370040998306f771e9`.
- [ ] On `carve`, retain the core `case-packet` commands and delete Dockerfiles, `attest/`, attested tools, S3 settings, and attested runbooks after their service-owned replacements pass.  ARB is complete; ADC and AARD remain.
- [ ] Search both branches for stale source paths and implicit assumptions that service and core files share one checkout.

ARB attested execution moved to `service/attested/arb` in service commit `dc7c61d61b478dd2bf24fdc7e1e4924d80b37443`.  Its base image fetches full core and service commit IDs, verifies both checkouts, builds the installed core programs and service launcher separately, and copies only their runtime assets.  Docker produced image `sha256:47642fe2e73df0ce1d8c3d15b4e9b0f91996dbf284a8e3e06724fb16626c5d9a`, whose service entrypoint and installed core complaint validation both passed.

### 4. Assign Participant Adapters and Local Launchers

- [x] Move the three MCP adapter packages to service-owned paths and add standalone `adc-mcp`, `aar-mcp`, and `aard-mcp` commands.  The ARB and AARD adapters pass complete paired real-core cases; the corresponding ADC case remains pending.
- [x] Move the ARB local-agent launcher and templates to service-owned paths, replace its proceeding import with `aar case`, and pass its fake-core and paired real-core tests.
- [x] Move the AARD local-agent launcher and templates to service-owned paths, replace its proceeding import with `aard case`, and pass its fake-core and paired real-core tests.
- [x] Move the ADC local-agent launcher and templates to service-owned paths, replace its runner import with `adc case` or `adc scenario`, and pass its fake-core and paired real-core tests.
- [x] Apply D3 and D7 to MCP, OpenClaw, Pi, agent templates, local-run commands, and their credential and process support by assigning them to `service`.
- [x] Make the three service-owned launchers start a core case process and use its documented Role API without importing a core runner or proceeding package.
- [x] Preserve participant supervision, secret cleanup, tool-authority, failure, output-limit, fake-core, and paired real-core interface tests.
- [x] On `carve`, remove each adapter and launcher after its retained service replacement passes package and paired compatibility tests.
- [x] Remove autonomous local runs from `carve` under the approved one-case runtime boundary in D1.
- [ ] Verify one complete local case per procedure through the selected ownership model.

### 5. Prune the Service Branch and Remove Auxiliary Material

- [ ] On `service`, delete the Lean engines, proofs, one-case runner and proceeding implementations, core commands, core rules, and core examples after all selected operational components have service-owned locations.
- [ ] Retain only compatibility schemas, clients, and small fixtures needed to test service behavior against external core binaries.
- [ ] Use `go list -deps` to confirm that retained service packages do not import deleted procedure implementation packages under the process-boundary option.
- [ ] Delete `evals/` and the ADC runtime eval package from `carve` after moving procedure assertions into ordinary tests where needed.
- [ ] Delete ADC probe commands `eval`, `juror`, `llm`, and `pool`.  ARB's `council-replay` and `juror-replay` experiments have left `carve` because D7 assigned them no operational use.
- [ ] Delete `vmcp/`, `scratch/`, and `skills/` after moving current design rationale into the applicable manual or development journal.
- [ ] Remove `common/acp`, `common/xproxy`, and the `common/submodules/pi-acp` submodule unless a selected service component still uses one of them.
- [ ] Remove `.gitmodules` from each branch that no longer contains a submodule entry.
- [ ] Review `docs/`, `CHANGES.md`, analysis directories, engine review notes, generated theorem tables, latency data, model-pool data, and source captures against the retention ledger.

Admission to `service` should require a direct role in building, testing, operating, deploying, or inspecting the retained services.  Tests that assert state transitions, role authority, evidence custody, failure behavior, certificate replay, and output integrity belong with core code on `carve`.  Provider comparisons, prompt candidates, model clustering, archived observations, and unrelated experiments should leave both branches.

### 6. Reduce Each Core Procedure to the Approved One-Case Path

- [ ] Restrict the `carve` command dispatchers to the approved commands.  The expected minimum for a retained one-case runtime is `case`, input validation, and certificate verification, with `complain`, `scenario`, `mcp`, and `run` governed by D1 and D3.
- [ ] Preserve all runtime behavior that implements an approved procedural rule outside Lean, including evidence custody, visibility, deadlines, invalid-attempt accounting, role failure, and terminal record production.
- [ ] If D1 selects the engine protocol, specify and test a stable stdin, stdout, and exit-status interface before deleting the Go case runtimes.
- [ ] Make one complete case executable from the command line for each procedure using the saved acceptance fixtures.
- [ ] Run the service compatibility suite after every change to a command, private API, or retained record.
- [ ] Keep command names `adc`, `aar`, and `aard` unless a separate naming decision approves an interface change.

### 7. Divide Shared Code and Dependencies

- [ ] Use `go list` and import searches on each branch to identify the exact packages required by its retained commands.
- [ ] Apply D4 to the reduced core dependency set on `carve`.
- [ ] Give retained operational utilities service-owned package paths and remove their imports of core implementation packages.
- [ ] Remove unused persona corpora, provider inventories, Pi container files, tools, and configuration records from both branches.
- [ ] Run `go mod tidy` independently on both branches, inspect every remaining module, and document each third-party dependency.
- [ ] Review ADC's SQLite store and `pacer` command separately.  Preserve the store on `carve` if the approved durable record uses it, and assign any service-side record viewer through D7.

### 8. Reduce Documentation and Examples

- [ ] On `carve`, retain one small, redistributable acceptance example for each procedure and document build, test, proof, one-case execution, records, and certificate verification.
- [ ] On `service`, retain small service fixtures and document installation of compatible core binaries, configuration, operation, deployment, inspection, and version compatibility.
- [ ] Remove saved web pages, provider captures, large PDFs, duplicate scenarios, and run-specific observations from both branches.
- [ ] Retain the governing rules and proof documentation on `carve`.  Retain service API, deployment, and operating documentation on `service`.
- [ ] Keep the procedure development journals on `carve` and the service-owned `devnotes.md` on `service`, as required by `AGENTS.md`.
- [ ] Check every local Markdown link and command example on both branches.

### 9. Final Verification

- [ ] Build `adc`, `aar`, and `aard` from a clean `carve` checkout using the documented commands.
- [ ] Build all three Lean engines and all three proof trees on `carve`.
- [ ] Run all retained core Go tests and one command-line acceptance case per procedure.
- [ ] Build every retained service, adapter, deployment program, and web program from a clean `service` checkout.
- [ ] Run all retained service tests with fake core binaries.
- [ ] Install the selected `carve` binaries into the service test environment and run the paired compatibility suite.
- [ ] Verify service-created cases, proxied participant calls, terminal records, artifacts, evidence reads, cancellation, process reconciliation, and attested execution if retained.
- [ ] Use `go list -deps` to confirm that `carve` has no service package and `service` has no import of a core implementation package under the process-boundary option.
- [ ] Search both branches for deleted commands, stale package imports, obsolete paths, and broken examples.
- [ ] Run `git diff --check` and compare each branch's tracked-file inventory with the retention ledger.
- [ ] Record the tested `carve` and `service` commit IDs together.

## Completion Criteria

The split is complete when `carve` builds and verifies the three procedures, and each procedure can complete one case through its documented command-line path.  `service` must build its selected operational programs under the approved D6 relationship, and it must pass its tests against a recorded `carve` revision.  Every remaining directory and third-party dependency on either branch must have an assigned role in the approved core or service path.
