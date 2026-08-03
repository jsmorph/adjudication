# Development Notes

## 2026-08-02: Lean 4.32.0

### Decision

The service branch's temporary core copies and the three attested image build stages now select Lean 4.32.0.  The proof revisions match `carve@e887cc3e0379b5a3eb9892a4183b6e6259d75305`, including the explicit reductions required by Lean 4.32.0's default `do` elaborator.  Each image build stage installs the same Lean release selected by the core checkout it compiles.

### Verification

- [x] `lean --version` reports Lean 4.32.0 in the ADC, ARB, AARD, and VMCP projects.
- [x] `lake build` completes all four project builds.
- [x] Every active Lean toolchain and attested image build definition names Lean 4.32.0.

## 2026-08-02: Service-owned shared code

### Decision

The model-request parser now lives at `service/modelrequest`, and all three local launchers import that service-owned package.  The Pi image recipe now lives at `service/pi-container`, beside the programs that require the image for juror and council agents.  Its retained files build the image directly, while the removed wrapper scripts had no caller and one required a `pi-acp` executable absent from the image.

### Verification

- [x] `go test -buildvcs=false -count=1 ./service/... ./cmd/... ./web/...`
- [x] `go list -buildvcs=false -deps ./service/... ./cmd/... ./web/...` lists no package under `adjudication/common`.
- [x] `bash -n service/pi-container/build-image.sh`

## 2026-08-02: Core and service branch split

### Split base

The `service` branch began at commit `1f62a56f66da3a476a7f4064a86a580a2970fadc`, shared with `carve` and `main` when extraction started.  It will retain operational code that starts, supervises, exposes, deploys, or inspects ADC, ARB, and AARD processes.  It will remove the Lean engines, proofs, one-case runtime implementations, core commands, procedural rules, and core examples after the retained services depend only on documented process and data interfaces.

### Approved boundary

The service branch will own the multi-case Clerk services, web programs, MCP adapters, local OpenClaw and Pi launchers, agent templates, attested execution, Docker deployment, run reporting, and their required support files.  Installed `adc`, `aar`, and `aard` binaries remain the procedure owners, including their case-owned HTTP Role APIs and durable records.  Compatibility will use tested pairs of immutable `carve` and `service` commit IDs until an interface change requires explicit version negotiation.

### Case-packet ownership

Deterministic case-packet construction remains in the `carve` commands because each builder uses procedure-owned complaint or case-file selection.  Attested drivers on `service` will invoke the installed `adc`, `aar`, or `aard` `case-packet` command through the process interface.  Service will retain packet transport, S3 staging, archive verification, container extraction, and attestation handling.

### Multi-case service extraction

The ADC, ARB, and AARD multi-case packages now have service-owned paths at `service/adc`, `service/arb`, and `service/arbd`.  The `adc-service`, `aar-service`, and `aard-service` commands start those packages without importing a procedure implementation package.  ARB and AARD now keep their process defaults inside the service packages, removing the two remaining imports of their core proceeding packages.

The existing service tests use fake core programs for process arguments, readiness, proxying, records, artifacts, evidence, attested execution, and failure handling.  An opt-in compatibility test uses `-carve-bin-dir` to inspect fresh `adc`, `aar`, and `aard` binaries and verify the direct command flags and required-input failures consumed by service.  The corresponding carve removal remains pending until the service checkpoint has a commit ID and the carve commands no longer dispatch the moved packages.

### Verification

- [x] `go test -buildvcs=false ./service/... ./cmd/...`
- [x] `go test -buildvcs=false -count=1 ./service/compat -args -carve-bin-dir=/tmp/carve-core-bins`
- [x] `go list -buildvcs=false -f '{{.ImportPath}}: {{join .Imports " "}}' ./service/... ./cmd/...`
- [x] Import search found no `adjudication/adc/runtime`, `adjudication/arb/runtime`, or `adjudication/arbd/runtime` import in `service/` or `cmd/`.

### MCP adapter extraction

The three MCP adapter packages now live at `service/mcp/adc`, `service/mcp/arb`, and `service/mcp/arbd`.  Standalone `adc-mcp`, `aar-mcp`, and `aard-mcp` commands preserve the existing adapter flags and pass cancellation from interrupt and termination signals.  The moved packages import only the Go standard library and communicate with a core case through its HTTP API.

The adapter package tests pass in an environment that permits loopback listeners.  Those tests cover MCP initialization, sessions, authentication, origins, tool schemas, case API forwarding, wait behavior, errors, and session expiry.  Carve retains its MCP dispatch entries until a paired test runs the service-owned commands against real core case processes.

### MCP verification

- [x] `go test -buildvcs=false ./service/mcp/... ./cmd/adc-mcp ./cmd/aar-mcp ./cmd/aard-mcp`

### ARB local launcher extraction

The ARB local-agent launcher now lives at `service/localrun/arb`, with `aar-run` as its standalone command.  It starts an installed `aar case` process, waits for the private case API, and uses the service-owned ARB MCP package.  The launcher imports no ARB implementation package and preserves the core `run.json` object when it writes its command result.

The launcher embeds its three default agent templates while preserving file-path overrides.  It passes every core case input through explicit command flags, accepts an explicit core working directory, records core output under `logs/`, and rejects a stale `run.json` left in a reused output directory.  The ARB multi-case service now invokes `aar-run` for Clerk local-agent requests and reserves `aar` for direct core cases.

The paired test starts the real `aar` binary and Lean engine from carve, performs council preflight against a local fake provider, waits for `/health`, and reads the Lawyer API status route.  Cancellation then stops the core child and verifies that the launcher observes its exit.  The paired test uses `CARVE_BIN_DIR` and `CARVE_ROOT` to identify the tested core checkout.

### ARB launcher verification

- [x] `CARVE_BIN_DIR=/tmp/carve-core-bins CARVE_ROOT=/media/hd2/src/adjudication-clones/adjudication-1 go test -buildvcs=false -count=1 ./service/arb ./service/localrun/arb ./cmd/aar-service ./cmd/aar-run`
- [x] Import search found no `adjudication/arb/runtime` import in `service/localrun/arb` or `cmd/aar-run`.

### AARD local launcher extraction

The AARD local-agent launcher now lives at `service/localrun/arbd`, with `aard-run` as its standalone command.  It starts an installed `aard case` process, waits for the private case API, and uses the service-owned AARD MCP package.  The launcher imports no AARD implementation package and preserves the complete core `run.json` object in its command result.

The launcher embeds its three default agent templates while preserving file-path overrides.  It passes the judgment standard and every other core case input through explicit command flags, accepts an explicit core working directory, records core output under `logs/`, and rejects a stale `run.json`.  The AARD multi-case service now invokes `aard-run` for Clerk local-agent requests and reserves `aard` for direct core cases.

The paired test starts the real `aard` binary and Lean engine from carve, performs council preflight against a local fake provider, waits for `/health`, and reads the Lawyer API status route.  Cancellation stops the core child and verifies that the launcher observes its exit.  Test flags identify the paired executable directory and carve checkout while retaining the reusable `go test` command prefix.

### AARD launcher verification

- [x] `go test -buildvcs=false -count=1 ./service/arbd ./service/localrun/arbd ./cmd/aard-service ./cmd/aard-run`
- [x] `go test -buildvcs=false -count=1 -run '^TestPairedCoreCaseAPI$' ./service/localrun/arbd -args -carve-bin-dir=/tmp/carve-core-bins -carve-root=/media/hd2/src/adjudication-clones/adjudication-1`
- [x] Import search found no `adjudication/arbd/runtime` import in `service/localrun/arbd` or `cmd/aard-run`.

### ADC local launcher extraction

The ADC local-agent launcher now lives at `service/localrun/adc`, with `adc-run` as its standalone command.  It starts `adc case` for a complaint or `adc scenario` for a prepared scenario, waits for the private Role API, and uses the service-owned ADC MCP package.  The launcher imports no ADC implementation package and preserves the complete core `run.json` object in its command result.

The launcher embeds its three default agent templates while preserving file-path overrides.  It passes complaint preparation, jury policy, runtime, report, and external-role inputs through explicit command flags, accepts an explicit core working directory, records core output under `logs/`, and rejects a stale `run.json`.  The ADC multi-case service now invokes `adc-run` for Clerk local-agent requests and reserves `adc` for direct core cases.

The paired test starts the real `adc` binary and Lean engine from carve, waits for `/health`, and reads the Role API status route while an external plaintiff opportunity remains open.  Cancellation stops the core child and verifies that the launcher observes its exit.  Test flags identify the paired executable directory and carve checkout while retaining the reusable `go test` command prefix.

### ADC launcher verification

- [x] `go test -buildvcs=false -count=1 ./service/adc ./service/localrun/adc ./cmd/adc-service ./cmd/adc-run`
- [x] `go test -buildvcs=false -count=1 -run '^TestPairedCoreCaseAPI$' ./service/localrun/adc -args -carve-bin-dir=/tmp/carve-core-bins -carve-root=/media/hd2/src/adjudication-clones/adjudication-1`
- [x] `go test -buildvcs=false -count=1 ./service/... ./cmd/...`
- [x] Import search found no `adjudication/adc/runtime` import in `service/localrun/adc`, `service/adc`, `cmd/adc-run`, or `cmd/adc-service`.

### Cross-branch service compatibility

The ARB and AARD service cases from the combined core command black-box tests now live under `service/compat/arb` and `service/compat/arbd`.  They start the standalone service and MCP executables, and each service starts the selected `carve` core executable with explicit working-directory and engine paths.  The direct-core cases remain on `carve`, where they test procedure behavior without the Clerk or MCP layers.

The service cases verify lawyer attempt exhaustion, lawyer deadlines, council-member attempt exhaustion, council-member deadlines, service status reconciliation, terminal result proxying, and recorded events.  The MCP cases complete the lawyer and council phases through the service-owned adapters, verify tool authority, read evidence, record work notes, and inspect terminal results.  ARB and AARD both pass these tests against the current `carve` executables and Lean engines.

The compatibility packages accept `-service-bin-dir`, `-carve-bin-dir`, and `-carve-root`, allowing one `go test` command to run every package.  The test packages import only the Go standard library and communicate with service and core through processes and HTTP.  The tests report process cleanup, HTTP body closure, fake-provider I/O, and retained-fixture log errors.

Service commit `48d19263fde43f010312cb446cd4d6970a019c4f` passes the complete compatibility suite against carve commit `e1e0c9d54783e04e30391d628c892507498007d4`.  That carve revision excludes the multi-case services, MCP adapters, local-agent launchers, and their combined command entries.  The passing pair confirms that the retained service programs use the installed core commands and private case APIs after those removals.

### Cross-branch verification

- [x] `go build -buildvcs=false -o /tmp/service-bins/aar-service ./cmd/aar-service`
- [x] `go build -buildvcs=false -o /tmp/service-bins/aard-service ./cmd/aard-service`
- [x] `go build -buildvcs=false -o /tmp/service-bins/aar-mcp ./cmd/aar-mcp`
- [x] `go build -buildvcs=false -o /tmp/service-bins/aard-mcp ./cmd/aard-mcp`
- [x] `go test -buildvcs=false -count=1 ./service/compat/... -args -service-bin-dir=/tmp/service-bins -carve-bin-dir=/tmp/carve-core-bins -carve-root=/media/hd2/src/adjudication-clones/adjudication-1`
- [x] `go test -buildvcs=false -count=1 ./service/compat/... -args -service-bin-dir=/tmp/service-bins -carve-bin-dir=/tmp/carve-core-only-bins -carve-root=/media/hd2/src/adjudication-clones/adjudication-1`
- [x] `go list` found no core implementation import in the three compatibility packages.

### ARB attested execution extraction

The ARB attested image, exec entrypoint, local driver, exec scripts, and runbooks now live under `service/attested/arb`.  The base image fetches and verifies full `CORE_COMMIT` and `SERVICE_COMMIT` values, builds `aar` and `aarengine` from core, and builds `aar-run` from service.  Its runtime filesystem contains the installed programs and required core data rather than a complete source checkout.

The local driver invokes the installed `aar case-packet` command for complaint-based runs.  `aar-service` passes its configured core executable path to that driver, and the driver records the path in `run.env`.  The exec workload starts the service-owned `aar-run` launcher with explicit paths to the installed core executable, engine, working directory, and common-data root.

The example wrapper accepts a core example directory and calls the sibling service-owned driver.  The runbook specifies a repository-root Docker build context and full core and service commit IDs.  It retains the AMI, PCR, S3, secret, artifact, and verification procedures required to operate the attested service.

The base image build passed for `service@dc7c61d61b478dd2bf24fdc7e1e4924d80b37443` and `carve@a4cc40d99899721d957c4f370040998306f771e9`.  Docker produced image `sha256:47642fe2e73df0ce1d8c3d15b4e9b0f91996dbf284a8e3e06724fb16626c5d9a`.  The image displayed the `aar-run` help through its service entrypoint and validated the embedded `examples/ex01/complaint.md` through `/opt/core/arb/.bin/aar`.

### ARB attested verification

- [x] `go test -buildvcs=false -count=1 ./service/arb ./cmd/aar-service`
- [x] `python3 -m unittest service/attested/arb/run_arb_attested_test.py`
- [x] `python3 -m py_compile service/attested/arb/run-arb-attested.py service/attested/arb/run_arb_attested_test.py`
- [x] `sh -n` passed for the POSIX shell programs, and `bash -n` passed for `run-one-attested-arb.sh`.
- [x] `go vet ./service/... ./cmd/... ./web/...`
- [x] All retained packages passed during `go test -buildvcs=false -count=1 ./...`.  The command failed only while loading obsolete core dispatchers that still import the already-extracted service and MCP package paths; Stage 5 deletes those dispatchers from this branch.
- [x] Build the base image from exact service and core commits, inspect its entrypoint and working directory, display `aar-run --help`, and validate an embedded complaint through the installed core executable.

### AARD attested execution extraction

The AARD attested image, exec entrypoint, local driver, exec scripts, and runbooks now live under `service/attested/arbd`.  The base image fetches and verifies full `CORE_COMMIT` and `SERVICE_COMMIT` values, builds `aard` and `aardengine` from core, and builds `aard-run` from service.  Its runtime filesystem contains the installed programs and required core data.

The local driver invokes the installed `aard case-packet` command for complaint-based runs.  `aard-service` passes its configured core executable path to that driver, and the driver records the path in `run.env`.  The exec workload starts the service-owned `aard-run` launcher with explicit paths to the installed core executable, engine, working directory, and common-data root.

The example wrapper accepts a core example directory and calls the sibling service-owned driver.  The runbook specifies a repository-root Docker build context and full core and service commit IDs.  It retains the AMI, PCR, S3, secret, artifact, and verification procedures required to operate the attested service.

### AARD attested verification

- [x] `go test -buildvcs=false -count=1 ./service/arbd ./cmd/aard-service`
- [x] `python3 -B -m unittest service/attested/arbd/run_arbd_attested_test.py`
- [x] `sh -n` passed for the POSIX shell programs, and `bash -n` passed for `run-one-attested-arbd.sh`.
- [x] `go vet ./service/arbd ./cmd/aard-service ./cmd/aard-run`
- [x] `go build -buildvcs=false -o /tmp/service-aard-run ./cmd/aard-run`
- [x] Build the base image from exact service and core commits, inspect its entrypoint and working directory, display `aard-run --help`, and validate an embedded complaint through the installed core executable.

The first exact-commit image build found an obsolete `arbd/pool.jsonl` copy in the extracted Dockerfile.  The selected core commit stores the default council pool at `common/data/personas/pool.jsonl`, and the image already copies the complete `common/data` and `common/etc` trees.  Removing the nonexistent source path preserves the runtime lookup under the explicit `/opt/core/common` root.

The corrected base image build passed for `service@5bf19d083ea670cdbf767ccf304c81ec712f90d4` and `carve@489cd9ecdb46f41f036d825fc9f5221f68c13c1a`.  Docker produced image `sha256:a35e3e6bdd8090f890ab3cdf9d877fbcc758670cce1b72b5ad25c56243d83264` with entrypoint `/usr/local/bin/aard-run-entrypoint` and working directory `/opt/core/arbd`.  The image displayed `aard-run` help and validated `examples/ex1/complaint.md` through `/opt/core/arbd/.bin/aard`.

### ADC attested execution extraction

The ADC attested image, exec entrypoint, local driver, exec scripts, and runbooks now live under `service/attested/adc`.  The base image fetches and verifies full `CORE_COMMIT` and `SERVICE_COMMIT` values, builds `adc` and `adcengine` from core, and builds `adc-run` from service.  Its runtime filesystem contains the installed programs, ADC court profiles, shared core data, the Docker CLI, and the embedded Pi juror root filesystem.

The local driver invokes the installed `adc case-packet` command for complaint-based runs.  `adc-service` passes its configured core executable path to that driver, and the driver records the path in `run.env`.  The exec workload starts the service-owned `adc-run` launcher with explicit paths to the installed core executable, engine, and working directory.

The one-complaint helper calls the sibling service-owned driver and stores output under the service checkout.  The runbook specifies a repository-root Docker build context and full core and service commit IDs.  It retains the AMI, PCR, S3, secret, artifact, and verification procedures required to operate the attested service.

### ADC attested verification

- [x] `go test -buildvcs=false -count=1 ./service/adc ./cmd/adc-service ./cmd/adc-run`
- [x] `python3 -B -m unittest service/attested/adc/run_adc_attested_test.py`
- [x] `sh -n` passed for the POSIX shell programs, and `bash -n` passed for `run-one-attested-adc.sh`.
- [x] `go vet ./service/adc ./cmd/adc-service ./cmd/adc-run`
- [x] `go build -buildvcs=false -o /tmp/service-adc-run ./cmd/adc-run`
- [x] Build the base image from exact service and core commits, inspect its entrypoint and working directory, display `adc-run --help`, and build a packet from a mounted complaint through the installed core executable.

The base image build passed for `service@58bd12061e604cca551ddcebcf9e76e46dea3098` and `carve@755246b50d0726dfc8dce9faf6a852b3a31f8b18`.  Docker produced image `sha256:89b6e85a6de9525bc8402e82b14ecc0fabe9102f4bd38e166819a28059cae938` with entrypoint `/usr/local/bin/adc-run-entrypoint` and working directory `/opt/core/adc`.  The image displayed `adc-run` help and built a deterministic complaint packet through `/opt/core/adc/.bin/adc`.
