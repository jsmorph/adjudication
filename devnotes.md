# Development Notes

## 2026-08-02: Core and service branch split

### Split base

The `service` branch began at commit `1f62a56f66da3a476a7f4064a86a580a2970fadc`, shared with `carve` and `main` when extraction started.  It will retain operational code that starts, supervises, exposes, deploys, or inspects ADC, ARB, and AARD processes.  It will remove the Lean engines, proofs, one-case runtime implementations, core commands, procedural rules, and core examples after the retained services depend only on documented process and data interfaces.

### Approved boundary

The service branch will own the multi-case Clerk services, web programs, MCP adapters, local OpenClaw and Pi launchers, agent templates, attested execution, Docker deployment, run reporting, and their required support files.  Installed `adc`, `aar`, and `aard` binaries remain the procedure owners, including their case-owned HTTP Role APIs and durable records.  Compatibility will use tested pairs of immutable `carve` and `service` commit IDs until an interface change requires explicit version negotiation.

### Multi-case service extraction

The ADC, ARB, and AARD multi-case packages now have service-owned paths at `service/adc`, `service/arb`, and `service/arbd`.  The `adc-service`, `aar-service`, and `aard-service` commands start those packages without importing a procedure implementation package.  ARB and AARD now keep their process defaults inside the service packages, removing the two remaining imports of their core proceeding packages.

The existing service tests use fake core programs for process arguments, readiness, proxying, records, artifacts, evidence, attested execution, and failure handling.  An opt-in compatibility test uses `CARVE_BIN_DIR` to inspect fresh `adc`, `aar`, and `aard` binaries and verify the direct command flags and required-input failures consumed by service.  The corresponding carve removal remains pending until the service checkpoint has a commit ID and the carve commands no longer dispatch the moved packages.

### Verification

- [x] `go test -buildvcs=false ./service/... ./cmd/...`
- [x] `CARVE_BIN_DIR=/tmp/carve-core-bins GOCACHE=/tmp/adjudication-service-go-cache go test -buildvcs=false -count=1 ./service/compat`
- [x] `go list -buildvcs=false -f '{{.ImportPath}}: {{join .Imports " "}}' ./service/... ./cmd/...`
- [x] Import search found no `adjudication/adc/runtime`, `adjudication/arb/runtime`, or `adjudication/arbd/runtime` import in `service/` or `cmd/`.
