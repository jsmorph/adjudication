# Adjudication Services

This branch contains the operational programs for Agent District Court, Agent Arbitration, and Agent Arbitration Degree.  The programs start and supervise core processes, expose multi-case Clerk APIs, adapt case Role APIs to MCP, run local agents, build attested workloads, and present service records through web applications.  The procedure engines, proofs, one-case runtimes, rules, and core commands live on the `carve` branch.

## Programs

| Program | Purpose |
| --- | --- |
| `adc-service`, `aar-service`, `aard-service` | Create, inspect, stop, and retrieve artifacts from multiple cases. |
| `adc-mcp`, `aar-mcp`, `aard-mcp` | Expose one core case's Role API through Streamable HTTP MCP. |
| `adc-run`, `aar-run`, `aard-run` | Start one core case and manage its OpenClaw lawyers and Pi jurors or council members. |
| `adjudication-web` | Operate the three Clerk services through one server-rendered console. |
| `adjudication-manage` | Manage ARB Clerk, attested, and direct cases. |
| `adjudication-report` | Read and render completed run directories from disk. |

## Core Boundary

The service programs communicate with installed `adc`, `aar`, and `aard` executables through their command-line, private HTTP, and artifact interfaces.  A service deployment selects an immutable `carve` commit, builds or installs those core executables, and supplies their executable and working-directory paths to the service commands.  [The core interface specification](docs/core-interface.md) records the commands, routes, schemas, artifacts, and process behavior used across that boundary.

The attested Dockerfiles fetch full core and service commit IDs into separate build stages.  They compile the selected core command and Lean engine from `carve`, compile the service-owned launcher from this branch, and copy the required runtime assets into the final image.  Moving branch names do not define a compatible deployment pair.

## Build and Test

Go 1.25 builds every retained command.  The package test command covers the services, launchers, adapters, compatibility fixtures, and web programs.  The dependency command confirms that these packages import only service-owned repository packages.

```bash
go build -buildvcs=false ./cmd/... ./web/cmd/...
go test -buildvcs=false -count=1 ./service/... ./cmd/... ./web/...
go list -buildvcs=false -deps ./service/... ./cmd/... ./web/...
```

The local-agent launchers require Docker for OpenClaw and Podman for Pi.  [The Pi container recipe](service/pi-container/README.md) builds the default `agentcourt-pi-sandbox` image used by the three launchers.  Model-provider credentials depend on the selected lawyer configuration and Pi pool records.

## Attested Execution

Each procedure has a service-owned attested driver, base image, workload image, entrypoint, and operating runbook.  The drivers call the installed core `case-packet` command for complaint inputs and retain deployment, S3, attestation, and artifact handling on this branch.  Their build commands require full `CORE_COMMIT` and `SERVICE_COMMIT` values.

| Procedure | Runbook | Development host |
| --- | --- | --- |
| ADC | [ADC attested runbook](service/attested/adc/Dockerfile.md) | [ADC host requirements](service/attested/adc/attested-dev-host.md) |
| ARB | [ARB attested runbook](service/attested/arb/Dockerfile.md) | [ARB host requirements](service/attested/arb/attested-dev-host.md) |
| AARD | [AARD attested runbook](service/attested/arbd/Dockerfile.md) | [AARD host requirements](service/attested/arbd/attested-dev-host.md) |

## Documentation

The [ADC service manual](service/adc/README.md), [ARB service manual](service/arb/README.md), and [AARD service manual](service/arbd/README.md) document their commands and HTTP APIs.  The [web overview](web/README.md) and [web runbook](web/runbook.md) document the three operator-facing web programs.  The [service development journal](devnotes.md) records extraction commits and verification results, while the [retention ledger](docs/retention-ledger.md) records ownership decisions during the branch split.

## License

The software is released under the MIT License in [LICENSE](LICENSE).  Trademark and related notice terms are in [NOTICES.md](NOTICES.md).  The notices apply to the retained service programs and deployment material.
