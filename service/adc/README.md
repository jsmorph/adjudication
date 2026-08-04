# ADC Service

The ADC service programs supervise core ADC cases and local agents.  They require an `adc` executable and its Lean engine from a selected `carve` revision.  The [core process interface](../../docs/core-interface.md) defines the boundary between the two revisions.

## Programs

| Program | Purpose |
| --- | --- |
| `adc-service` | Run the multi-case Clerk HTTP service. |
| `adc-run` | Run one core case with MCP, OpenClaw lawyers, and Pi jurors. |
| `adc-mcp` | Adapt one core Role API to Streamable HTTP MCP. |

Build the service commands from this checkout and build ADC from the selected `carve` checkout.  The service receives explicit executable and working-directory paths, so the checkouts need not share a parent directory.  `adc-service --help`, `adc-run --help`, and `adc-mcp --help` give the complete flag inventory.

```bash
go build -o ./bin/adc-service ./cmd/adc-service
go build -o ./bin/adc-run ./cmd/adc-run
go build -o ./bin/adc-mcp ./cmd/adc-mcp

./bin/adc-service \
  --listen 127.0.0.1:19870 \
  --output-root out/adc-service \
  --adc-bin /path/to/carve/adc/.bin/adc \
  --adc-run-bin "$(pwd)/bin/adc-run" \
  --adc-working-dir /path/to/carve/adc \
  --engine /path/to/carve/adc/.bin/adcengine
```

## HTTP API

The Clerk and `/api/v1/cases` routes use the same ADC case records.  The service stores each record in its case output directory and reconciles terminal status from the core `run.json`.  Setting `--bearer-token` requires the same bearer token on every service route.

| Method | Path | Purpose |
| --- | --- | --- |
| `POST`, `GET` | `/clerk/v1/cases` | Create or list cases. |
| `GET` | `/clerk/v1/cases/{case_id}` | Read a case record. |
| `POST` | `/clerk/v1/cases/{case_id}/kill` | Stop an attached child process. |
| `GET` | `/clerk/v1/cases/{case_id}/result` | Read a terminal result or current status. |
| `GET` | `/clerk/v1/cases/{case_id}/artifacts[/name]` | List or read allowed artifacts. |
| `GET` | `/clerk/v1/cases/{case_id}/evidence/{evidence_id}` | Read evidence named by the core manifest. |
| `GET` | `/clerk/v1/cases/{case_id}/attestation/events` | Read live or downloaded attestation events. |
| same methods | `/api/v1/cases...` | Aliases for the Clerk case routes. |
| any | `/roleapi/v1/get`, `/wait_for_opportunity`, `/status`, `/result`, `/do`, `/fail` | Proxy a request to the selected core case. |

An omitted `mode`, or `mode: "run"`, starts `adc-run` and its local-agent processes.  `mode: "direct"` starts `adc case` or `adc scenario` and accepts `external_roles` for agents managed by the caller.  A request selects exactly one of `complaint_path` and `scenario_path`, and an explicit `out_dir` must be an immediate child of the configured output root.

```bash
curl -sS -X POST http://127.0.0.1:19870/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "mode": "direct",
    "case_id": "adc-service-example",
    "complaint_path": "/path/to/carve/adc/examples/ex1/complaint.md",
    "out_dir": "out/adc-service/adc-service-example"
  }'
```

The create request also accepts core setup, model, jury, timeout, response-limit, and engine fields.  Local-agent fields select MCP addresses, instruction files, OpenClaw options, Pi options, container commands, and output limits.  The `CaseCreateRequest` type in `service/adc/service.go` is the exact JSON field definition.

## Attested Execution

An attested complaint request sets `execution.mode` to `attested` and supplies `execution.attestation`.  Service flags beginning with `--attested-` provide deployment defaults, while request fields can select the driver, parser, S3 prefixes, AMI, host, AWS settings, image tar, polling limits, timeout, and expected PCR values.  ADC attested execution requires verification and accepts complaint input rather than a prepared scenario.

```json
{
  "mode": "run",
  "case_id": "adc-attested-example",
  "complaint_path": "/path/to/carve/adc/examples/ex1/complaint.md",
  "execution": {
    "mode": "attested",
    "attestation": {
      "verify": true,
      "input_prefix": "s3://BUCKET/adc-inputs/adc-attested-example",
      "output_prefix": "s3://BUCKET/adc-runs/adc-attested-example"
    }
  }
}
```

The service records requested and resolved execution settings with the attestation status and local artifact paths.  It reports completion after the driver verifies the attestation and extracts a readable `adc-output/run.json`.  The [ADC image runbook](../attested/adc/Dockerfile.md) and [development-host requirements](../attested/adc/attested-dev-host.md) describe the complete build, launch, S3, and verification procedure.

## Records and Artifacts

The artifact endpoint exposes an allowlist that includes the core result, state, certificate, digest, transcript, events, work notes, and evidence manifest, plus service process logs.  Attested records add selected launcher, manifest, archive, attestation, and verification files.  Missing allowlisted files and names outside the allowlist produce different API errors.

Local runs write `local-run.json`, while the multi-case service writes its case record and service logs under the selected output directory.  A service restart reads disk records and reconciles an available terminal core record.  A case that lacks a readable terminal record after losing its attached process becomes failed.
