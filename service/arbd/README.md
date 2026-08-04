# AARD Service

The AARD service programs supervise Agent Arbitration Degree cases and local agents.  They require an `aard` executable and its Lean engine from a selected `carve` revision.  The [core process interface](../../docs/core-interface.md) defines the boundary between the two revisions.

## Programs

| Program | Purpose |
| --- | --- |
| `aard-service` | Run the multi-case Clerk and direct-case HTTP service. |
| `aard-run` | Run one core case with MCP, OpenClaw lawyers, and Pi council members. |
| `aard-mcp` | Adapt one core lawyer and council API to Streamable HTTP MCP. |

Build the service commands from this checkout and build AARD from the selected `carve` checkout.  The service receives explicit executable and working-directory paths, so the checkouts need not share a parent directory.  `aard-service --help`, `aard-run --help`, and `aard-mcp --help` give the complete flag inventory.

```bash
go build -o ./bin/aard-service ./cmd/aard-service
go build -o ./bin/aard-run ./cmd/aard-run
go build -o ./bin/aard-mcp ./cmd/aard-mcp

./bin/aard-service \
  --listen 127.0.0.1:19790 \
  --out-root out/aard-service \
  --aard-bin /path/to/carve/arbd/.bin/aard \
  --aard-run-bin "$(pwd)/bin/aard-run" \
  --aard-working-dir /path/to/carve/arbd \
  --engine /path/to/carve/arbd/.bin/aardengine
```

## HTTP API

Clerk routes start `aard-run`, which manages the core case, MCP adapter, OpenClaw lawyers, and Pi council members.  Direct routes start `aard case` for callers that manage participants through HTTP.  Setting `--bearer-token` requires the same bearer token on Clerk, direct-case, role-proxy, artifact, and evidence routes.

| Method | Path | Purpose |
| --- | --- | --- |
| `POST`, `GET` | `/clerk/v1/cases` | Create or list Clerk cases. |
| `GET` | `/clerk/v1/cases/{case_id}` | Read a Clerk record. |
| `POST` | `/clerk/v1/cases/{case_id}/kill` | Stop an attached Clerk child process. |
| `GET` | `/clerk/v1/cases/{case_id}/result` | Read a Clerk result or current status. |
| `GET` | `/clerk/v1/cases/{case_id}/artifacts[/name]` | List or read allowed Clerk artifacts. |
| `GET` | `/clerk/v1/cases/{case_id}/evidence/{evidence_id}` | Read evidence named by the core manifest. |
| `GET` | `/clerk/v1/cases/{case_id}/attestation/events` | Read live or downloaded attestation events. |
| `POST`, `GET` | `/api/v1/cases` | Create or list direct cases. |
| `GET` | `/api/v1/cases/{case_id}` | Read a direct-case record. |
| `POST` | `/api/v1/cases/{case_id}/cancel` | Stop an attached direct case. |
| `GET` | `/api/v1/cases/{case_id}/result` | Read a direct result or current status. |
| `GET` | `/api/v1/cases/{case_id}/artifacts[/name]` | List or read allowed direct-case artifacts. |
| `GET` | `/api/v1/cases/{case_id}/evidence/{evidence_id}` | Read direct-case evidence. |
| any | `/lawyerapi/v1/get`, `/wait`, `/status`, `/result`, `/do` | Proxy a lawyer request to a direct case. |
| any | `/councilapi/v1/get`, `/wait`, `/do` | Proxy a council request to a direct case. |

A Clerk request selects either an `example` from the core checkout or a `complaint_path` with optional `case_files`.  Its remaining fields cover policy and judgment-standard selection, council size and pool, prompts, timeouts, engine path, MCP addresses, OpenClaw settings, Pi settings, container commands, and output limits.  The `ClerkCreateRequest` type in `service/arbd/clerk.go` is the exact JSON field definition.

```bash
curl -sS -X POST http://127.0.0.1:19790/clerk/v1/cases \
  -H 'content-type: application/json' \
  --data '{
    "case_id": "aard-service-example",
    "complaint_path": "/path/to/carve/arbd/examples/ex1/complaint.md",
    "out_dir": "aard-service-example",
    "auto_lawyers": "both",
    "council_pool_path": "/path/to/council-pool.jsonl"
  }'
```

A direct request uses `POST /api/v1/cases` with `complaint_path`, optional `case_files`, and core runtime fields.  Set `council_backend` to `councilapi` when council members will act through the proxy routes.  The `CaseCreateRequest` type in `service/arbd/service.go` defines the direct JSON shape.

## Attested Execution

An attested Clerk request sets `execution.mode` to `attested` and supplies `execution.attestation`.  Service flags beginning with `--attested-` provide deployment defaults, while request fields can select the driver, parser, S3 prefixes, AMI, host, AWS settings, image tar, polling limits, timeout, and expected PCR values.  Attested execution accepts the same case selectors as local Clerk execution and rejects local-agent or runtime fields that the attested driver cannot reproduce.

```json
{
  "case_id": "aard-attested-example",
  "complaint_path": "/path/to/carve/arbd/examples/ex1/complaint.md",
  "execution": {
    "mode": "attested",
    "attestation": {
      "input_prefix": "s3://BUCKET/aard-inputs/aard-attested-example",
      "output_prefix": "s3://BUCKET/aard-runs/aard-attested-example"
    }
  }
}
```

The service records requested and resolved execution settings with the attestation status and local artifact paths.  It reports completion after the driver verifies the attestation and extracts a readable `aard-output/run.json`.  The [AARD image runbook](../attested/arbd/Dockerfile.md) and [development-host requirements](../attested/arbd/attested-dev-host.md) describe the complete build, launch, S3, and verification procedure.

## Records and Artifacts

Each Clerk output directory contains `clerk.json`, child standard streams, and the files produced by `aard-run` and the core process.  Direct-case records live under `--registry-dir`, while their core artifacts and service logs live under the selected case output directory.  After a restart, the service reconciles terminal `run.json` files and marks an unrecoverable detached process failed.

Artifact routes expose fixed allowlists rather than arbitrary paths.  Local records include the core result, state, certificate, digest, transcript, events, work notes, evidence manifest, and service logs.  Attested records add selected run environment, launcher, archive, manifest, attestation, and verification files.
