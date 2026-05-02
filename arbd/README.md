# Agent Arbitration Degree

Agent Arbitration Degree is a sibling of [Agent Arbitration](../arb).  It keeps the same stripped-down merits procedure: openings, arguments, rebuttal, surrebuttal, closings, and council deliberation.  The difference is the question type.  `arbd/` handles questions of degree and returns one bounded integer answer from each council member in the range `[0,100]`.

The procedure does not aggregate those answers.  It records the final answer map keyed by `member_id`, for example `{"C1":72,"C2":45,"C3":88}`.  The result closes when every seated council member has submitted one answer for the round.  If removals or timeouts reduce the seated set during deliberation, closure follows the remaining seated members.

## Layout

| Path | Purpose |
|---|---|
| `engine/` | Lean engine and proofs |
| `runtime/` | Go runtime and `aard` CLI |
| `prompts/` | Attorney and council prompts |
| `examples/` | Degree-question example materials |

## Build

Run these commands from `arbd/`:

```bash
make build-image
make build
make test
make prove
```

`make build-image` builds the shared Podman image used by the ACP attorney backend.  `make build` then builds the Lean engine and the Go CLI.  `make demo` drafts `examples/ex1/complaint.md` from `examples/ex1/situation.md` and runs one complete case in `out/ex1-demo/`.

## Complaint Format

`aard complain` and `aard validate` use one required heading:

```markdown
# Question

What percentage of artwork Y is novel in view of artwork X?
```

## Run A Case

```bash
make build-image
make build
.bin/aard complain \
  --situation examples/ex1/situation.md \
  --out examples/ex1/complaint.md
.bin/aard case \
  --complaint examples/ex1/complaint.md \
  --out-dir out/ex1-demo
```

`aard case` scans the complaint directory for case files when `--file` is absent.  It skips the complaint, the situation file, `README.md`, signing artifacts, and directories.  It loads `.txt`, `.md`, `.pem`, and `.b64` files as readable case files and records other file types as byte-bearing exhibits.

The default attorney path uses `../common/pi-container/acp-podman.sh`.  That path also requires a provider API key in the environment for the selected model endpoint, such as `OPENAI_API_KEY` for `openai://...` models or `OPENROUTER_API_KEY` for `openrouter://...` models.

## Key Flags

| Flag | Meaning |
|---|---|
| `--complaint` | Complaint markdown file.  Required. |
| `--out-dir` | Output directory for the run packet.  Required. |
| `--file` | Explicit case file path or glob.  Repeating this flag replaces automatic complaint-directory scanning. |
| `--policy` | Policy JSON file.  Defaults to `./etc/policy.json` when present. |
| `--council-size` | Override `policy.council_size`. |
| `--judgment-standard` | Override `policy.judgment_standard`. |
| `--council-pool` | Council model and persona pool.  Defaults under `common/`. |
| `--attorney-model` | Attorney ACP model id. |
| `--attorney-instructions` | Standing attorney instructions file. |
| `--engine` | Lean engine binary.  Defaults to `.bin/aardengine` next to the CLI binary. |

## Outputs

Each run writes a full packet to `--out-dir`: `complaint.md`, `policy.json`, `runtime.json`, `run.json`, `state.json`, `council.json`, `digest.md`, `transcript.md`, and `events.ndjson`.

On success, `aard case` prints one JSON object to stdout:

```json
{"status":"ok","answers":{"C1":72,"C2":45,"C3":88},"run_id":"run-123","out_dir":"out/ex1-demo"}
```

On failure, it prints:

```json
{"status":"error","error":"..."}
```
