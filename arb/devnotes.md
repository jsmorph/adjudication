# Development Notes

## 2026-04-01

### Literate Lean proof pass

Reference: [Literate Lean notes](docs/literate-lean.md)

The first proof batch does not try to prove the whole procedure at once.  It
states a few properties that the present engine already claims to implement and
that are useful enough to stabilize early.

The current proof files are:

| File | Purpose |
|---|---|
| `engine/Proofs/InitializeCase.lean` | Policy and initialization postconditions |
| `engine/Proofs/MeritsFlow.lean` | Ordered phase progression through the merits sequence |
| `engine/Proofs/Deliberation.lean` | Vote threshold, no-majority closure, round advance, and member selection |

The shared sample file, `engine/Proofs/Samples.lean`, exists only to keep the
later files readable.  It collects the small example states and the narrow
field-extraction helpers that the theorems need.

### Why these proofs first

Initialization, phase order, and deliberation are the parts of the engine that
give the procedure its meaning.  The proofs are still sample-based, but they
are not arbitrary tests.  Each theorem states a procedural fact that should
remain true if the engine changes later.

### Initial proof targets

- Prove the symmetric policy facts that motivated shared per-side limits.
- Prove more about opportunity selection in rebuttal, surrebuttal, and
  deliberation.
- Prove cumulative material limits on exhibits and technical reports.
- Consider whether the engine should expose cleaner helper definitions for more
  general theorems about deliberation and closure.

### Reachable-state invariants

The proof set no longer stops at representative examples.  The current files
now prove two global invariants over every Lean state reachable through
successful initialization and successful public `step` transitions.

| File | Purpose |
|---|---|
| `engine/Proofs/ReachableInvariants.lean` | Every reachable state preserves the merits-sequence invariant, and therefore procedural parity |
| `engine/Proofs/ReachableMaterialLimits.lean` | Every reachable state respects the cumulative exhibit and report caps |
| `engine/Proofs/StepPreservation.lean` | Public `step` preservation for openings, arguments, rebuttals, surrebuttals, closings, optional passes, council votes, and council-member removal |

This changed the proof burden.  The hard part is no longer to state the global
theorems.  It is to keep the step-preservation layer readable while it mirrors
the executable branching structure in `Main.lean`.

### Next proof targets

- Prove stronger global facts about council composition and vote thresholds.
- Prove more about opportunity selection from reachable states, not only about
  state preservation after a successful step.
- Simplify some proof surfaces in `StepPreservation.lean` so the executable
  branches and the proof branches line up more directly.

## 2026-04-02

### Deliberation-neutrality policy decision

Reference: [Verification notes](docs/verification-notes.md)

The proof work exposed a policy-space problem rather than a coding defect.
`currentResolution?` checks `demonstrated` before `not_demonstrated`.  That is
acceptable only if both outcomes cannot simultaneously satisfy the configured
threshold.  The validator previously allowed that overlap.

The engine now resolves that at the policy boundary.  `validatePolicy` in Lean
and Go requires `2 * required_votes_for_decision > council_size`.  That keeps
the current aggregation rule, removes the dual-threshold cases, and makes the
planned deliberation-neutrality theorem a theorem about the whole validated
policy space rather than a theorem with an extra side condition.

### Deliberation-neutrality proof

Reference: [Verification plan](docs/verification-plan.md)

Stage 7 is now complete in `engine/Proofs/Neutrality.lean`.  The proof does
not quantify over arbitrary malformed cases.  It proves neutrality over
reachable states, where the existing integrity layer already guarantees that
current-round votes come from distinct seated members and cannot outgrow the
configured council size.

The key proof shape is simple.  First, define a vote-flip map on council
votes and show that flipping the current round swaps the two substantive vote
counts.  Then combine that with the strict-majority validator and the
reachable seat bound to exclude dual-threshold states.  That is enough to show
that `currentResolution?` commutes with the vote flip on every reachable
state.

## 2026-04-03

### Explicit case-file selection for `aar case`

`aar case` still defaults to loading case files from the complaint directory.
That behavior is convenient for the examples, but it depends on a directory
scan and a skip list.  The CLI now also accepts repeated `--file` arguments,
including glob patterns, and passes the resolved file list into the runner.

The explicit list replaces the directory scan entirely.  That keeps the old
default while giving the caller a precise file boundary for one run.  The CLI
expands globs, rejects unmatched glob patterns, and rejects prohibited
extensions: `.gitignore`, `.sh`, and `.sig`.  The runner then loads exactly
those files and fails on duplicate basenames, because the case record keys
files by visible filename.

### `aar case` summary JSON

`aar case` now writes one JSON object to standard output for execution
results.  On success, the object reports the resolution and the final-round
counts for votes for and against the proposition.  On failure, the object
reports the error string.

The command still exits nonzero on failure.  The CLI wraps those failures in a
reported-error type so the JSON object remains the only case-result payload on
standard output and the binary does not add a second plain-text error line for
that path.

### Attorney web search in ACP runs

The attorney prompts already instruct the model to use native web search when
public investigation matters.  `arb` had not been staging a search-enabled
model into the temporary PI home for ACP sessions, so the attorneys were told
to do work that the runtime had not enabled.

The PI-home staging path now overrides the temporary ACP default model to
`openai://gpt-5?tools=search` and adds that model to the staged PI catalog.
That keeps the shared PI configuration unchanged while making the `arb`
attorney sessions match the prompt surface and the xproxy capability surface.

The old attorney timeout also became too short once that search path was real.
`arb` had been giving ACP attorney turns 480 seconds.  In `ex4`, the plaintiff
arguments turn now uses public-source investigation heavily enough to exceed
that limit before filing.  The default ACP attorney timeout is now 900
seconds.

### Attorney filing limits in prompts

`ex4` exposed a second prompt defect after web search was enabled.  The
attorneys could now gather the needed material, but the prompt still left key
filing constraints implicit.  The plaintiff rebuttal then burned its retries on
 three avoidable mistakes: a rebuttal that exceeded the text limit, too many
technical reports for the side-wide cap, and earlier attempts to place
workspace filenames in `offered_files`.

The prompt and attorney view now state the hard limits for the current
opportunity.  That includes the text limit for the current filing, the per-file
and per-side exhibit and technical-report caps, the amount already used by the
current side, and the remaining capacity.  The prompt now also states the real
record rule: `offered_files` may name only visible case files by `file_id`;
outside material enters through `technical_reports`.

The ACP-side validation errors now carry the attempted count and the remaining
side capacity.  That keeps the model close to the actual engine rule and avoids
wasting retries on blind correction attempts.

### Configurable attorney model and capability-aware prompts

`aar case` now accepts `--attorney-model`.  The value is an explicit xproxy
model id such as `openai://gpt-5` or `openai://gpt-5?tools=search`.  The
runner validates that model id up front, stages it into the temporary PI home,
and records the effective attorney model and search flag in the run metadata.

The attorney prompts no longer hardcode web-search availability.  They render
one capability section from the configured model and one phase-specific
investigation section that changes when native search is unavailable.  That
keeps one prompt family while making the runtime state explicit.  It also
removes the earlier mismatch where the prompt told counsel to use native search
even when the configured model lacked it.

The `arb` Makefile now chooses attorney models explicitly by example.  `demo`,
`ex2`, and `ex3` use `openai://gpt-5` without native search.  `ex4` keeps
`openai://gpt-5?tools=search`, because that example depends on public-source
investigation.

### Per-role ACP configuration and remote endpoints

ACP still centers on stdio.  The ACP transport page says the protocol defines
stdio today and lists streamable HTTP as draft work in progress.  It also
permits custom transports.  The current `pi-acp` adapter in this repository
documents only JSON-RPC 2.0 over stdio.  Those sources matter here:

- ACP transports: https://agentclientprotocol.com/protocol/transports
- ACP introduction: https://agentclientprotocol.com/get-started/introduction
- `pi-acp` README: ../common/submodules/pi-acp/README.md
- `pi-acp` engineering notes: ../common/submodules/pi-acp/AGENTS.md
- GitHub Copilot CLI ACP server reference, which documents a TCP mode as a custom remote transport: https://docs.github.com/en/copilot/reference/copilot-cli-reference/acp-server

`arb` now resolves attorney configuration per role.  The global
`--attorney-model` and `--acp-command` flags remain the defaults.  The CLI also
accepts plaintiff and defendant overrides for model, ACP command, ACP endpoint,
and ACP session cwd.  That allows one side to stay on the local wrapper while
the other side points at a different ACP server.

The remote path uses a custom TCP transport.  The client opens a persistent TCP
connection and exchanges newline-delimited ACP JSON-RPC messages over that
stream.  This is a deliberate custom transport, not an implementation of the
draft streamable-HTTP work.  The runner records the resolved attorney
configuration for each side in `run.json` and in the `run_initialized` event.

The runner still depends on `_aar/*` client methods for case access and filing.
`pi-acp` learns those methods from environment staging in the local wrapper
path.  A remote ACP server must already know how to use the current `_aar/*`
method contract.  The new transport path does not make an arbitrary ACP server
usable as an `arb` attorney by itself.

### Proxy-backed plaintiff demo

The proxy demo now stages the backend PI home through the same code path that
ordinary attorney runs use.  `aar` exposes two helper commands for that
purpose: one stages the PI home into a supplied directory, and one prints the
current `_aar/*` tool catalog as JSON.  The demo script now uses those helpers
instead of carrying its own copies of `settings.json`, `models.json`, and the
tool schema.

That change fixed a real mismatch.  The earlier script omitted
`_aar/write_case_file` and hand-built the PI configuration.  After the change,
the proxy-backed plaintiff opening matched the ordinary local path closely
enough to complete: note file write, opening submission, accepted filing.

It did not fix the plaintiff arguments failure in `ex6`.  The plaintiff still
stalled in the arguments phase.  The failure mode changed, which narrows the
cause.  The old run spent its time rewriting notes around citation formatting
and source packaging.  The new run used the full tool surface and reached the
substance faster.  It still kept rewriting `case-notes.md`, but the content now
tracked the adverse merits directly: the notes concluded that the official
record supports ground entry but likely not the territorial-objective element,
and that the plaintiff's best colorable `YES` theory runs into the explicit
edge-case carveout.  That points to a prompt or role-interface problem about
how plaintiff advocacy should proceed when truthful investigation turns the case
against the assigned side.  It does not point to ACP transport or PI-home
staging any longer.
