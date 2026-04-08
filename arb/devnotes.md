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

Reference: [Verification](docs/verification.md)

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

Reference: [Verification](docs/verification.md)

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

## 2026-04-08

### Verification document consolidation

Reference: [Verification](docs/verification.md)

The verification material had split into a status note, a stage plan, and a
findings note.  That separation made the current state harder to read, because
a reader had to reconstruct one story from three files.  The documentation now
uses `docs/verification.md` as the canonical record for established results,
the finished stage structure, proof-driven findings, and the limits of what the
Lean engine can prove.

### Abstract verification structures

Reference: [More verification notes](docs/more-verification-notes.md)

The next proof work now has a separate note about abstractions that the current
engine already suggests.  The strongest candidates are a progress preorder over
fixed-frame runs, a compact deliberation summary, a viable-outcomes notion for
threshold reachability, the existing vote-flip involution, a lexicographic
termination potential, and a trace semantics for successful runs.  The
recommended first extension is a deliberation-summary layer that isolates
counts, remaining eligible voters, round budget, and outcome attainability from
the full case record.

### Deliberation summary proof layer

Reference: [More verification notes](docs/more-verification-notes.md)

The first implementation step now spans
`engine/Proofs/DeliberationSummaryCore.lean` and
`engine/Proofs/DeliberationSummary.lean`.  The core file now carries the
compact proof-side `DeliberationSummary` record, the direct case-level
correspondence with `currentResolution?`, and the lower council arithmetic that
the summary layer needs.  The wrapper file keeps the reachable vote-count,
seated-count, and positive-threshold bounds that rely on later proof layers.

### Summary-core dependency split

Reference: [Verification](docs/verification.md)

The import graph had blocked the next summary-based compression.  `OutcomeSoundness.lean`
and `NoStuck.lean` sat below `DeliberationSummary.lean`, because that file had
been importing `BoundedTermination.lean` for a few local arithmetic lemmas and
for the reachable wrappers.  The summary layer now splits at that boundary:
`DeliberationSummaryCore.lean` sits below `OutcomeSoundness.lean`, while
`DeliberationSummary.lean` keeps only the reachable wrappers above `NoStuck`.

That change pulled the direct `currentResolution?` soundness facts into the
summary core and let `OutcomeSoundness.lean` consume them directly.  The lower
termination file now imports the core arithmetic instead of defining the same
council-length and current-round-capacity lemmas itself.  The remaining import
pressure is now on the liveness side rather than on outcome soundness.

### Summary-form liveness bridge

Reference: [Verification](docs/verification.md)

The next split now reaches one theorem in `NoStuck.lean`.  The selector fact
that `nextCouncilMember?` returns a seated member who has not yet voted moved
into `DeliberationSummaryCore.lean`, together with the summary-capacity lemma
that turns that fact into `current_round_vote_count < seated_count`.  `NoStuck.lean`
now uses those lower results to prove the summary-form round-capacity theorem
for every reachable live deliberation state.

This matters because it moves one real liveness theorem below
`ViableOutcomes.lean` instead of leaving the whole summary bridge above the
existing Stage 3 file.  The remaining pressure is now narrower: the viability
and closure facts still sit above `NoStuck.lean`, but the basic summary view
of live deliberation no longer does.

### Viability-core dependency split

Reference: [Verification](docs/verification.md)

The same import pressure then showed up inside the viability layer.  The
summary-level viability definitions and lemmas had been sitting in
`ViableOutcomes.lean` above the executable update correspondences, even though
most of them did not depend on removal arithmetic or on later proof layers.
The viability layer now splits the same way the summary layer did:
`ViableOutcomesCore.lean` carries the pure viability language and the
summary-only theorems, while `ViableOutcomes.lean` keeps the direct vote and
removal update correspondences.

This matters on the closure side.  `OutcomeSoundness.lean` now imports
`ViableOutcomesCore.lean` and proves the `no_majority` branch through summary
non-viability instead of reopening the threshold arithmetic directly from
`currentResolution? = none`.  The core file now also carries a summary closure
predicate for `no_majority`, so the lower layer can package the executable
closure reasons with the below-threshold conclusion before `OutcomeSoundness.lean`
translates the result back to the state-level statement.  `OutcomeSoundness.lean`
now also proves the direct bridge in both directions: summary `no_majority`
closure is sufficient for `continueDeliberation` to close that way, and an
executable `no_majority` closure from deliberation implies the same summary
predicate on the source state.  That leaves the higher file responsible only
for the executable update correspondence lemmas that still depend on the later
termination layer.

### Viable outcomes proof layer

Reference: [More verification notes](docs/more-verification-notes.md)

The second implementation step now spans `engine/Proofs/ViableOutcomesCore.lean`
and `engine/Proofs/ViableOutcomes.lean`.  The core file defines summary-level
viability for the two substantive outcomes, proves the first shrinkage facts,
and packages the pure summary-side closure lemmas.  A vote for one side
preserves that side's viability and can only shrink the other side's viability.
Removing one seated member can only shrink viability for both sides.  The
higher file then proves that these summary updates match the intermediate
deliberation states produced by direct vote and removal updates before
`continueDeliberation` runs.

### Summary-based public wrappers

Reference: [More verification notes](docs/more-verification-notes.md)

The first bridge theorems for the third stage now split across
`engine/Proofs/OutcomeSoundness.lean`, `engine/Proofs/NoStuck.lean`,
`engine/Proofs/ViableOutcomesCore.lean`, and `engine/Proofs/ViableOutcomes.lean`.
The liveness side now proves the summary-form current-round capacity bound in
`NoStuck.lean`.  The closure side now proves the `no_majority` arithmetic
through summary non-viability in `OutcomeSoundness.lean`.  The core viability
file handles the summary-side facts: executable `currentResolution?` implies
the corresponding summary-viability fact, summary-level exhaustion implies
executable non-resolution, and the summary-level count flip swaps the two
substantive outcomes.  The higher viability file then handles the executable
vote and removal update correspondences.  `engine/Proofs/Neutrality.lean` now
uses that lower summary form directly, so the reachable vote-flip theorem is
stated over the same public result but proved through `DeliberationSummary`
instead of through another round of raw vote-count case analysis on the case
record.

### Closed-resolution bridge

Reference: [Verification](docs/verification.md)

The next compression step turned the summary closure language into one uniform
bridge for closed deliberation results.  `ViableOutcomesCore.lean` now defines
the proof-side `DeliberationSummary.closedResolution?` function and proves the
summary equalities that correspond to substantive threshold closure and to
`no_majority` closure.  `OutcomeSoundness.lean` now proves the executable
bridge in both directions: if the source summary reports a closed resolution,
`continueDeliberation` returns exactly that closed result, and if
`continueDeliberation` closes a deliberation-phase case, the source summary
reports the same result.

This matters because the summary layer no longer describes only the
`no_majority` branch.  It now packages the whole closed-output boundary of
`continueDeliberation`, which is the right granularity for later monotonicity
or inevitability theorems.  The remaining higher work is correspondingly
narrower: the executable vote and removal update correspondences still sit
above this layer, but the closure logic itself now has one proof-side shape.

### Executable viability transport

Reference: [More verification notes](docs/more-verification-notes.md)

The next step converted those remaining executable update correspondences into
real viability statements.  `ViableOutcomes.lean` still uses the summary equalities
for the intermediate vote and removal cases before `continueDeliberation`, but
it now proves what those equalities mean for the engine state.  A vote for
`demonstrated` preserves demonstrated viability and preserves impossibility of
`not_demonstrated`.  A vote for `not_demonstrated` preserves not-demonstrated
viability and preserves impossibility of `demonstrated`.  A seated-member
removal preserves impossibility for both substantive outcomes.

This matters because the higher viability file is no longer only a transport
layer.  It now carries executable impossibility facts that the later public
step theorems can consume without reopening the arithmetic in the summary core.

### Same-round final-state bridge

Reference: [Verification](docs/verification.md)

The next step pushed that transport across the `continueDeliberation` boundary
when the round does not advance.  `ViableOutcomes.lean` now proves a compact
congruence fact for `DeliberationSummary`: if `continueDeliberation` keeps the
same deliberation round, then the final state has the same summary as the
intermediate `stateWithCase s c`.  That is the right bridge because the
function may still close the case in place, but closure changes none of the
summary fields.

That bridge supports two new public same-round results.  First, a successful
council-vote step now yields an existential `sameRoundVoteTransport` theorem:
for the submitted vote label, the final state preserves viability of the voted
side and preserves impossibility of the opposite side.  Second, a successful
council-member removal step now preserves demonstrated impossibility,
not-demonstrated impossibility, and therefore total substantive non-viability
when the round stays fixed.

### Progress-viability bridge

Reference: [More verification notes](docs/more-verification-notes.md)

The next step connected those same-round deliberation facts to the structural
progress layer without overstating what `fixedFrameProgress` can prove by
itself.  `ProgressViability.lean` imports both `Progress.lean` and
`ViableOutcomes.lean` and proves two public bridge theorems.  A successful
same-round council-vote step now yields both `fixedFrameProgress s t` and an
existential `sameRoundVoteTransport` witness.  A successful same-round
council-member removal step now yields `fixedFrameProgress s t` together with
an implication from source total substantive non-viability to target total
substantive non-viability.

This matters because it marks the boundary of the current abstraction honestly.
The present preorder tracks case frame, materials, seats, phase rank, and
round.  It does not track current-round votes.  The new bridge therefore pairs
progress with viability transport on the concrete same-round deliberation steps
where the vote update is known, instead of claiming a false global monotonicity
theorem for `fixedFrameProgress` alone.

### Same-round deliberation progress

Reference: [Verification](docs/verification.md)

The next step turned that bridge into a proof-side relation.  `ProgressViability.lean`
now defines `viableOutcomesShrink`, which says that target viability for either
substantive outcome implies source viability for that same outcome.  It then
defines `sameRoundDeliberationProgress`, which combines `fixedFrameProgress`,
same-round equality, and that shrink relation.  Both new relations are
reflexive and transitive.

The public step theorems now establish that same-round relation for successful
council-vote and council-removal steps.  The vote side uses a new lower wrapper
in `StepPreservation.lean` that exposes the already-forced vote-label
disjunction from `recordCouncilVote`.  The removal-side non-viability
preservation theorem now follows from `viableOutcomesShrink` instead of sitting
as a separate ad hoc implication.  This is the first abstract relation in the
library that tracks both structural progress and substantive viability
shrinkage without pretending that the global preorder already contains current-round
vote data.

### Same-round closure inevitability

Reference: [More verification notes](docs/more-verification-notes.md)

The next step completed that same-round line.  `ProgressViability.lean` now
proves that `sameRoundDeliberationProgress` preserves `no_majority` closure
reasons in the only form that matters for later closure: the target state has
completed the round.  The key structural lemma here is seat-count monotonicity
under `fixedFrameProgress` plus source council-id uniqueness.  That suffices to
carry the "too few seats" closure reason forward, while same-round equality and
fixed policy carry the last-round reason.

The file then packages the main theorem: if the source summary already has no
viable substantive outcome and already has one `no_majority` closure reason,
then any later same-round progress state that completes the round is forced to
summary `no_majority` closure.  The executable corollary is direct through
`OutcomeSoundness.lean`: `continueDeliberation` on that target state must close
as `no_majority`.  The public council-vote and council-removal theorems now
inherit that result.  This finishes the summary, viability, and same-round
progress agenda as a coherent proof line.

### Fixed-frame progress preorder

Reference: [More verification notes](docs/more-verification-notes.md)

The next implementation step now lives in `engine/Proofs/Progress.lean`.  The
file defines `fixedFrameProgress`, a state relation anchored to the source
frame and paired with the monotone coordinates that the library had been
proving separately: append-only admitted materials, shrinking seated-member
identifiers, nondecreasing phase rank, and nondecreasing deliberation round.
The first theorem batch proves reflexivity and transitivity, shows that every
successful public step establishes that relation, and packages the initialized
run form as the conjunction of the initialization frame and source-anchored
progress from the initialized state.
