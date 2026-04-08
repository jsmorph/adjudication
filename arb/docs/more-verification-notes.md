# More Verification Notes

## Purpose

This note records abstract structures that seem latent in the current Lean engine and proof library.  The aim is to identify concepts that would compress the next proof batch instead of adding another layer of local wrappers.  The engine already has enough verified behavior to support that kind of re-description.

## Current Abstract Shape

The engine is a finite transition system over a fixed case frame.  The static part of a run is already isolated by `caseFrameMatches`, while the dynamic part runs through `Reachable` and `StepPath`.  The existing proofs also expose three monotone behaviors: admitted materials extend by suffix, seated council membership only shrinks, and the remaining-step budget strictly decreases along successful public steps.

This means the core mathematical shape is closer to order theory and well-founded transition analysis than to ordinary algebra.  The state space is discrete, the public effects are mostly append-only or shrinking, and the interesting symmetries are small.  That is a good thing, because it points toward structures that match the executable semantics instead of decorating them.

## Candidate Structures

| Structure | Existing anchors | Candidate theorem family | Use |
|---|---|---|---|
| Progress preorder | `caseFrameMatches`, `materialsExtend`, seated-roster shrinkage, phase and round monotonicity | Every successful public step is monotone inside one fixed case frame. | Compresses many preservation theorems into one order-theoretic statement. |
| Deliberation summary | `currentRoundVotes`, `voteCountFor`, `seatedCouncilMemberCount`, `currentResolution?`, `continueDeliberation` | Resolution, live-next-voter existence, and closure conditions depend only on a compact summary. | Isolates the arithmetic core of deliberation from the rest of the case record. |
| Viable outcomes structure | Threshold counts, uncast seated votes, `no_majority` closure conditions | Votes and removals can only shrink the set of still-attainable substantive outcomes. | States impossibility and inevitability results cleanly. |
| `C₂` action on outcomes | `flipOutcomeLabel`, `flipCouncilVote`, `flipCaseVotes`, neutrality theorem | The aggregation rule is equivariant under the vote-flip involution. | Captures the real symmetry already present in the engine. |
| Lexicographic potential | `remainingMeritsSteps`, `remainingDeliberationSteps`, `remainingStepBudget` | Each public action decreases one coordinate of a structured potential. | Makes termination arguments more informative than a single collapsed scalar. |
| Trace semantics | `Reachable`, `StepPath`, append-only record growth, new-vote provenance | Successful runs admit clean projections to filings, materials, and votes. | Prepares replay and runtime-to-engine correspondence results. |

## What Does Not Fit

A ring, field, or ordinary topology does not match the engine well.  The procedure does not combine states by invertible composition, and it does not study continuity over an interesting ambient space.  The present engine is better described by fixed-frame transition orders, threshold arithmetic, and small symmetry actions.

## Recommended First Extension

If the next proof batch introduces one new concept, it should probably be `DeliberationSummary` together with a notion of viable outcomes.  Those two structures cut across outcome soundness, live-state liveness, neutrality, and closure, and they would make later theorems shorter because they isolate the arithmetic core of deliberation.  They also avoid forcing abstract algebra onto parts of the engine that are really about ordered transition structure and threshold reachability.

## Staged Roadmap

The next proof work should proceed in a narrow order.  The first step is a proof-side `DeliberationSummary` layer that packages the counts and limits already driving `currentResolution?`, `nextCouncilMember?`, and `continueDeliberation`.  The immediate theorem targets are correspondence results: the summary reproduces the executable resolution rule, its counts satisfy the reachable vote-integrity bounds, and its fields inherit the positive-threshold and seated-count facts already proved elsewhere.

The second step should define viable outcomes from that summary.  That structure should say whether `demonstrated` or `not_demonstrated` can still reach the threshold given the current counts and remaining uncast seated votes.  The next theorems should then show that council votes and removals can only shrink viability, and that `no_majority` closure coincides with viability exhaustion or round exhaustion.

The third step should lift the summary and viability layer back into the public results.  Outcome soundness, reachable live-state liveness, and neutrality should then become short consequences of the same summary facts instead of three mostly separate proof paths.  Only after that compression is in place should the library add a fixed-frame progress preorder, because that order should describe the state transitions that remain after the deliberation core has been simplified.

The fourth step should define that fixed-frame progress preorder.  It should package the monotone parts that the library already proves separately: case-frame stability, append-only record growth, seated-roster shrinkage, and phase or round advancement.  The point of that order is not novelty by itself.  It should replace a cluster of preservation theorems with one coherent state-transition description.

The fifth step is optional and should wait.  If the summary layer makes the current scalar termination measure look too coarse, then the library can replace it with a lexicographic potential.  Trace semantics and runtime-to-engine correspondence should come after that, because they depend more on the final shape of the proof language than on the current local invariants.

## Current Implementation

The first stage now spans `engine/Proofs/DeliberationSummaryCore.lean` and `engine/Proofs/DeliberationSummary.lean`.  The core file now carries the summary definition, the direct case-level correspondence with the executable resolution rule, and the lower council arithmetic that does not depend on later reachability layers.  The wrapper file keeps only the reachable summary bounds on vote counts, seated counts, and threshold positivity.

The second stage now spans `engine/Proofs/ViableOutcomesCore.lean` and `engine/Proofs/ViableOutcomes.lean`.  The core file carries the pure viability language on `DeliberationSummary`, the summary-only monotonicity lemmas, the state-level wrappers that do not depend on later reachability or removal arithmetic, and the summary-side closure language.  That closure language now includes both the `no_majority` predicate and the proof-side `closedResolution?` function for any closed deliberation result.  The layer includes case-level theorems that turn `currentResolution? = none` plus round completion and one executable closure reason into summary `no_majority` soundness and closure, and it also packages the direct summary equalities for substantive threshold closure and `no_majority` closure.  The higher file now goes well past raw summary identity.  It first proves a same-round `continueDeliberation` bridge for `DeliberationSummary`, then lifts vote and removal updates through that bridge into executable viability transport.  A vote for one side preserves that side's viability and preserves impossibility of the opposite side when the step stays in the same round.  A seated-member removal preserves impossibility for both substantive outcomes, and the public removal step now preserves total substantive non-viability under the same round condition.

The first part of the third stage now reaches four files.  `engine/Proofs/OutcomeSoundness.lean` now consumes both `engine/Proofs/DeliberationSummaryCore.lean` and `engine/Proofs/ViableOutcomesCore.lean`, so the direct `currentResolution?` soundness facts, the `no_majority` non-viability step, and the uniform summary-side characterization of closed `continueDeliberation` results sit in the lower summary layer instead of being reproved locally.  `engine/Proofs/NoStuck.lean` now also carries a summary-form liveness theorem: every reachable live deliberation state has current-round capacity in `DeliberationSummary`.  `engine/Proofs/ViableOutcomes.lean` then lifts the executable vote and removal updates through a same-round `continueDeliberation` bridge, while the core file continues to carry the pure summary facts: executable `currentResolution?` implies the corresponding summary-level viability fact, summary-level exhaustion implies executable non-resolution, and viability is preserved under the summary-level count flip that swaps the two substantive outcomes.  `engine/Proofs/Neutrality.lean` now consumes that lower summary form, so the reachable vote-flip theorem factors through `DeliberationSummary` instead of repeating the raw case arithmetic directly.

The fourth stage now has two files.  `engine/Proofs/Progress.lean` defines `fixedFrameProgress`, a source-anchored state relation that packages preservation of the source case frame, append-only admitted materials, shrinking seated-member identifiers, nondecreasing phase rank, and nondecreasing deliberation round.  It proves reflexivity and transitivity for that relation, proves that every successful public `step` establishes it, and packages the initialized-run form as the conjunction of the initialization frame and source-anchored progress from the initialized state.

`engine/Proofs/ProgressViability.lean` now adds the first deliberation-specific progress relation on top of that base.  The file defines `viableOutcomesShrink`, which says that if a substantive outcome is viable in the target state then it was already viable in the source state.  It then defines `sameRoundDeliberationProgress`, which combines `fixedFrameProgress`, same-round equality, and that shrink relation.  Both relations are reflexive and transitive.  The file proves that successful same-round council-vote and council-removal steps establish `sameRoundDeliberationProgress`, and it derives total substantive non-viability preservation from the shrink relation itself.

That relation now carries the first same-round inevitability theorem as well.  If a source state already has no viable substantive outcome and already satisfies one `no_majority` closure reason, then any later same-round progress state that completes the round is forced to summary `no_majority` closure.  The file then lifts that summary fact back to the executable boundary: `continueDeliberation` on the target state must close as `no_majority`.  The public council-vote and council-removal theorems now inherit that result as direct corollaries.  This remains narrower than full monotonicity of viability under `fixedFrameProgress` alone, but it completes the planned same-round closure layer without forcing vote counts into the global preorder.
