# Verification

## Purpose

This document is the canonical verification record for the Lean engine.  It replaces the earlier split plan and findings notes.  It states what the current proof library establishes, which proof-driven findings changed the executable semantics, and which further results now look worth pursuing.

## Current Results

The current Lean library proves the initial public claims about the engine over reachable executions rather than isolated examples.  The published [theorem index](theorems.md) and [proof statistics](proofstats.md) remain the best inventory of the full surface.  The table below records the results that matter most to the procedure's meaning.

| Area | Main theorem family | Meaning |
|---|---|---|
| Merits structure | `reachable_phaseShape` | Every reachable state preserves the intended merits sequence. |
| Procedural parity | `reachable_proceduralParity` | The engine does not give one side extra merits turns. |
| Case immutability | `initialized_run_preserves_caseFrame` | A successful run keeps one proposition, one policy, and one council identity set. |
| Aggregate material caps | `reachable_materialLimitsRespected` | Reachable states respect the cumulative exhibit and report limits. |
| Outcome soundness | `reachable_closed_demonstrated_sound`, `reachable_closed_not_demonstrated_sound`, `reachable_closed_no_majority_sound` | Closed outcomes follow from the recorded deliberation state and the executable closure conditions. |
| Live-state liveness | `reachable_nonclosed_has_nextOpportunity` | A reachable non-closed case always has a next public opportunity. |
| Council integrity and status monotonicity | `reachable_councilVoteIntegrity`, `step_shrinks_seatedCouncilMemberIds`, `step_introduces_newCouncilVotes_only_from_seated` | Stored votes stay well formed, seated membership only shrinks, and new votes come from seated members in the source state. |
| Record provenance and append-only growth | `reachable_recordProvenance`, `stepReachableFrom_materialsExtend` | Admitted materials come from allowed phase-role origins, and later successful steps only append to those lists. |
| Fixed-frame progress | `fixedFrameProgress`, `step_establishes_fixedFrameProgress`, `initialized_run_progresses_in_initial_frame` | Successful steps stay inside one case frame while admitted materials only append, seated council identifiers only shrink, phase rank never falls, and deliberation round never decreases. |
| Bounded termination | `stepPath_length_le_initializedBudget` | Successful public runs from initialization are finite, with an explicit procedural upper bound. |
| Deliberation neutrality | `reachable_currentResolution_is_neutral_under_vote_flip` | Flipping every current-round substantive vote flips the substantive outcome in the same way. |

Taken together, these theorems say that the engine keeps the procedure in order, preserves the record's integrity, and closes cases only in ways justified by the stored deliberation state.  They also say that the engine neither strands a live case nor admits an infinite successful public run.  The initial public verification agenda is therefore complete.

## Verification Program

The proof work followed a staged order because later claims depended on earlier invariants.  That order still matters as a map of the library, even though the stages are now complete.  The table below records the finished agenda and the public result each stage delivered.

| Stage | Theorem family | Status | Public result |
|---|---|---|---|
| 1 | Case immutability after initialization | complete | The engine adjudicates one case under one fixed policy and council identity set. |
| 2 | Outcome soundness | complete | Reachable closed outcomes are justified by the recorded vote state and closure conditions. |
| 3 | No stuck reachable state | complete | Every reachable non-closed state has a next opportunity. |
| 4 | Council vote integrity | complete | Reachable deliberation records are well formed, and public steps never restore removed seats or admit votes from non-seated members. |
| 5 | Record provenance and monotonicity | complete | Admitted materials have allowed origins and later successful steps do not rewrite earlier admitted entries. |
| 6 | Bounded termination | complete | Every successful public run from initialization has an explicit finite upper bound. |
| 7 | Deliberation neutrality | complete | The aggregation rule is symmetric under the current-round vote flip over the validated policy space. |

This stage sequence is now history rather than a pending work queue.  It still explains why the library has its present shape, because the global results sit on top of earlier preservation and reachability layers.  Further work should begin only with a claim that adds new structure or a stronger public guarantee.

## Findings Exposed by Proof Work

The proof work changed the engine in three material ways.  Two findings exposed concrete procedural defects in the executable semantics.  The third exposed a mismatch between a planned theorem and the earlier validated policy space.

| Area | Earlier issue | Resolution | Why it mattered |
|---|---|---|---|
| Initialization | `initializeCase` accepted duplicate council `member_id` values. | Initialization now rejects duplicate identifiers. | `member_id` is the seat identity key for voting, removal, and next-opportunity selection. |
| Deliberation | `removeCouncilMember` allowed removal of a current-round voter. | Deliberation now rejects removal after a current-round vote. | The old rule could advance the round before every remaining seated member had voted. |
| Aggregation policy | Non-strict thresholds allowed dual-threshold deliberation states. | Policy validation now requires `2 * required_votes_for_decision > council_size`. | The neutrality theorem fails when both substantive outcomes can satisfy the threshold at once. |

### Council Identity

The deliberation model already treated `member_id` as the identity of a council seat.  Voting, member removal, and next-opportunity selection all keyed their logic to that field.  Without uniqueness, one vote could block two seats for a round and one removal could rewrite several seats at once, so the proof work made the implicit identity rule explicit at initialization.

### Round Completion After Removal

The old round-completion rule compared the length of `currentRoundVotes` with the current seated-member count.  That arithmetic is sound only if both sides of the equation refer to the same set of seats.  In the old engine, a member could vote and then be removed, which made it possible to advance from round one to round two before every remaining seated member had voted.  The direct counterexample used a five-member council with a four-vote threshold: `C1` voted and was removed, `C2` through `C4` voted, and the engine advanced even though `C5` had not voted.  The repair kept the simpler deliberation model and rejected removal of a member who had already cast a current-round vote.

### Neutrality and Strict Majority

`currentResolution?` checks `demonstrated` before `not_demonstrated`.  That ordering is neutral only when both substantive outcomes cannot reach the threshold at the same time.  Under the earlier validator, a two-member council with a one-vote threshold allowed one `demonstrated` vote and one `not_demonstrated` vote to satisfy both thresholds at once, so flipping the votes did not flip the result.  The validator now requires a strict majority, which removes that overlap and turns deliberation neutrality into a theorem over the whole validated policy space.

## Limits

Lean proves properties of the executable procedure and of the stored case record.  It does not prove that an advocate searched well, reasoned honestly, or exercised sound judgment, and it does not prove the truth of the proposition.  It also does not prove that the evidence standard was wise or substantively adequate, because that standard remains policy text rather than a formal semantics.

## Next Results

The proof library now has two organizing layers beyond the original public agenda: the deliberation summary and viability layer, and the fixed-frame progress preorder with its same-round deliberation refinement.  The lower import split now reaches outcome soundness, one liveness fact, and the pure viability language.  `engine/Proofs/DeliberationSummaryCore.lean` carries the pure summary arithmetic and the direct `currentResolution?` correspondence facts.  `engine/Proofs/ViableOutcomesCore.lean` now carries summary non-viability, the summary-side closure language for `no_majority`, the proof-side `closedResolution?` function for any closed deliberation result, and the pure viability monotonicity lemmas.  `OutcomeSoundness.lean` now uses that layer both to prove the `no_majority` soundness branch and to characterize every closed `continueDeliberation` result in summary terms.  `engine/Proofs/NoStuck.lean` also proves the summary-form round-capacity fact for reachable live deliberation states.  `engine/Proofs/ViableOutcomes.lean` now adds a same-round `continueDeliberation` bridge for `DeliberationSummary`, lifts vote and removal updates through that bridge, and proves the executable same-round transport lemmas that control substantive viability and impossibility at the final state.

`engine/Proofs/ProgressViability.lean` now builds the first genuine same-round deliberation relation on top of that executable layer.  It defines `viableOutcomesShrink`, which says that every substantive outcome viable in the target summary was already viable in the source summary.  It then defines `sameRoundDeliberationProgress`, which packages `fixedFrameProgress`, equality of deliberation round, and viability shrink.  The file proves reflexivity and transitivity for those proof-side objects, proves that successful same-round council-vote and council-removal steps establish them, and uses them to lift the first inevitability theorem back to the executable boundary.  Once a same-round source state already has no viable substantive outcome and already satisfies one `no_majority` closure reason, any later same-round progress state that completes the round is forced to summary `no_majority` closure, and `continueDeliberation` on that target state must close as `no_majority`.

That completes the summary, viability, and same-round progress agenda that grew out of the original verification program.  The remaining questions are optional again.  One option is to decide whether the global preorder should absorb some vote-side data instead of leaving it in the same-round refinement.  Another is to return to the deferred work on a more structured termination measure or trace semantics.  Those are new directions, not missing pieces in the present proof line.
