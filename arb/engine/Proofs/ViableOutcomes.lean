import Proofs.BoundedTermination
import Proofs.CouncilStatus
import Proofs.ViableOutcomesCore

namespace ArbProofs

/-
This file begins the viable-outcomes layer promised by
`docs/more-verification-notes.md`.

`Proofs.ViableOutcomesCore` now carries the summary-level viability
definitions, the pure summary theorems, and the state-level wrappers that do
not depend on later reachability or removal arithmetic.  This file keeps the
remaining correspondence lemmas that identify summary updates with the
intermediate deliberation states produced by the executable vote and removal
paths before `continueDeliberation` runs.
-/

def sameRoundVoteTransport (vote : String) (s t : ArbitrationState) : Prop :=
  (vote = "demonstrated" →
      ((deliberationSummary t).demonstratedViable ↔
        (deliberationSummary s).demonstratedViable) ∧
      (¬ (deliberationSummary s).notDemonstratedViable →
        ¬ (deliberationSummary t).notDemonstratedViable)) ∧
    (vote = "not_demonstrated" →
      ((deliberationSummary t).notDemonstratedViable ↔
        (deliberationSummary s).notDemonstratedViable) ∧
      (¬ (deliberationSummary s).demonstratedViable →
        ¬ (deliberationSummary t).demonstratedViable))

@[simp] private theorem trimString_demonstrated :
    trimString "demonstrated" = "demonstrated" := by
  native_decide

@[simp] private theorem trimString_not_demonstrated :
    trimString "not_demonstrated" = "not_demonstrated" := by
  native_decide

private theorem voteCountFor_append
    (xs ys : List CouncilVote)
    (value : String) :
    voteCountFor (xs ++ ys) value = voteCountFor xs value + voteCountFor ys value := by
  induction xs with
  | nil =>
      simp [voteCountFor]
  | cons vote votes ih =>
      simp [voteCountFor_cons, ih, Nat.add_assoc, Nat.add_comm]

private theorem deliberationSummary_congr
    {s t : ArbitrationState}
    (hVotes : t.case.council_votes = s.case.council_votes)
    (hMembers : t.case.council_members = s.case.council_members)
    (hRound : t.case.deliberation_round = s.case.deliberation_round)
    (hPolicy : t.policy = s.policy) :
    deliberationSummary t = deliberationSummary s := by
  have hSeatedCount : seatedCouncilMemberCount t.case = seatedCouncilMemberCount s.case := by
    simp [seatedCouncilMemberCount, seatedCouncilMembers, hMembers]
  have hCurrentVotes : currentRoundVotes t.case = currentRoundVotes s.case := by
    simp [currentRoundVotes, hVotes, hRound]
  apply DeliberationSummary.ext
  · simp [deliberationSummary, deliberationSummaryForCase, hPolicy]
  · simpa [deliberationSummary, deliberationSummaryForCase] using hSeatedCount
  · simpa [deliberationSummary, deliberationSummaryForCase] using congrArg List.length hCurrentVotes
  · simpa [deliberationSummary, deliberationSummaryForCase] using
      congrArg (fun votes => voteCountFor votes "demonstrated") hCurrentVotes
  · simpa [deliberationSummary, deliberationSummaryForCase] using
      congrArg (fun votes => voteCountFor votes "not_demonstrated") hCurrentVotes
  · simp [deliberationSummary, deliberationSummaryForCase, hRound]
  · simp [deliberationSummary, deliberationSummaryForCase, hPolicy]

private theorem continueDeliberation_preserves_policy
    (s t : ArbitrationState)
    (c : ArbitrationCase)
    (hCont : continueDeliberation s c = .ok t) :
    t.policy = s.policy := by
  unfold continueDeliberation at hCont
  by_cases hRoundComplete : (currentRoundVotes c).length = seatedCouncilMemberCount c
  · cases hResolution : currentResolution? c s.policy.required_votes_for_decision with
    | some resolution =>
        simp [hRoundComplete, hResolution, stateWithCase] at hCont
        cases hCont
        rfl
    | none =>
        by_cases hTooFew : seatedCouncilMemberCount c < s.policy.required_votes_for_decision
        · simp [hRoundComplete, hResolution, hTooFew, stateWithCase] at hCont
          cases hCont
          rfl
        · by_cases hLastRound : c.deliberation_round ≥ s.policy.max_deliberation_rounds
          · simp [hRoundComplete, hResolution, hTooFew, hLastRound, stateWithCase] at hCont
            cases hCont
            rfl
          · simp [hRoundComplete, hResolution, hTooFew, hLastRound, stateWithCase] at hCont
            cases hCont
            rfl
  · simp [hRoundComplete, stateWithCase] at hCont
    cases hCont
    rfl

private theorem continueDeliberation_same_round_preserves_deliberationSummary
    (s t : ArbitrationState)
    (c : ArbitrationCase)
    (hCont : continueDeliberation s c = .ok t)
    (hRound : t.case.deliberation_round = c.deliberation_round) :
    deliberationSummary t = deliberationSummary (stateWithCase s c) := by
  apply deliberationSummary_congr
  · exact continueDeliberation_preserves_council_votes s t c hCont
  · exact continueDeliberation_preserves_council_members s t c hCont
  · simpa [stateWithCase] using hRound
  · simpa [stateWithCase] using continueDeliberation_preserves_policy s t c hCont

theorem deliberationSummary_after_append_demonstrated_vote
    (s : ArbitrationState)
    (memberId rationale : String) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "demonstrated"
      rationale := trimString rationale
    } }
    deliberationSummary (stateWithCase s c1) =
      (deliberationSummary s).afterDemonstratedVote := by
  let vote : CouncilVote := {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  }
  apply DeliberationSummary.ext
  · rfl
  · rfl
  · simp [deliberationSummary, deliberationSummaryForCase,
      DeliberationSummary.afterDemonstratedVote, stateWithCase,
      currentRoundVotes, List.concat_eq_append, List.filter_append]
  · calc
      voteCountFor
          (currentRoundVotes { s.case with council_votes := s.case.council_votes.concat vote })
          "demonstrated" =
        voteCountFor (currentRoundVotes s.case ++ [vote]) "demonstrated" := by
          simp [vote, currentRoundVotes, List.concat_eq_append, List.filter_append]
      _ = voteCountFor (currentRoundVotes s.case) "demonstrated" +
            voteCountFor [vote] "demonstrated" := by
          simpa using voteCountFor_append (currentRoundVotes s.case) [vote] "demonstrated"
      _ = voteCountFor (currentRoundVotes s.case) "demonstrated" + 1 := by
          simp [voteCountFor, vote]
  · calc
      voteCountFor
          (currentRoundVotes { s.case with council_votes := s.case.council_votes.concat vote })
          "not_demonstrated" =
        voteCountFor (currentRoundVotes s.case ++ [vote]) "not_demonstrated" := by
          simp [vote, currentRoundVotes, List.concat_eq_append, List.filter_append]
      _ = voteCountFor (currentRoundVotes s.case) "not_demonstrated" +
            voteCountFor [vote] "not_demonstrated" := by
          simpa using voteCountFor_append (currentRoundVotes s.case) [vote] "not_demonstrated"
      _ = voteCountFor (currentRoundVotes s.case) "not_demonstrated" := by
          simp [voteCountFor, vote]
  · rfl
  · rfl

theorem deliberationSummary_after_append_not_demonstrated_vote
    (s : ArbitrationState)
    (memberId rationale : String) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "not_demonstrated"
      rationale := trimString rationale
    } }
    deliberationSummary (stateWithCase s c1) =
      (deliberationSummary s).afterNotDemonstratedVote := by
  let vote : CouncilVote := {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  }
  apply DeliberationSummary.ext
  · rfl
  · rfl
  · simp [deliberationSummary, deliberationSummaryForCase,
      DeliberationSummary.afterNotDemonstratedVote, stateWithCase,
      currentRoundVotes, List.concat_eq_append, List.filter_append]
  · calc
      voteCountFor
          (currentRoundVotes { s.case with council_votes := s.case.council_votes.concat vote })
          "demonstrated" =
        voteCountFor (currentRoundVotes s.case ++ [vote]) "demonstrated" := by
          simp [vote, currentRoundVotes, List.concat_eq_append, List.filter_append]
      _ = voteCountFor (currentRoundVotes s.case) "demonstrated" +
            voteCountFor [vote] "demonstrated" := by
          simpa using voteCountFor_append (currentRoundVotes s.case) [vote] "demonstrated"
      _ = voteCountFor (currentRoundVotes s.case) "demonstrated" := by
          simp [voteCountFor, vote]
  · calc
      voteCountFor
          (currentRoundVotes { s.case with council_votes := s.case.council_votes.concat vote })
          "not_demonstrated" =
        voteCountFor (currentRoundVotes s.case ++ [vote]) "not_demonstrated" := by
          simp [vote, currentRoundVotes, List.concat_eq_append, List.filter_append]
      _ = voteCountFor (currentRoundVotes s.case) "not_demonstrated" +
            voteCountFor [vote] "not_demonstrated" := by
          simpa using voteCountFor_append (currentRoundVotes s.case) [vote] "not_demonstrated"
      _ = voteCountFor (currentRoundVotes s.case) "not_demonstrated" + 1 := by
          simp [voteCountFor, vote]
  · rfl
  · rfl

theorem deliberationSummary_after_seated_member_removal
    (s : ArbitrationState)
    (memberId status : String)
    (hUnique : councilIdsUnique s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hStatus : trimString status ≠ "seated") :
    let c1 := { s.case with council_members := s.case.council_members.map (fun member =>
      if member.member_id = memberId then
        { member with status := trimString status }
      else
        member) }
    deliberationSummary (stateWithCase s c1) =
      (deliberationSummary s).afterSeatedMemberRemoval := by
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hSeatedCount :
      seatedCouncilMemberCount c1 + 1 = seatedCouncilMemberCount s.case := by
    simpa [c1] using
      seatedCouncilMemberCount_removeUnvotedCouncilMember
        s.case memberId status hUnique hSeated hStatus
  have hSeatedPred : seatedCouncilMemberCount c1 = seatedCouncilMemberCount s.case - 1 := by
    omega
  apply DeliberationSummary.ext
  · rfl
  · simpa [deliberationSummary, deliberationSummaryForCase,
      DeliberationSummary.afterSeatedMemberRemoval, stateWithCase, c1] using hSeatedPred
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem deliberationSummary_after_append_demonstrated_vote_demonstratedViable_iff_of_fresh_seated
    (s : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "demonstrated"
      rationale := trimString rationale
    } }
    (deliberationSummary (stateWithCase s c1)).demonstratedViable ↔
      (deliberationSummary s).demonstratedViable := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  } }
  change (deliberationSummary (stateWithCase s c1)).demonstratedViable ↔
    (deliberationSummary s).demonstratedViable
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  rw [deliberationSummary_after_append_demonstrated_vote s memberId rationale]
  exact
    (deliberationSummary s).afterDemonstratedVote_demonstratedViable_iff hCapacity

theorem deliberationSummary_after_append_demonstrated_vote_notDemonstratedViable_implies_of_fresh_seated
    (s : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "demonstrated"
      rationale := trimString rationale
    } }
    (deliberationSummary (stateWithCase s c1)).notDemonstratedViable →
      (deliberationSummary s).notDemonstratedViable := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  } }
  change (deliberationSummary (stateWithCase s c1)).notDemonstratedViable →
    (deliberationSummary s).notDemonstratedViable
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  rw [deliberationSummary_after_append_demonstrated_vote s memberId rationale]
  exact
    (deliberationSummary s).afterDemonstratedVote_notDemonstratedViable_implies hCapacity

theorem deliberationSummary_after_append_demonstrated_vote_preserves_notDemonstrated_impossibility
    (s : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hNotViable : ¬ (deliberationSummary s).notDemonstratedViable) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "demonstrated"
      rationale := trimString rationale
    } }
    ¬ (deliberationSummary (stateWithCase s c1)).notDemonstratedViable := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  } }
  change ¬ (deliberationSummary (stateWithCase s c1)).notDemonstratedViable
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  rw [deliberationSummary_after_append_demonstrated_vote s memberId rationale]
  intro hAfter
  exact hNotViable <|
    (deliberationSummary s).afterDemonstratedVote_notDemonstratedViable_implies hCapacity hAfter

theorem deliberationSummary_after_append_not_demonstrated_vote_notDemonstratedViable_iff_of_fresh_seated
    (s : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "not_demonstrated"
      rationale := trimString rationale
    } }
    (deliberationSummary (stateWithCase s c1)).notDemonstratedViable ↔
      (deliberationSummary s).notDemonstratedViable := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  } }
  change (deliberationSummary (stateWithCase s c1)).notDemonstratedViable ↔
    (deliberationSummary s).notDemonstratedViable
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  rw [deliberationSummary_after_append_not_demonstrated_vote s memberId rationale]
  exact
    (deliberationSummary s).afterNotDemonstratedVote_notDemonstratedViable_iff hCapacity

theorem deliberationSummary_after_append_not_demonstrated_vote_demonstratedViable_implies_of_fresh_seated
    (s : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "not_demonstrated"
      rationale := trimString rationale
    } }
    (deliberationSummary (stateWithCase s c1)).demonstratedViable →
      (deliberationSummary s).demonstratedViable := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  } }
  change (deliberationSummary (stateWithCase s c1)).demonstratedViable →
    (deliberationSummary s).demonstratedViable
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  rw [deliberationSummary_after_append_not_demonstrated_vote s memberId rationale]
  exact
    (deliberationSummary s).afterNotDemonstratedVote_demonstratedViable_implies hCapacity

theorem deliberationSummary_after_append_not_demonstrated_vote_preserves_demonstrated_impossibility
    (s : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hNotViable : ¬ (deliberationSummary s).demonstratedViable) :
    let c1 := { s.case with council_votes := s.case.council_votes.concat {
      member_id := memberId
      round := s.case.deliberation_round
      vote := "not_demonstrated"
      rationale := trimString rationale
    } }
    ¬ (deliberationSummary (stateWithCase s c1)).demonstratedViable := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  } }
  change ¬ (deliberationSummary (stateWithCase s c1)).demonstratedViable
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  rw [deliberationSummary_after_append_not_demonstrated_vote s memberId rationale]
  intro hAfter
  exact hNotViable <|
    (deliberationSummary s).afterNotDemonstratedVote_demonstratedViable_implies hCapacity hAfter

theorem deliberationSummary_after_seated_member_removal_demonstratedViable_implies_of_fresh_seated
    (s : ArbitrationState)
    (memberId status : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hStatus : trimString status ≠ "seated") :
    let c1 := { s.case with council_members := s.case.council_members.map (fun member =>
      if member.member_id = memberId then
        { member with status := trimString status }
      else
        member) }
    (deliberationSummary (stateWithCase s c1)).demonstratedViable →
      (deliberationSummary s).demonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  have hImp :
      (deliberationSummary (stateWithCase s c1)).demonstratedViable →
        (deliberationSummary s).demonstratedViable := by
    rw [deliberationSummary_after_seated_member_removal s memberId status hUnique hSeated hStatus]
    exact (deliberationSummary s).afterSeatedMemberRemoval_demonstratedViable_implies hCapacity
  simpa [c1] using hImp

theorem deliberationSummary_after_seated_member_removal_notDemonstratedViable_implies_of_fresh_seated
    (s : ArbitrationState)
    (memberId status : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hStatus : trimString status ≠ "seated") :
    let c1 := { s.case with council_members := s.case.council_members.map (fun member =>
      if member.member_id = memberId then
        { member with status := trimString status }
      else
        member) }
    (deliberationSummary (stateWithCase s c1)).notDemonstratedViable →
      (deliberationSummary s).notDemonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  have hImp :
      (deliberationSummary (stateWithCase s c1)).notDemonstratedViable →
        (deliberationSummary s).notDemonstratedViable := by
    rw [deliberationSummary_after_seated_member_removal s memberId status hUnique hSeated hStatus]
    exact (deliberationSummary s).afterSeatedMemberRemoval_notDemonstratedViable_implies hCapacity
  simpa [c1] using hImp

theorem deliberationSummary_after_seated_member_removal_preserves_demonstrated_impossibility
    (s : ArbitrationState)
    (memberId status : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hStatus : trimString status ≠ "seated")
    (hNotViable : ¬ (deliberationSummary s).demonstratedViable) :
    let c1 := { s.case with council_members := s.case.council_members.map (fun member =>
      if member.member_id = memberId then
        { member with status := trimString status }
      else
        member) }
    ¬ (deliberationSummary (stateWithCase s c1)).demonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  have hImp :
      ¬ (deliberationSummary (stateWithCase s c1)).demonstratedViable := by
    rw [deliberationSummary_after_seated_member_removal s memberId status hUnique hSeated hStatus]
    intro hAfter
    exact hNotViable <|
      (deliberationSummary s).afterSeatedMemberRemoval_demonstratedViable_implies hCapacity hAfter
  simpa [c1] using hImp

theorem deliberationSummary_after_seated_member_removal_preserves_notDemonstrated_impossibility
    (s : ArbitrationState)
    (memberId status : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hStatus : trimString status ≠ "seated")
    (hNotViable : ¬ (deliberationSummary s).notDemonstratedViable) :
    let c1 := { s.case with council_members := s.case.council_members.map (fun member =>
      if member.member_id = memberId then
        { member with status := trimString status }
      else
        member) }
    ¬ (deliberationSummary (stateWithCase s c1)).notDemonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hCapacity :
      (deliberationSummary s).current_round_vote_count <
        (deliberationSummary s).seated_count :=
    deliberationSummary_current_round_vote_count_lt_seated_count_of_fresh_seated
      s memberId hUnique hIntegrity hSeated hFresh
  have hImp :
      ¬ (deliberationSummary (stateWithCase s c1)).notDemonstratedViable := by
    rw [deliberationSummary_after_seated_member_removal s memberId status hUnique hSeated hStatus]
    intro hAfter
    exact hNotViable <|
      (deliberationSummary s).afterSeatedMemberRemoval_notDemonstratedViable_implies hCapacity hAfter
  simpa [c1] using hImp

theorem continueDeliberation_after_append_demonstrated_vote_same_round_demonstratedViable_iff
    (s t : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hCont :
      let c1 := { s.case with council_votes := s.case.council_votes.concat {
        member_id := memberId
        round := s.case.deliberation_round
        vote := "demonstrated"
        rationale := trimString rationale
      } }
      continueDeliberation s c1 = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round) :
    (deliberationSummary t).demonstratedViable ↔
      (deliberationSummary s).demonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  } }
  have hMid :
      (deliberationSummary (stateWithCase s c1)).demonstratedViable ↔
        (deliberationSummary s).demonstratedViable :=
    deliberationSummary_after_append_demonstrated_vote_demonstratedViable_iff_of_fresh_seated
      s memberId rationale hUnique hIntegrity hSeated hFresh
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  simpa [hSummaryEq] using hMid

theorem continueDeliberation_after_append_demonstrated_vote_same_round_preserves_notDemonstrated_impossibility
    (s t : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hCont :
      let c1 := { s.case with council_votes := s.case.council_votes.concat {
        member_id := memberId
        round := s.case.deliberation_round
        vote := "demonstrated"
        rationale := trimString rationale
      } }
      continueDeliberation s c1 = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hNotViable : ¬ (deliberationSummary s).notDemonstratedViable) :
    ¬ (deliberationSummary t).notDemonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  } }
  have hMid :
      ¬ (deliberationSummary (stateWithCase s c1)).notDemonstratedViable :=
    deliberationSummary_after_append_demonstrated_vote_preserves_notDemonstrated_impossibility
      s memberId rationale hUnique hIntegrity hSeated hFresh hNotViable
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  intro hAfter
  exact hMid (by simpa [hSummaryEq] using hAfter)

theorem continueDeliberation_after_append_demonstrated_vote_same_round_notDemonstratedViable_implies
    (s t : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hCont :
      let c1 := { s.case with council_votes := s.case.council_votes.concat {
        member_id := memberId
        round := s.case.deliberation_round
        vote := "demonstrated"
        rationale := trimString rationale
      } }
      continueDeliberation s c1 = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hViable : (deliberationSummary t).notDemonstratedViable) :
    (deliberationSummary s).notDemonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "demonstrated"
    rationale := trimString rationale
  } }
  have hMid :
      (deliberationSummary (stateWithCase s c1)).notDemonstratedViable →
        (deliberationSummary s).notDemonstratedViable :=
    deliberationSummary_after_append_demonstrated_vote_notDemonstratedViable_implies_of_fresh_seated
      s memberId rationale hUnique hIntegrity hSeated hFresh
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  exact hMid (by simpa [hSummaryEq] using hViable)

theorem continueDeliberation_after_append_not_demonstrated_vote_same_round_notDemonstratedViable_iff
    (s t : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hCont :
      let c1 := { s.case with council_votes := s.case.council_votes.concat {
        member_id := memberId
        round := s.case.deliberation_round
        vote := "not_demonstrated"
        rationale := trimString rationale
      } }
      continueDeliberation s c1 = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round) :
    (deliberationSummary t).notDemonstratedViable ↔
      (deliberationSummary s).notDemonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  } }
  have hMid :
      (deliberationSummary (stateWithCase s c1)).notDemonstratedViable ↔
        (deliberationSummary s).notDemonstratedViable :=
    deliberationSummary_after_append_not_demonstrated_vote_notDemonstratedViable_iff_of_fresh_seated
      s memberId rationale hUnique hIntegrity hSeated hFresh
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  simpa [hSummaryEq] using hMid

theorem continueDeliberation_after_append_not_demonstrated_vote_same_round_preserves_demonstrated_impossibility
    (s t : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hCont :
      let c1 := { s.case with council_votes := s.case.council_votes.concat {
        member_id := memberId
        round := s.case.deliberation_round
        vote := "not_demonstrated"
        rationale := trimString rationale
      } }
      continueDeliberation s c1 = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hNotViable : ¬ (deliberationSummary s).demonstratedViable) :
    ¬ (deliberationSummary t).demonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  } }
  have hMid :
      ¬ (deliberationSummary (stateWithCase s c1)).demonstratedViable :=
    deliberationSummary_after_append_not_demonstrated_vote_preserves_demonstrated_impossibility
      s memberId rationale hUnique hIntegrity hSeated hFresh hNotViable
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  intro hAfter
  exact hMid (by simpa [hSummaryEq] using hAfter)

theorem continueDeliberation_after_append_not_demonstrated_vote_same_round_demonstratedViable_implies
    (s t : ArbitrationState)
    (memberId rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hCont :
      let c1 := { s.case with council_votes := s.case.council_votes.concat {
        member_id := memberId
        round := s.case.deliberation_round
        vote := "not_demonstrated"
        rationale := trimString rationale
      } }
      continueDeliberation s c1 = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hViable : (deliberationSummary t).demonstratedViable) :
    (deliberationSummary s).demonstratedViable := by
  let c1 : ArbitrationCase := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := "not_demonstrated"
    rationale := trimString rationale
  } }
  have hMid :
      (deliberationSummary (stateWithCase s c1)).demonstratedViable →
        (deliberationSummary s).demonstratedViable :=
    deliberationSummary_after_append_not_demonstrated_vote_demonstratedViable_implies_of_fresh_seated
      s memberId rationale hUnique hIntegrity hSeated hFresh
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  exact hMid (by simpa [hSummaryEq] using hViable)

theorem step_submit_council_vote_same_round_supports_submitted_outcome
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "submit_council_vote")
    (hStep : step { state := s, action := action } = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case) :
    ∃ vote, sameRoundVoteTransport vote s t := by
  rcases step_submit_council_vote_details s t action hType hStep with
    ⟨memberId, vote, rationale, _hPhase, hSeated, hFresh, hCont⟩
  refine ⟨vote, ?_⟩
  constructor
  · intro hVote
    subst hVote
    have hCont' :
        let c1 := { s.case with council_votes := s.case.council_votes.concat {
          member_id := memberId
          round := s.case.deliberation_round
          vote := "demonstrated"
          rationale := trimString rationale
        } }
        continueDeliberation s c1 = .ok t := by
      simpa using hCont
    constructor
    · exact continueDeliberation_after_append_demonstrated_vote_same_round_demonstratedViable_iff
        s t memberId rationale hUnique hIntegrity hSeated hFresh hCont' hSameRound
    · intro hNotViable
      exact continueDeliberation_after_append_demonstrated_vote_same_round_preserves_notDemonstrated_impossibility
        s t memberId rationale hUnique hIntegrity hSeated hFresh hCont' hSameRound hNotViable
  · intro hVote
    subst hVote
    have hCont' :
        let c1 := { s.case with council_votes := s.case.council_votes.concat {
          member_id := memberId
          round := s.case.deliberation_round
          vote := "not_demonstrated"
          rationale := trimString rationale
        } }
        continueDeliberation s c1 = .ok t := by
      simpa using hCont
    constructor
    · exact continueDeliberation_after_append_not_demonstrated_vote_same_round_notDemonstratedViable_iff
        s t memberId rationale hUnique hIntegrity hSeated hFresh hCont' hSameRound
    · intro hNotViable
      exact continueDeliberation_after_append_not_demonstrated_vote_same_round_preserves_demonstrated_impossibility
        s t memberId rationale hUnique hIntegrity hSeated hFresh hCont' hSameRound hNotViable

theorem step_remove_council_member_same_round_preserves_demonstrated_impossibility
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "remove_council_member")
    (hStep : step { state := s, action := action } = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hNotViable : ¬ (deliberationSummary s).demonstratedViable) :
    ¬ (deliberationSummary t).demonstratedViable := by
  rcases step_remove_council_member_details s t action hType hStep with
    ⟨memberId, status, _hPhase, hSeated, hFresh, hStatus, hCont⟩
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hMid :
      ¬ (deliberationSummary (stateWithCase s c1)).demonstratedViable :=
    deliberationSummary_after_seated_member_removal_preserves_demonstrated_impossibility
      s memberId status hUnique hIntegrity hSeated hFresh hStatus hNotViable
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  intro hAfter
  exact hMid (by simpa [hSummaryEq] using hAfter)

theorem step_remove_council_member_same_round_demonstratedViable_implies
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "remove_council_member")
    (hStep : step { state := s, action := action } = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hViable : (deliberationSummary t).demonstratedViable) :
    (deliberationSummary s).demonstratedViable := by
  rcases step_remove_council_member_details s t action hType hStep with
    ⟨memberId, status, _hPhase, hSeated, hFresh, hStatus, hCont⟩
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hMid :
      (deliberationSummary (stateWithCase s c1)).demonstratedViable →
        (deliberationSummary s).demonstratedViable :=
    deliberationSummary_after_seated_member_removal_demonstratedViable_implies_of_fresh_seated
      s memberId status hUnique hIntegrity hSeated hFresh hStatus
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  exact hMid (by simpa [hSummaryEq] using hViable)

theorem step_remove_council_member_same_round_preserves_notDemonstrated_impossibility
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "remove_council_member")
    (hStep : step { state := s, action := action } = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hNotViable : ¬ (deliberationSummary s).notDemonstratedViable) :
    ¬ (deliberationSummary t).notDemonstratedViable := by
  rcases step_remove_council_member_details s t action hType hStep with
    ⟨memberId, status, _hPhase, hSeated, hFresh, hStatus, hCont⟩
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hMid :
      ¬ (deliberationSummary (stateWithCase s c1)).notDemonstratedViable :=
    deliberationSummary_after_seated_member_removal_preserves_notDemonstrated_impossibility
      s memberId status hUnique hIntegrity hSeated hFresh hStatus hNotViable
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  intro hAfter
  exact hMid (by simpa [hSummaryEq] using hAfter)

theorem step_remove_council_member_same_round_notDemonstratedViable_implies
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "remove_council_member")
    (hStep : step { state := s, action := action } = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hViable : (deliberationSummary t).notDemonstratedViable) :
    (deliberationSummary s).notDemonstratedViable := by
  rcases step_remove_council_member_details s t action hType hStep with
    ⟨memberId, status, _hPhase, hSeated, hFresh, hStatus, hCont⟩
  let c1 : ArbitrationCase := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hMid :
      (deliberationSummary (stateWithCase s c1)).notDemonstratedViable →
        (deliberationSummary s).notDemonstratedViable :=
    deliberationSummary_after_seated_member_removal_notDemonstratedViable_implies_of_fresh_seated
      s memberId status hUnique hIntegrity hSeated hFresh hStatus
  have hSummaryEq : deliberationSummary t = deliberationSummary (stateWithCase s c1) := by
    exact continueDeliberation_same_round_preserves_deliberationSummary s t c1
      hCont
      (by simpa [c1] using hSameRound)
  exact hMid (by simpa [hSummaryEq] using hViable)

theorem step_remove_council_member_same_round_preserves_noSubstantiveOutcomeViable
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "remove_council_member")
    (hStep : step { state := s, action := action } = .ok t)
    (hSameRound : t.case.deliberation_round = s.case.deliberation_round)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hNoViable : (deliberationSummary s).noSubstantiveOutcomeViable) :
    (deliberationSummary t).noSubstantiveOutcomeViable := by
  constructor
  · exact step_remove_council_member_same_round_preserves_demonstrated_impossibility
      s t action hType hStep hSameRound hUnique hIntegrity hNoViable.1
  · exact step_remove_council_member_same_round_preserves_notDemonstrated_impossibility
      s t action hType hStep hSameRound hUnique hIntegrity hNoViable.2

end ArbProofs
