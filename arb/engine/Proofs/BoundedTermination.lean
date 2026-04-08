import Proofs.NoStuck
import Proofs.DeliberationSummaryCore
import Proofs.RecordProvenance

namespace ArbProofs

/-
This file begins Stage 6 of the verification plan: bounded termination.

The proof is not complete yet.  What is complete here is the framework the
final theorem will need:

1. a remaining-step budget for merits and deliberation;
2. an indexed public-run relation that records the number of successful steps;
3. small list facts about phase-local progress; and
4. preservation lemmas showing that merits actions leave the deliberation
   budget unchanged.

That groundwork matters.  The eventual bounded-termination proof should not
reconstruct these definitions inside one long induction.  It should state its
measure once, prove the local decrease lemmas cleanly, and then lift them to
an indexed run bound.
-/

def remainingMeritsSteps (c : ArbitrationCase) : Nat :=
  match c.phase with
  | "openings" => if c.openings.isEmpty then 8 else 7
  | "arguments" => if c.arguments.isEmpty then 6 else 5
  | "rebuttals" => 4
  | "surrebuttals" => 3
  | "closings" => if c.closings.isEmpty then 2 else 1
  | _ => 0

def remainingDeliberationSteps (s : ArbitrationState) : Nat :=
  (s.policy.max_deliberation_rounds - s.case.deliberation_round) * s.policy.council_size +
    (seatedCouncilMemberCount s.case - (currentRoundVotes s.case).length)

def remainingStepBudget (s : ArbitrationState) : Nat :=
  if s.case.phase = "closed" then
    0
  else
    remainingMeritsSteps s.case + remainingDeliberationSteps s

/-
`Reachable` says only that some successful run exists.  Bounded termination
needs the stronger indexed relation below, because the final theorem has to
compare a run length against the initialized budget.
-/
inductive StepPath (start : ArbitrationState) : Nat → ArbitrationState → Prop where
  | refl : StepPath start 0 start
  | step (n : Nat) (s t : ArbitrationState) (action : CourtAction)
      (hs : StepPath start n s)
      (h : step { state := s, action := action } = .ok t) :
      StepPath start (n + 1) t

/--
If a list is nonempty, appending one element yields a list of length at least
two.

This is the local list fact behind the second opening, the second argument,
and the second closing.
-/
theorem concat_length_ge_two_of_isEmpty_false
    {α : Type}
    (xs : List α)
    (x : α)
    (hNonempty : xs.isEmpty = false) :
    2 ≤ (xs.concat x).length := by
  cases xs with
  | nil =>
      simp at hNonempty
  | cons head tail =>
      simp

/--
If the length is not at least one, the list is empty.

The later local decrease proofs will use this fact to turn a failed progress
test into a concrete first-filing case.
-/
theorem eq_nil_of_not_one_le_length
    {α : Type}
    (xs : List α)
    (hLen : ¬ 1 ≤ xs.length) :
    xs = [] := by
  cases xs with
  | nil =>
      rfl
  | cons head tail =>
      simp at hLen

/--
If the length is at least one, the list is nonempty.
-/
theorem ne_nil_of_one_le_length
    {α : Type}
    (xs : List α)
    (hLen : 1 ≤ xs.length) :
    xs ≠ [] := by
  cases xs with
  | nil =>
      simp at hLen
  | cons head tail =>
      simp

/--
Merits actions leave the deliberation budget unchanged.

They do not change the stored vote list, the deliberation round, or the
current council roster.  The later bounded-termination proof will use these
lemmas to separate merits progress from deliberation progress.
-/
theorem remainingDeliberationSteps_addFiling
    (s : ArbitrationState)
    (phase role text : String) :
    remainingDeliberationSteps (stateWithCase s (addFiling s.case phase role text)) =
      remainingDeliberationSteps s := by
  have hRound := addFiling_preserves_deliberation_round s.case phase role text
  have hMembers := addFiling_preserves_council_members s.case phase role text
  have hVotes := addFiling_preserves_council_votes s.case phase role text
  unfold remainingDeliberationSteps seatedCouncilMemberCount seatedCouncilMembers currentRoundVotes
  simp [stateWithCase, hRound, hMembers, hVotes]

theorem remainingDeliberationSteps_appendSupplementalMaterials
    (s : ArbitrationState)
    (offered : List OfferedFile)
    (reports : List TechnicalReport) :
    remainingDeliberationSteps
        (stateWithCase s (appendSupplementalMaterials s.case offered reports)) =
      remainingDeliberationSteps s := by
  unfold remainingDeliberationSteps seatedCouncilMemberCount seatedCouncilMembers currentRoundVotes
  simp [stateWithCase, appendSupplementalMaterials]

theorem remainingDeliberationSteps_phase_update
    (s : ArbitrationState)
    (phase : String) :
    remainingDeliberationSteps (stateWithCase s { s.case with phase := phase }) =
      remainingDeliberationSteps s := by
  unfold remainingDeliberationSteps seatedCouncilMemberCount seatedCouncilMembers currentRoundVotes
  simp [stateWithCase]

/--
Away from `closed`, the step budget splits into its merits and deliberation
components.

This rewrite is convenient because the later local decrease theorems will
usually reason about only one component at a time.
-/
theorem remainingStepBudget_of_phase_ne_closed
    (s : ArbitrationState)
    (hPhase : s.case.phase ≠ "closed") :
    remainingStepBudget s =
      remainingMeritsSteps s.case + remainingDeliberationSteps s := by
  simp [remainingStepBudget, hPhase]

/--
Successful policy validation guarantees that the deliberation-round limit is
positive.

The bounded-termination proof needs this arithmetic fact at initialization.
Without it, the first-round deliberation budget does not collapse to the
expected closed form.
-/
theorem validatePolicy_ok_implies_max_deliberation_rounds_positive
    (p : ArbitrationPolicy)
    (hPolicy : validatePolicy p = .ok PUnit.unit) :
    0 < p.max_deliberation_rounds := by
  unfold validatePolicy at hPolicy
  by_cases hCouncil : p.council_size = 0
  · simp [hCouncil] at hPolicy
    cases hPolicy
  · by_cases hEvidence : trimString p.evidence_standard = ""
    · simp [hCouncil, hEvidence] at hPolicy
      cases hPolicy
    · by_cases hVotes : p.required_votes_for_decision = 0
      · simp [hCouncil, hEvidence, hVotes] at hPolicy
        cases hPolicy
      · by_cases hTooLarge : p.required_votes_for_decision > p.council_size
        · simp [hCouncil, hEvidence, hVotes, hTooLarge] at hPolicy
          cases hPolicy
        · by_cases hNotMajority : 2 * p.required_votes_for_decision ≤ p.council_size
          · simp [hCouncil, hEvidence, hVotes, hTooLarge, hNotMajority] at hPolicy
            cases hPolicy
          · by_cases hRounds : p.max_deliberation_rounds = 0
            · simp [hCouncil, hEvidence, hVotes, hTooLarge, hNotMajority, hRounds] at hPolicy
              cases hPolicy
            · exact Nat.pos_of_ne_zero hRounds

theorem initializeCase_establishes_max_deliberation_rounds_positive
    (req : InitializeCaseRequest)
    (s : ArbitrationState)
    (hInit : initializeCase req = .ok s) :
    0 < s.policy.max_deliberation_rounds := by
  have hFrame := initializeCase_establishes_caseFrame req s hInit
  rcases hFrame with ⟨_hProp, hPolicyEq, _hMembers⟩
  have hValid : validatePolicy req.state.policy = .ok PUnit.unit := by
    unfold initializeCase at hInit
    cases hPolicy : validatePolicy req.state.policy with
    | error err =>
        simp [hPolicy] at hInit
        cases hInit
    | ok okv =>
        cases okv
        rfl
  have hPos : 0 < req.state.policy.max_deliberation_rounds :=
    validatePolicy_ok_implies_max_deliberation_rounds_positive req.state.policy hValid
  simpa [hPolicyEq] using hPos

/--
Adding an opening filing consumes exactly one merits step.

`phaseShape` limits a reachable openings list to `[]` or `[plaintiff]`.  The
first opening stays in the same phase.  The second opening completes the
bilateral pair and advances the phase machine to `arguments`.  In either case
the merits budget drops by one.
-/
theorem addOpening_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (role text : String)
    (hShape : phaseShape c)
    (hPhase : c.phase = "openings") :
    remainingMeritsSteps (addFiling c "openings" role text) + 1 =
      remainingMeritsSteps c := by
  have hShape' :
      bilateralStarted "openings" c.openings ∧
        c.arguments = [] ∧ c.rebuttals = [] ∧ c.surrebuttals = [] ∧ c.closings = [] := by
    simpa [phaseShape, hPhase] using hShape
  rcases hShape' with ⟨hStarted, hArguments, hRebuttals, hSurrebuttals, hClosings⟩
  cases hList : c.openings with
  | nil =>
      simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hList,
        hArguments, hRebuttals, hSurrebuttals, hClosings]
  | cons head tail =>
      cases tail with
      | nil =>
          simp [bilateralStarted, hList] at hStarted
          simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hList,
            hArguments, hRebuttals, hSurrebuttals, hClosings]
      | cons next rest =>
          simp [bilateralStarted, hList] at hStarted

/--
Adding an argument filing consumes exactly one merits step.
-/
theorem addArgument_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (role text : String)
    (hShape : phaseShape c)
    (hPhase : c.phase = "arguments") :
    remainingMeritsSteps (addFiling c "arguments" role text) + 1 =
      remainingMeritsSteps c := by
  have hShape' :
      bilateralComplete "openings" c.openings ∧
        bilateralStarted "arguments" c.arguments ∧
        c.rebuttals = [] ∧ c.surrebuttals = [] ∧ c.closings = [] := by
    simpa [phaseShape, hPhase] using hShape
  rcases hShape' with ⟨_hOpenings, hStarted, hRebuttals, hSurrebuttals, hClosings⟩
  cases hList : c.arguments with
  | nil =>
      simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hList,
        hRebuttals, hSurrebuttals, hClosings]
  | cons head tail =>
      cases tail with
      | nil =>
          simp [bilateralStarted, hList] at hStarted
          simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hList,
            hRebuttals, hSurrebuttals, hClosings]
      | cons next rest =>
          simp [bilateralStarted, hList] at hStarted

/--
Adding a rebuttal filing consumes exactly one merits step.
-/
theorem addRebuttal_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (text : String)
    (hShape : phaseShape c)
    (hPhase : c.phase = "rebuttals") :
    remainingMeritsSteps (addFiling c "rebuttals" "plaintiff" text) + 1 =
      remainingMeritsSteps c := by
  have hShape' :
      bilateralComplete "openings" c.openings ∧
        bilateralComplete "arguments" c.arguments ∧
        c.rebuttals = [] ∧ c.surrebuttals = [] ∧ c.closings = [] := by
    simpa [phaseShape, hPhase] using hShape
  rcases hShape' with ⟨_hOpenings, _hArguments, hRebuttals, _hSurrebuttals, _hClosings⟩
  simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hRebuttals]

/--
Passing rebuttal consumes exactly one merits step.
-/
theorem passRebuttal_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (hPhase : c.phase = "rebuttals") :
    remainingMeritsSteps { c with phase := "surrebuttals" } + 1 =
      remainingMeritsSteps c := by
  simp [remainingMeritsSteps, hPhase]

/--
Adding a surrebuttal filing consumes exactly one merits step.
-/
theorem addSurrebuttal_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (text : String)
    (hShape : phaseShape c)
    (hPhase : c.phase = "surrebuttals") :
    remainingMeritsSteps (addFiling c "surrebuttals" "defendant" text) + 1 =
      remainingMeritsSteps c := by
  have hShape' :
      bilateralComplete "openings" c.openings ∧
        bilateralComplete "arguments" c.arguments ∧
        plaintiffOptionalSequence "rebuttals" c.rebuttals ∧
        c.surrebuttals = [] ∧ c.closings = [] := by
    simpa [phaseShape, hPhase] using hShape
  rcases hShape' with ⟨_hOpenings, _hArguments, _hRebuttals, hSurrebuttals, hClosings⟩
  simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hSurrebuttals, hClosings]

/--
Passing surrebuttal consumes exactly one merits step.
-/
theorem passSurrebuttal_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (hShape : phaseShape c)
    (hPhase : c.phase = "surrebuttals") :
    remainingMeritsSteps { c with phase := "closings" } + 1 =
      remainingMeritsSteps c := by
  have hShape' :
      bilateralComplete "openings" c.openings ∧
        bilateralComplete "arguments" c.arguments ∧
        plaintiffOptionalSequence "rebuttals" c.rebuttals ∧
        c.surrebuttals = [] ∧ c.closings = [] := by
    simpa [phaseShape, hPhase] using hShape
  rcases hShape' with ⟨_hOpenings, _hArguments, _hRebuttals, _hSurrebuttals, hClosings⟩
  simp [remainingMeritsSteps, hPhase, hClosings]

/--
Adding a closing filing consumes exactly one merits step.
-/
theorem addClosing_decreases_remainingMeritsSteps
    (c : ArbitrationCase)
    (role text : String)
    (hShape : phaseShape c)
    (hPhase : c.phase = "closings") :
    remainingMeritsSteps (addFiling c "closings" role text) + 1 =
      remainingMeritsSteps c := by
  have hShape' :
      bilateralComplete "openings" c.openings ∧
        bilateralComplete "arguments" c.arguments ∧
        plaintiffOptionalSequence "rebuttals" c.rebuttals ∧
          defendantOptionalSequence "surrebuttals" c.surrebuttals ∧
          bilateralStarted "closings" c.closings := by
    simpa [phaseShape, hPhase] using hShape
  rcases hShape' with ⟨_hOpenings, _hArguments, _hRebuttals, _hSurrebuttals, hStarted⟩
  cases hList : c.closings with
      | nil =>
          simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hList]
      | cons head tail =>
          cases tail with
          | nil =>
              simp [bilateralStarted, hList] at hStarted
              simp [remainingMeritsSteps, addFiling, advanceAfterMerits, hPhase, hList]
          | cons next rest =>
              simp [bilateralStarted, hList] at hStarted

/--
Each successful merits step decreases the total remaining-step budget by
exactly one.

The total budget splits into a merits component and a deliberation component.
Merits steps consume one unit of the merits budget and leave the deliberation
budget unchanged.
-/
theorem step_record_opening_statement_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "record_opening_statement")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 = remainingStepBudget s := by
  have hShape : phaseShape s.case := reachable_phaseShape s hs
  have hTarget0 : t.case.phase ≠ "closed" := by
    exact step_record_opening_statement_phase_ne_closed s t action hType hStep
  have hPhase : s.case.phase = "openings" := by
    by_cases hOpen : s.case.phase = "openings"
    · exact hOpen
    · simp [step, hType, hOpen] at hStep
      cases hStep
  rcases step_record_opening_statement_result s t action hType hStep with ⟨rawText, rfl⟩
  have hMerits :
      remainingMeritsSteps
          (addFiling s.case "openings"
            (if s.case.openings.isEmpty then "plaintiff" else "defendant")
            (trimString rawText)) + 1 =
        remainingMeritsSteps s.case := by
    exact addOpening_decreases_remainingMeritsSteps
      s.case
      (if s.case.openings.isEmpty then "plaintiff" else "defendant")
      (trimString rawText)
      hShape
      hPhase
  have hDelib :
      remainingDeliberationSteps
          (stateWithCase s
            (addFiling s.case "openings"
              (if s.case.openings.isEmpty then "plaintiff" else "defendant")
              (trimString rawText))) =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_addFiling
      s
      "openings"
      (if s.case.openings.isEmpty then "plaintiff" else "defendant")
      (trimString rawText)
  have hTarget :
      (stateWithCase s
        (addFiling s.case "openings"
          (if s.case.openings.isEmpty then "plaintiff" else "defendant")
          (trimString rawText))).case.phase ≠ "closed" := by
    simpa [List.isEmpty_iff] using hTarget0
  rw [remainingStepBudget_of_phase_ne_closed _ hTarget]
  rw [remainingStepBudget_of_phase_ne_closed s (by simp [hPhase])]
  rw [hDelib]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun n => n + remainingDeliberationSteps s) hMerits

theorem step_submit_argument_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "submit_argument")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 = remainingStepBudget s := by
  have hShape : phaseShape s.case := reachable_phaseShape s hs
  have hTarget0 : t.case.phase ≠ "closed" := by
    exact step_submit_argument_phase_ne_closed s t action hType hStep
  have hSubmit :
      recordMeritsSubmission
        s
        "arguments"
        action.actor_role
        (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
        "argument"
        s.policy.max_argument_chars
        true
        action.payload = .ok t := by
    simpa [step, hType] using hStep
  rcases recordMeritsSubmission_with_materials_result
      s t "arguments" action.actor_role
      (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
      "argument" s.policy.max_argument_chars action.payload hSubmit with
    ⟨rawText, offered, reports, rfl⟩
  have hPhase : s.case.phase = "arguments" := by
    by_cases hArg : s.case.phase = "arguments"
    · exact hArg
    · simp [recordMeritsSubmission, hArg] at hSubmit
      cases hSubmit
  have hMerits :
      remainingMeritsSteps
          (addFiling s.case "arguments"
            (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
            (trimString rawText)) + 1 =
        remainingMeritsSteps s.case := by
    exact addArgument_decreases_remainingMeritsSteps
      s.case
      (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
      (trimString rawText)
      hShape
      hPhase
  have hDelib1 :
      remainingDeliberationSteps
          (stateWithCase s
            (addFiling s.case "arguments"
              (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
              (trimString rawText))) =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_addFiling
      s
      "arguments"
      (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
      (trimString rawText)
  have hDelib :
      remainingDeliberationSteps
          (stateWithCase s
            (appendSupplementalMaterials
              (addFiling s.case "arguments"
                (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
                (trimString rawText))
              offered
              reports)) =
        remainingDeliberationSteps s := by
    unfold remainingDeliberationSteps seatedCouncilMemberCount seatedCouncilMembers currentRoundVotes at *
    simpa [stateWithCase, appendSupplementalMaterials] using hDelib1
  have hTarget :
      (stateWithCase s
        (appendSupplementalMaterials
          (addFiling s.case "arguments"
            (if s.case.arguments.isEmpty then "plaintiff" else "defendant")
            (trimString rawText))
          offered
          reports)).case.phase ≠ "closed" := by
    simpa [List.isEmpty_iff] using hTarget0
  rw [remainingStepBudget_of_phase_ne_closed _ hTarget]
  rw [remainingStepBudget_of_phase_ne_closed s (by simp [hPhase])]
  rw [hDelib]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun n => n + remainingDeliberationSteps s) hMerits

theorem step_submit_rebuttal_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "submit_rebuttal")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 = remainingStepBudget s := by
  have hShape : phaseShape s.case := reachable_phaseShape s hs
  have hTarget0 : t.case.phase ≠ "closed" := by
    exact step_submit_rebuttal_phase_ne_closed s t action hType hStep
  have hSubmit :
      recordMeritsSubmission
        s
        "rebuttals"
        action.actor_role
        "plaintiff"
        "rebuttal"
        s.policy.max_rebuttal_chars
        true
        action.payload = .ok t := by
    simpa [step, hType] using hStep
  rcases recordMeritsSubmission_with_materials_result
      s t "rebuttals" action.actor_role
      "plaintiff"
      "rebuttal" s.policy.max_rebuttal_chars action.payload hSubmit with
    ⟨rawText, offered, reports, rfl⟩
  have hPhase : s.case.phase = "rebuttals" := by
    by_cases hReb : s.case.phase = "rebuttals"
    · exact hReb
    · simp [recordMeritsSubmission, hReb] at hSubmit
      cases hSubmit
  have hMerits :
      remainingMeritsSteps
          (addFiling s.case "rebuttals" "plaintiff" (trimString rawText)) + 1 =
        remainingMeritsSteps s.case := by
    exact addRebuttal_decreases_remainingMeritsSteps
      s.case
      (trimString rawText)
      hShape
      hPhase
  have hDelib1 :
      remainingDeliberationSteps
          (stateWithCase s
            (addFiling s.case "rebuttals" "plaintiff" (trimString rawText))) =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_addFiling
      s
      "rebuttals"
      "plaintiff"
      (trimString rawText)
  have hDelib :
      remainingDeliberationSteps
          (stateWithCase s
            (appendSupplementalMaterials
              (addFiling s.case "rebuttals" "plaintiff" (trimString rawText))
              offered
              reports)) =
        remainingDeliberationSteps s := by
    unfold remainingDeliberationSteps seatedCouncilMemberCount seatedCouncilMembers currentRoundVotes at *
    simpa [stateWithCase, appendSupplementalMaterials] using hDelib1
  have hTarget :
      (stateWithCase s
        (appendSupplementalMaterials
          (addFiling s.case "rebuttals" "plaintiff" (trimString rawText))
          offered
          reports)).case.phase ≠ "closed" := by
    exact hTarget0
  rw [remainingStepBudget_of_phase_ne_closed _ hTarget]
  rw [remainingStepBudget_of_phase_ne_closed s (by simp [hPhase])]
  rw [hDelib]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun n => n + remainingDeliberationSteps s) hMerits

theorem step_submit_surrebuttal_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "submit_surrebuttal")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 = remainingStepBudget s := by
  have hShape : phaseShape s.case := reachable_phaseShape s hs
  have hTarget0 : t.case.phase ≠ "closed" := by
    exact step_submit_surrebuttal_phase_ne_closed s t action hType hStep
  have hSubmit :
      recordMeritsSubmission
        s
        "surrebuttals"
        action.actor_role
        "defendant"
        "surrebuttal"
        s.policy.max_surrebuttal_chars
        false
        action.payload = .ok t := by
    simpa [step, hType] using hStep
  rcases recordMeritsSubmission_without_materials_result
      s t "surrebuttals" action.actor_role "defendant"
      "surrebuttal" s.policy.max_surrebuttal_chars action.payload hSubmit with
    ⟨rawText, rfl⟩
  have hPhase : s.case.phase = "surrebuttals" := by
    by_cases hSur : s.case.phase = "surrebuttals"
    · exact hSur
    · simp [recordMeritsSubmission, hSur] at hSubmit
      cases hSubmit
  have hMerits :
      remainingMeritsSteps
          (addFiling s.case "surrebuttals" "defendant" (trimString rawText)) + 1 =
        remainingMeritsSteps s.case := by
    exact addSurrebuttal_decreases_remainingMeritsSteps
      s.case
      (trimString rawText)
      hShape
      hPhase
  have hDelib :
      remainingDeliberationSteps
          (stateWithCase s
            (addFiling s.case "surrebuttals" "defendant" (trimString rawText))) =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_addFiling
      s
      "surrebuttals"
      "defendant"
      (trimString rawText)
  have hTarget :
      (stateWithCase s
        (addFiling s.case "surrebuttals" "defendant" (trimString rawText))).case.phase ≠ "closed" := by
    exact hTarget0
  rw [remainingStepBudget_of_phase_ne_closed _ hTarget]
  rw [remainingStepBudget_of_phase_ne_closed s (by simp [hPhase])]
  rw [hDelib]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun n => n + remainingDeliberationSteps s) hMerits

theorem step_deliver_closing_statement_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "deliver_closing_statement")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 = remainingStepBudget s := by
  have hShape : phaseShape s.case := reachable_phaseShape s hs
  have hTarget0 : t.case.phase ≠ "closed" := by
    exact step_deliver_closing_statement_phase_ne_closed s t action hType hStep
  have hPhase : s.case.phase = "closings" := by
    by_cases hClosings : s.case.phase = "closings"
    · exact hClosings
    · simp [step, hType, hClosings] at hStep
      cases hStep
  rcases step_deliver_closing_statement_result s t action hType hStep with ⟨rawText, rfl⟩
  have hMerits :
      remainingMeritsSteps
          (addFiling s.case "closings"
            (if s.case.closings.isEmpty then "plaintiff" else "defendant")
            (trimString rawText)) + 1 =
        remainingMeritsSteps s.case := by
    exact addClosing_decreases_remainingMeritsSteps
      s.case
      (if s.case.closings.isEmpty then "plaintiff" else "defendant")
      (trimString rawText)
      hShape
      hPhase
  have hDelib :
      remainingDeliberationSteps
          (stateWithCase s
            (addFiling s.case "closings"
              (if s.case.closings.isEmpty then "plaintiff" else "defendant")
              (trimString rawText))) =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_addFiling
      s
      "closings"
      (if s.case.closings.isEmpty then "plaintiff" else "defendant")
      (trimString rawText)
  have hTarget :
      (stateWithCase s
        (addFiling s.case "closings"
          (if s.case.closings.isEmpty then "plaintiff" else "defendant")
          (trimString rawText))).case.phase ≠ "closed" := by
    simpa [List.isEmpty_iff] using hTarget0
  rw [remainingStepBudget_of_phase_ne_closed _ hTarget]
  rw [remainingStepBudget_of_phase_ne_closed s (by simp [hPhase])]
  rw [hDelib]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun n => n + remainingDeliberationSteps s) hMerits

/--
Passing a rebuttal or surrebuttal also consumes exactly one merits step.

The public `pass_phase_opportunity` action is the only successful merits step
that does not add a filing.  It still advances the phase machine, and it still
uses one unit of the fixed merits budget.
-/
theorem step_pass_phase_opportunity_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "pass_phase_opportunity")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 = remainingStepBudget s := by
  have hShape : phaseShape s.case := reachable_phaseShape s hs
  have hTarget0 : t.case.phase ≠ "closed" := by
    exact step_pass_phase_opportunity_phase_ne_closed s t action hType hStep
  by_cases hRebuttals : s.case.phase = "rebuttals"
  · have hPass :
        (do
          requireRole action.actor_role "plaintiff"
          if !s.case.rebuttals.isEmpty then
            throw "rebuttal already submitted"
          pure <| stateWithCase s { s.case with phase := "surrebuttals" }) = .ok t := by
      simpa [step, hType, hRebuttals] using hStep
    cases hRole : requireRole action.actor_role "plaintiff" with
    | error err =>
        rw [hRole] at hPass
        simp at hPass
        cases hPass
    | ok okv =>
        cases okv
        rw [hRole] at hPass
        cases hEmpty : s.case.rebuttals.isEmpty with
        | false =>
            simp [hEmpty] at hPass
            cases hPass
        | true =>
            simp [hEmpty] at hPass
            cases hPass
            have hMerits :
                remainingMeritsSteps { s.case with phase := "surrebuttals" } + 1 =
                  remainingMeritsSteps s.case := by
              exact passRebuttal_decreases_remainingMeritsSteps s.case hRebuttals
            have hDelib :
                remainingDeliberationSteps (stateWithCase s { s.case with phase := "surrebuttals" }) =
                  remainingDeliberationSteps s := by
              exact remainingDeliberationSteps_phase_update s "surrebuttals"
            rw [remainingStepBudget_of_phase_ne_closed _ (by simpa using hTarget0)]
            rw [remainingStepBudget_of_phase_ne_closed s (by simp [hRebuttals])]
            rw [hDelib]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              congrArg (fun n => n + remainingDeliberationSteps s) hMerits
  · by_cases hSurrebuttals : s.case.phase = "surrebuttals"
    · have hPass :
          (do
            requireRole action.actor_role "defendant"
            if !s.case.surrebuttals.isEmpty then
              throw "surrebuttal already submitted"
            pure <| stateWithCase s { s.case with phase := "closings" }) = .ok t := by
        simpa [step, hType, hRebuttals, hSurrebuttals] using hStep
      cases hRole : requireRole action.actor_role "defendant" with
      | error err =>
          rw [hRole] at hPass
          simp at hPass
          cases hPass
      | ok okv =>
          cases okv
          rw [hRole] at hPass
          cases hEmpty : s.case.surrebuttals.isEmpty with
          | false =>
              simp [hEmpty] at hPass
              cases hPass
          | true =>
              simp [hEmpty] at hPass
              cases hPass
              have hMerits :
                  remainingMeritsSteps { s.case with phase := "closings" } + 1 =
                    remainingMeritsSteps s.case := by
                exact passSurrebuttal_decreases_remainingMeritsSteps s.case hShape hSurrebuttals
              have hDelib :
                  remainingDeliberationSteps (stateWithCase s { s.case with phase := "closings" }) =
                    remainingDeliberationSteps s := by
                exact remainingDeliberationSteps_phase_update s "closings"
              rw [remainingStepBudget_of_phase_ne_closed _ (by simpa using hTarget0)]
              rw [remainingStepBudget_of_phase_ne_closed s (by simp [hSurrebuttals])]
              rw [hDelib]
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                congrArg (fun n => n + remainingDeliberationSteps s) hMerits
    · simp [step, hType, hRebuttals, hSurrebuttals] at hStep

/--
Appending a fresh current-round vote consumes exactly one unit of
deliberation budget.

The seated roster does not change.  The current-round vote count increases by
one.  The strict-inequality hypothesis says there was still one unit of round
capacity left to consume.
-/
theorem remainingDeliberationSteps_appendCurrentRoundVote
    (s : ArbitrationState)
    (memberId vote rationale : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case) :
    remainingDeliberationSteps
        (stateWithCase s
          { s.case with council_votes := s.case.council_votes.concat {
              member_id := memberId
              round := s.case.deliberation_round
              vote := trimString vote
              rationale := trimString rationale
            } }) + 1 =
      remainingDeliberationSteps s := by
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := trimString vote
    rationale := trimString rationale
  } }
  have hRoundCapacity :
      (currentRoundVotes s.case).length < seatedCouncilMemberCount s.case := by
    exact currentRoundVotes_length_lt_seatedCouncilMemberCount_of_fresh_seated
      s.case memberId hUnique hIntegrity hSeated hFresh
  have hVoteLen :
      (currentRoundVotes c1).length = (currentRoundVotes s.case).length + 1 := by
    simp [c1, currentRoundVotes, List.concat_eq_append]
  have hSeatedSame : seatedCouncilMemberCount c1 = seatedCouncilMemberCount s.case := by
    simp [c1, seatedCouncilMemberCount, seatedCouncilMembers]
  calc
    remainingDeliberationSteps (stateWithCase s c1) + 1
        = ((s.policy.max_deliberation_rounds - s.case.deliberation_round) * s.policy.council_size +
            (seatedCouncilMemberCount c1 - (currentRoundVotes c1).length)) + 1 := by
              simp [remainingDeliberationSteps, stateWithCase, c1]
    _ = ((s.policy.max_deliberation_rounds - s.case.deliberation_round) * s.policy.council_size +
          (seatedCouncilMemberCount s.case - ((currentRoundVotes s.case).length + 1))) + 1 := by
          rw [hSeatedSame, hVoteLen]
    _ = remainingDeliberationSteps s := by
          simp [remainingDeliberationSteps]
          omega

/--
Updating a member status for an identifier that is not present leaves the
seated-member count unchanged.

The removal proof uses this fact on the untouched tail of the council roster.
-/
theorem seatedCount_status_update_absent
    (members : List CouncilMember)
    (memberId status : String)
    (hAbsent : memberId ∉ councilMemberIds members) :
    (members.map (fun member =>
        if member.member_id = memberId then
          { member with status := trimString status }
        else
          member)
      |>.filter memberIsSeated).length =
      (members.filter memberIsSeated).length := by
  induction members with
  | nil =>
      simp
  | cons head tail ih =>
      have hHeadNe : head.member_id ≠ memberId := by
        intro hEq
        exact hAbsent (by simp [councilMemberIds, hEq])
      have hTailAbsent : memberId ∉ councilMemberIds tail := by
        intro hMem
        exact hAbsent (by
          have : memberId ∈ head.member_id :: councilMemberIds tail :=
            List.mem_cons.mpr (Or.inr hMem)
          simpa [councilMemberIds] using this)
      by_cases hHeadSeated : memberIsSeated head = true
      · simp [hHeadNe, hHeadSeated, ih hTailAbsent]
      · simp [hHeadNe, hHeadSeated, ih hTailAbsent]

/--
Changing one seated member to a non-seated status decreases the seated-member
count by exactly one.

The uniqueness of council identifiers matters here.  It rules out the
possibility that the requested identifier names some other seated member in the
tail while the head uses the same identifier with a different status.
-/
theorem seatedFilterLength_removeOne
    (members : List CouncilMember)
    (memberId status : String)
    (hUnique : (members.map (fun member => member.member_id)).Nodup)
    (hSeated : memberId ∈ (members.filter memberIsSeated).map (fun member => member.member_id))
    (hStatus : trimString status ≠ "seated") :
    ((members.map (fun member =>
        if member.member_id = memberId then
          { member with status := trimString status }
        else
          member)).filter memberIsSeated).length + 1 =
      (members.filter memberIsSeated).length := by
  induction members with
  | nil =>
      simp at hSeated
  | cons head tail ih =>
      have hUniqueInfo := List.nodup_cons.mp hUnique
      have hSeatedWitness :
          ∃ a, ((a = head ∨ a ∈ tail) ∧ memberIsSeated a = true) ∧ a.member_id = memberId := by
        simpa using hSeated
      by_cases hHeadId : head.member_id = memberId
      · have hHeadSeated : memberIsSeated head = true := by
          rcases hSeatedWitness with ⟨a, ⟨hMemA, hSeatA⟩, hIdA⟩
          rcases hMemA with rfl | hTail
          · simpa [hHeadId] using hSeatA
          · have hTailId : memberId ∈ tail.map (fun member => member.member_id) := by
              exact List.mem_map.mpr ⟨a, hTail, hIdA⟩
            exact False.elim (hUniqueInfo.1 (by simpa [hHeadId] using hTailId))
        have hTailAbsent : memberId ∉ tail.map (fun member => member.member_id) := by
          simpa [hHeadId] using hUniqueInfo.1
        have hTailSame :
            ((tail.map (fun member =>
                if member.member_id = memberId then
                  { member with status := trimString status }
                else
                  member)).filter memberIsSeated).length =
              (tail.filter memberIsSeated).length :=
          seatedCount_status_update_absent tail memberId status hTailAbsent
        have hUpdatedHeadNotSeated :
            memberIsSeated { head with status := trimString status } = false := by
          simp [memberIsSeated, hStatus]
        calc
          (((head :: tail).map (fun member =>
                if member.member_id = memberId then
                  { member with status := trimString status }
                else
                  member)).filter memberIsSeated).length + 1
              = ((tail.map (fun member =>
                    if member.member_id = memberId then
                      { member with status := trimString status }
                    else
                      member)).filter memberIsSeated).length + 1 := by
                  simp [List.map, memberIsSeated, hHeadId, hStatus]
          _ = (tail.filter memberIsSeated).length + 1 := by
                  rw [hTailSame]
          _ = ((head :: tail).filter memberIsSeated).length := by
                  simp [hHeadSeated]
      · have hTailSeated : memberId ∈ (tail.filter memberIsSeated).map (fun member => member.member_id) := by
          rcases hSeatedWitness with ⟨a, ⟨hMemA, hSeatA⟩, hIdA⟩
          have hATail : a ∈ tail := by
            rcases hMemA with rfl | hTail
            · exact False.elim (hHeadId (by simpa using hIdA))
            · exact hTail
          exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨hATail, hSeatA⟩, hIdA⟩
        have ih' := ih hUniqueInfo.2 hTailSeated
        by_cases hHeadSeated : memberIsSeated head = true
        · simpa [hHeadId, hHeadSeated, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg Nat.succ ih'
        · simpa [hHeadId, hHeadSeated] using ih'

theorem seatedCouncilMemberCount_removeUnvotedCouncilMember
    (c : ArbitrationCase)
    (memberId status : String)
    (hUnique : councilIdsUnique c)
    (hSeated : memberId ∈ seatedCouncilMemberIds c)
    (hStatus : trimString status ≠ "seated") :
    seatedCouncilMemberCount
      { c with council_members := c.council_members.map (fun member =>
          if member.member_id = memberId then
            { member with status := trimString status }
          else
            member) } + 1 =
      seatedCouncilMemberCount c := by
  unfold councilIdsUnique councilMemberIds at hUnique
  unfold seatedCouncilMemberIds at hSeated
  unfold seatedCouncilMemberCount seatedCouncilMembers
  simpa using seatedFilterLength_removeOne c.council_members memberId status hUnique hSeated hStatus

/--
Removing an unvoted seated member consumes exactly one unit of deliberation
budget before `continueDeliberation` runs.

The vote list does not change.  The active round does not change.  The seated
roster loses exactly one member because successful removal forbids both empty
status and the status `"seated"`.
-/
theorem remainingDeliberationSteps_removeUnvotedCouncilMember
    (s : ArbitrationState)
    (memberId status : String)
    (hUnique : councilIdsUnique s.case)
    (hIntegrity : councilVoteIntegrity s.case)
    (hSeated : memberId ∈ seatedCouncilMemberIds s.case)
    (hFresh : memberId ∉ currentRoundVoteIds s.case)
    (hStatus : trimString status ≠ "seated") :
    remainingDeliberationSteps
        (stateWithCase s
          { s.case with council_members := s.case.council_members.map (fun member =>
              if member.member_id = memberId then
                { member with status := trimString status }
              else
                member) }) + 1 =
      remainingDeliberationSteps s := by
  let c1 := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hRoundCapacity :
      (currentRoundVotes s.case).length < seatedCouncilMemberCount s.case := by
    exact currentRoundVotes_length_lt_seatedCouncilMemberCount_of_fresh_seated
      s.case memberId hUnique hIntegrity hSeated hFresh
  have hSeatedCount :
      seatedCouncilMemberCount c1 + 1 = seatedCouncilMemberCount s.case := by
    simpa [c1] using
      seatedCouncilMemberCount_removeUnvotedCouncilMember s.case memberId status hUnique hSeated hStatus
  have hVotes :
      currentRoundVotes c1 = currentRoundVotes s.case := by
    simp [c1, currentRoundVotes]
  calc
    remainingDeliberationSteps (stateWithCase s c1) + 1
        = ((s.policy.max_deliberation_rounds - s.case.deliberation_round) * s.policy.council_size +
            ((seatedCouncilMemberCount s.case - 1) - (currentRoundVotes s.case).length)) + 1 := by
              have hSeatedPred : seatedCouncilMemberCount c1 = seatedCouncilMemberCount s.case - 1 := by
                omega
              simp [remainingDeliberationSteps, stateWithCase, c1, hVotes, hSeatedPred]
    _ = remainingDeliberationSteps s := by
          simp [remainingDeliberationSteps]
          omega

/--
Once `continueDeliberation` receives a deliberating case, it does not increase
the remaining-step budget.

Closing makes the budget zero.  An incomplete round preserves the deliberation
budget exactly.  A completed but non-final round advances the round counter and
therefore leaves at most one full round of budget less than before.
-/
theorem continueDeliberation_does_not_increase_remainingStepBudget
    (s t : ArbitrationState)
    (c : ArbitrationCase)
    (hPhase : c.phase = "deliberation")
    (hSeatedBound : seatedCouncilMemberCount c ≤ s.policy.council_size)
    (hRounds : councilVoteRoundsBounded c)
    (hCont : continueDeliberation s c = .ok t) :
    remainingStepBudget t ≤ remainingDeliberationSteps (stateWithCase s c) := by
  unfold continueDeliberation at hCont
  by_cases hRoundComplete : (currentRoundVotes c).length = seatedCouncilMemberCount c
  · cases hResolution : currentResolution? c s.policy.required_votes_for_decision with
    | some resolution =>
        simp [hRoundComplete, hResolution, stateWithCase] at hCont
        cases hCont
        exact Nat.zero_le _
    | none =>
        by_cases hTooFew : seatedCouncilMemberCount c < s.policy.required_votes_for_decision
        · simp [hRoundComplete, hResolution, hTooFew, stateWithCase] at hCont
          cases hCont
          exact Nat.zero_le _
        · by_cases hLastRound : c.deliberation_round ≥ s.policy.max_deliberation_rounds
          · simp [hRoundComplete, hResolution, hTooFew, hLastRound, stateWithCase] at hCont
            cases hCont
            exact Nat.zero_le _
          · simp [hRoundComplete, hResolution, hTooFew, hLastRound, stateWithCase] at hCont
            cases hCont
            let c1 : ArbitrationCase := { c with deliberation_round := c.deliberation_round + 1 }
            have hNoVotes :
                currentRoundVotes c1 = [] := by
              exact currentRoundVotes_empty_after_round_increment c hRounds
            have hRoundLt : c.deliberation_round < s.policy.max_deliberation_rounds := by
              exact Nat.lt_of_not_ge hLastRound
            have hSeatedSame : seatedCouncilMemberCount c1 = seatedCouncilMemberCount c := by
              simp [c1, seatedCouncilMemberCount, seatedCouncilMembers]
            rw [remainingStepBudget_of_phase_ne_closed _ (by simp [hPhase])]
            have hDelibBudget :
                remainingDeliberationSteps (stateWithCase s c1) ≤
                  remainingDeliberationSteps (stateWithCase s c) := by
              have hBudgetC1 :
                  remainingDeliberationSteps (stateWithCase s c1) =
                    (s.policy.max_deliberation_rounds - (c.deliberation_round + 1)) *
                        s.policy.council_size +
                      seatedCouncilMemberCount c := by
                simp [remainingDeliberationSteps, stateWithCase, c1, hNoVotes, hSeatedSame]
              have hBudgetC :
                  remainingDeliberationSteps (stateWithCase s c) =
                    (s.policy.max_deliberation_rounds - c.deliberation_round) *
                      s.policy.council_size := by
                simp [remainingDeliberationSteps, stateWithCase, hRoundComplete]
              calc
                remainingDeliberationSteps (stateWithCase s c1)
                    = (s.policy.max_deliberation_rounds - (c.deliberation_round + 1)) *
                        s.policy.council_size +
                      seatedCouncilMemberCount c := hBudgetC1
                _ ≤ (s.policy.max_deliberation_rounds - (c.deliberation_round + 1)) *
                        s.policy.council_size +
                      s.policy.council_size := by
                      exact Nat.add_le_add_left hSeatedBound _
                _ = (s.policy.max_deliberation_rounds - c.deliberation_round) *
                      s.policy.council_size := by
                      have hSub :
                          s.policy.max_deliberation_rounds - c.deliberation_round =
                            (s.policy.max_deliberation_rounds - (c.deliberation_round + 1)) + 1 := by
                        omega
                      rw [hSub, Nat.add_mul]
                      simp
                _ = remainingDeliberationSteps (stateWithCase s c) := hBudgetC.symm
            simpa [remainingMeritsSteps, stateWithCase, c1, hPhase] using hDelibBudget
  · simp [hRoundComplete, stateWithCase] at hCont
    cases hCont
    simp [remainingStepBudget, remainingMeritsSteps, remainingDeliberationSteps,
      stateWithCase, hPhase]

/--
A successful council-vote step decreases the total remaining-step budget by at
least one.

The vote itself consumes one unit of round capacity.  After that,
`continueDeliberation` cannot increase the remaining budget.
-/
theorem step_submit_council_vote_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "submit_council_vote")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 ≤ remainingStepBudget s := by
  rcases step_submit_council_vote_details s t action hType hStep with
    ⟨memberId, vote, rationale, hPhase, hSeated, hFresh, hCont⟩
  let c1 := { s.case with council_votes := s.case.council_votes.concat {
    member_id := memberId
    round := s.case.deliberation_round
    vote := trimString vote
    rationale := trimString rationale
  } }
  have hUnique : councilIdsUnique s.case := reachable_councilIdsUnique s hs
  have hIntegrity : councilVoteIntegrity s.case := reachable_councilVoteIntegrity s hs
  have hIntegrity1 : councilVoteIntegrity c1 := by
    exact appendCurrentRoundVote_preserves_councilVoteIntegrity
      s.case memberId vote rationale hIntegrity hSeated hFresh
  have hVoteBudget :
      remainingDeliberationSteps (stateWithCase s c1) + 1 =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_appendCurrentRoundVote
      s memberId vote rationale hUnique hIntegrity hSeated hFresh
  have hSeatedBound : seatedCouncilMemberCount c1 ≤ s.policy.council_size := by
    simpa [c1] using reachable_seatedCouncilMemberCount_le_councilSize s hs
  have hContBudget :
      remainingStepBudget t ≤ remainingDeliberationSteps (stateWithCase s c1) := by
    exact continueDeliberation_does_not_increase_remainingStepBudget
      s t c1
      (by simpa [c1] using hPhase)
      hSeatedBound
      hIntegrity1.2.2
      (by simpa [c1] using hCont)
  have hSourceBudget :
      remainingStepBudget s = remainingDeliberationSteps s := by
    simp [remainingStepBudget, remainingMeritsSteps, hPhase]
  rw [hSourceBudget]
  calc
    remainingStepBudget t + 1 ≤ remainingDeliberationSteps (stateWithCase s c1) + 1 := by
      exact Nat.add_le_add_right hContBudget 1
    _ = remainingDeliberationSteps s := hVoteBudget

/--
A successful council-removal step decreases the total remaining-step budget by
at least one.

Successful removal changes one seated member to a non-seated status and leaves
the current-round vote list unchanged.  That consumes one unit of the
deliberation budget before `continueDeliberation` runs.
-/
theorem step_remove_council_member_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hType : action.action_type = "remove_council_member")
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 ≤ remainingStepBudget s := by
  rcases step_remove_council_member_details s t action hType hStep with
    ⟨memberId, status, hPhase, hSeated, hFresh, hStatus, hCont⟩
  let c1 := { s.case with council_members := s.case.council_members.map (fun (member : CouncilMember) =>
    if member.member_id = memberId then
      { member with status := trimString status }
    else
      member) }
  have hUnique : councilIdsUnique s.case := reachable_councilIdsUnique s hs
  have hIntegrity : councilVoteIntegrity s.case := reachable_councilVoteIntegrity s hs
  have hIntegrity1 : councilVoteIntegrity c1 := by
    simpa [c1] using
      removeUnvotedCouncilMember_preserves_councilVoteIntegrity
        s.case memberId status hIntegrity hFresh
  have hRemovalBudget :
      remainingDeliberationSteps (stateWithCase s c1) + 1 =
        remainingDeliberationSteps s := by
    exact remainingDeliberationSteps_removeUnvotedCouncilMember
      s memberId status hUnique hIntegrity hSeated hFresh hStatus
  have hSeatedCount :
      seatedCouncilMemberCount c1 + 1 = seatedCouncilMemberCount s.case := by
    simpa [c1] using
      seatedCouncilMemberCount_removeUnvotedCouncilMember
        s.case memberId status hUnique hSeated hStatus
  have hSeatedBound : seatedCouncilMemberCount c1 ≤ s.policy.council_size := by
    have hOldBound : seatedCouncilMemberCount s.case ≤ s.policy.council_size := by
      exact reachable_seatedCouncilMemberCount_le_councilSize s hs
    omega
  have hContBudget :
      remainingStepBudget t ≤ remainingDeliberationSteps (stateWithCase s c1) := by
    exact continueDeliberation_does_not_increase_remainingStepBudget
      s t c1
      (by simpa [c1] using hPhase)
      hSeatedBound
      hIntegrity1.2.2
      (by simpa [c1] using hCont)
  have hSourceBudget :
      remainingStepBudget s = remainingDeliberationSteps s := by
    simp [remainingStepBudget, remainingMeritsSteps, hPhase]
  rw [hSourceBudget]
  calc
    remainingStepBudget t + 1 ≤ remainingDeliberationSteps (stateWithCase s c1) + 1 := by
      exact Nat.add_le_add_right hContBudget 1
    _ = remainingDeliberationSteps s := hRemovalBudget

/--
Every successful public step decreases the remaining-step budget by at least
one.

The merits actions decrease the budget exactly by one.  The two council
actions may close the case immediately, so the public theorem records only the
inequality that the later path bound needs.
-/
theorem step_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t + 1 ≤ remainingStepBudget s := by
  by_cases hOpening : action.action_type = "record_opening_statement"
  · exact Nat.le_of_eq <|
      step_record_opening_statement_decreases_remainingStepBudget s t action hOpening hs hStep
  · by_cases hArgument : action.action_type = "submit_argument"
    · exact Nat.le_of_eq <|
        step_submit_argument_decreases_remainingStepBudget s t action hArgument hs hStep
    · by_cases hRebuttal : action.action_type = "submit_rebuttal"
      · exact Nat.le_of_eq <|
          step_submit_rebuttal_decreases_remainingStepBudget s t action hRebuttal hs hStep
      · by_cases hSurrebuttal : action.action_type = "submit_surrebuttal"
        · exact Nat.le_of_eq <|
            step_submit_surrebuttal_decreases_remainingStepBudget s t action hSurrebuttal hs hStep
        · by_cases hClosing : action.action_type = "deliver_closing_statement"
          · exact Nat.le_of_eq <|
              step_deliver_closing_statement_decreases_remainingStepBudget s t action hClosing hs hStep
          · by_cases hPass : action.action_type = "pass_phase_opportunity"
            · exact Nat.le_of_eq <|
                step_pass_phase_opportunity_decreases_remainingStepBudget s t action hPass hs hStep
            · by_cases hVote : action.action_type = "submit_council_vote"
              · exact step_submit_council_vote_decreases_remainingStepBudget s t action hVote hs hStep
              · by_cases hRemoval : action.action_type = "remove_council_member"
                · exact step_remove_council_member_decreases_remainingStepBudget s t action hRemoval hs hStep
                · cases hType : action.action_type <;>
                    simp [hType] at hOpening hArgument hRebuttal hSurrebuttal hClosing hPass hVote hRemoval <;>
                    simp [step, hType] at hStep

/--
Every successful public step strictly decreases the remaining-step budget.
-/
theorem step_strictly_decreases_remainingStepBudget
    (s t : ArbitrationState)
    (action : CourtAction)
    (hs : Reachable s)
    (hStep : step { state := s, action := action } = .ok t) :
    remainingStepBudget t < remainingStepBudget s := by
  have hDecrease := step_decreases_remainingStepBudget s t action hs hStep
  omega

/--
Every state on a successful indexed path from a reachable start state is
reachable.

`StepPath` records successful public steps but does not itself assert that the
start state came from initialization.  The bounded-termination theorem combines
the two relations: a reachable start plus a successful indexed path from that
start.
-/
theorem stepPath_reachable
    (start s : ArbitrationState)
    (n : Nat)
    (hStart : Reachable start)
    (hPath : StepPath start n s) :
    Reachable s := by
  induction hPath with
  | refl =>
      exact hStart
  | step n u v action hu hStep ih =>
      exact Reachable.step u v action ih hStep

/--
The indexed path length plus the remaining-step budget never exceeds the
initialized budget.

This is the central monotone-measure theorem of Stage 6.  Each successful step
uses one unit of budget, and the budget never becomes negative.
-/
theorem stepPath_length_plus_budget_le
    (start s : ArbitrationState)
    (n : Nat)
    (hStart : Reachable start)
    (hPath : StepPath start n s) :
    n + remainingStepBudget s ≤ remainingStepBudget start := by
  induction hPath with
  | refl =>
      simp
  | step n u v action hu hStep ih =>
      have hReachU : Reachable u := stepPath_reachable start u n hStart hu
      have hDecrease :
          remainingStepBudget v + 1 ≤ remainingStepBudget u := by
        exact step_decreases_remainingStepBudget u v action hReachU hStep
      calc
        (n + 1) + remainingStepBudget v = n + (remainingStepBudget v + 1) := by
          omega
        _ ≤ n + remainingStepBudget u := by
          exact Nat.add_le_add_left hDecrease n
        _ ≤ remainingStepBudget start := ih

/--
If every initialized council member is seated, the seated-member count is the
full council-roster length.
-/
theorem filter_length_eq_length_of_all_seated
    (members : List CouncilMember)
    (hAllSeated : ∀ member ∈ members, memberIsSeated member = true) :
    (members.filter memberIsSeated).length = members.length := by
  induction members with
  | nil =>
      simp
  | cons head tail ih =>
      have hHead : memberIsSeated head = true := hAllSeated head (by simp)
      have hTail : ∀ member ∈ tail, memberIsSeated member = true := by
        intro member hMem
        exact hAllSeated member (by simp [hMem])
      have hTailLen : (tail.filter memberIsSeated).length = tail.length := ih hTail
      simp [hHead, hTailLen]

theorem seatedCouncilMemberCount_eq_length_of_all_seated
    (c : ArbitrationCase)
    (hAllSeated : ∀ member ∈ c.council_members, memberIsSeated member = true) :
    seatedCouncilMemberCount c = c.council_members.length := by
  have hFilter :
      (c.council_members.filter memberIsSeated).length = c.council_members.length := by
    exact filter_length_eq_length_of_all_seated c.council_members hAllSeated
  simpa [seatedCouncilMemberCount, seatedCouncilMembers] using hFilter

/--
Successful initialization fixes the starting remaining-step budget at
`8 + max_deliberation_rounds * council_size`.

The merits side contributes eight fixed actions.  Initialization also starts
deliberation in round one with the full council seated and no current-round
votes, so the deliberation budget is exactly the number of full council votes
available across the configured rounds.
-/
theorem initializeCase_remainingStepBudget
    (req : InitializeCaseRequest)
    (s : ArbitrationState)
    (hInit : initializeCase req = .ok s) :
    remainingStepBudget s =
      8 + s.policy.max_deliberation_rounds * s.policy.council_size := by
  have hPhase : s.case.phase = "openings" := initializeCase_phase_openings req s hInit
  have hPristine : pristineCouncilState s.case := initializeCase_establishes_pristineCouncilState req s hInit
  have hCount : s.case.council_members.length = s.policy.council_size :=
    initializeCase_establishes_councilMemberCount_eq_policySize req s hInit
  have hSeatedCount : seatedCouncilMemberCount s.case = s.policy.council_size := by
    calc
      seatedCouncilMemberCount s.case = s.case.council_members.length := by
        exact seatedCouncilMemberCount_eq_length_of_all_seated s.case hPristine.2.2
      _ = s.policy.council_size := hCount
  have hVotes : currentRoundVotes s.case = [] := by
    simp [currentRoundVotes, hPristine.1, hPristine.2.1]
  have hOpeningsEmpty : s.case.openings = [] := by
    unfold initializeCase at hInit
    cases hPolicy : validatePolicy req.state.policy with
    | error err =>
        simp [hPolicy] at hInit
        cases hInit
    | ok okv =>
        cases okv
        by_cases hProposition : trimString req.proposition = ""
        · simp [hPolicy, hProposition] at hInit
          cases hInit
        · by_cases hEvidence : trimString req.state.policy.evidence_standard = ""
          · simp [hPolicy, hProposition, hEvidence] at hInit
            cases hInit
          · by_cases hEmpty : req.council_members.isEmpty
            · simp [hPolicy, hProposition, hEvidence, hEmpty] at hInit
              cases hInit
            · by_cases hLength : req.council_members.length != req.state.policy.council_size
              · simp [hPolicy, hProposition, hEvidence, hEmpty, hLength] at hInit
                cases hInit
              · by_cases hDuplicate : hasDuplicateCouncilMemberIds req.council_members
                · simp [hPolicy, hProposition, hEvidence, hEmpty, hLength, hDuplicate] at hInit
                  cases hInit
                · simp [hPolicy, hProposition, hEvidence, hEmpty, hLength, hDuplicate,
                    stateWithCase] at hInit
                  cases hInit
                  rfl
  rw [remainingStepBudget_of_phase_ne_closed s (by simp [hPhase])]
  have hMerits : remainingMeritsSteps s.case = 8 := by
    simp [remainingMeritsSteps, hPhase, hOpeningsEmpty]
  have hRoundsPos : 0 < s.policy.max_deliberation_rounds :=
    initializeCase_establishes_max_deliberation_rounds_positive req s hInit
  have hDelib : remainingDeliberationSteps s = s.policy.max_deliberation_rounds * s.policy.council_size := by
    rw [remainingDeliberationSteps, hPristine.2.1, hVotes, hSeatedCount]
    simp
    have hSub :
        s.policy.max_deliberation_rounds - 1 + 1 = s.policy.max_deliberation_rounds := by
      omega
    have hMul :
        (s.policy.max_deliberation_rounds - 1) * s.policy.council_size + s.policy.council_size =
          ((s.policy.max_deliberation_rounds - 1) + 1) * s.policy.council_size := by
      simpa using
        (Nat.add_mul (s.policy.max_deliberation_rounds - 1) 1 s.policy.council_size).symm
    rw [hMul, hSub]
  rw [hMerits, hDelib]

/--
Every successful indexed public run from initialization has a fixed explicit
length bound.

This is the public Stage 6 theorem.  If a run starts from successful
initialization and then follows `n` successful public `step` transitions, then
`n` cannot exceed the initialized remaining-step budget.
-/
theorem stepPath_length_le_initializedBudget
    (req : InitializeCaseRequest)
    (start s : ArbitrationState)
    (n : Nat)
    (hInit : initializeCase req = .ok start)
    (hPath : StepPath start n s) :
    n ≤ 8 + start.policy.max_deliberation_rounds * start.policy.council_size := by
  have hReachStart : Reachable start := Reachable.init req start hInit
  have hBound := stepPath_length_plus_budget_le start s n hReachStart hPath
  have hBudget : remainingStepBudget start =
      8 + start.policy.max_deliberation_rounds * start.policy.council_size := by
    exact initializeCase_remainingStepBudget req start hInit
  calc
    n ≤ n + remainingStepBudget s := by
      omega
    _ ≤ remainingStepBudget start := hBound
    _ = 8 + start.policy.max_deliberation_rounds * start.policy.council_size := hBudget


end ArbProofs
