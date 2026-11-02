import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalWindow

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawal

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open IncidentWithdrawalNative

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (ready : IncidentWithdrawal.Ready model start past vocabulary encoding law)
  (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code)))
  (answer : IncidentResponse.Answer model start vocabulary encoding law)

abbrev row := StageTrace.material (EventHistory.execute start answer.pastStages) answer.actualRule answer.rival
abbrev item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨0, (EventStep.seed (EventHistory.execute start answer.pastStages)).current,
    IncidentResponse.signature model answer.response.incident.receiver⟩

theorem items_are_original : StageTrace.items (row model start vocabulary encoding law answer) =
    [item model start vocabulary encoding law answer] := by
  unfold StageTrace.items
  rw [(IncidentResponse.every_answer_has_the_actual_owned_signature model start vocabulary encoding law answer).2]
  rfl

def index : Fin (StageTrace.items (row model start vocabulary encoding law answer)).length :=
  ⟨0, by rw [items_are_original]; exact Nat.zero_lt_succ 0⟩

theorem item_is_original : (StageTrace.items (row model start vocabulary encoding law answer)).get
    (index model start vocabulary encoding law answer) = item model start vocabulary encoding law answer := by
  simp only [index, List.get_eq_getElem, items_are_original, List.getElem_cons_zero]

variable (actual : answer ∈ IncidentResponse.journal model start past vocabulary encoding law)

include actual in
theorem birth_is_in_the_common_final_source : row model start vocabulary encoding law answer ∈
    StageTrace.records start (full model start past vocabulary encoding law ready rival more) := by
  have inside := IncidentResponse.every_registered_response_is_an_actual_history_row model start past vocabulary encoding law answer actual
  rw [full, StageQueue.records_append, StageQueue.records_append]
  exact List.mem_append_left _ (List.mem_append_left _ inside)

abbrev position := IncidentChallenge.position model start (full model start past vocabulary encoding law ready rival more)
  (row model start vocabulary encoding law answer)
  (birth_is_in_the_common_final_source model start past vocabulary encoding law ready rival more answer actual)
  (index model start vocabulary encoding law answer)

include actual in
theorem position_item_is_original : (position model start past vocabulary encoding law ready rival more answer actual).item
    (family model start past vocabulary encoding law ready rival more) (sourceIndex model start past vocabulary encoding law ready rival more) =
      item model start vocabulary encoding law answer :=
  (IncidentChallenge.position_item_is_the_actual_item _ _ _ _ _ _).trans (item_is_original _ _ _ _ _ _)

include actual in
theorem birth_precedes_the_common_attempt :
    (position model start past vocabulary encoding law ready rival more answer actual).ordinal <
      (attemptPosition model start past vocabulary encoding law ready rival more).ordinal := by
  obtain ⟨tail, same⟩ := IncidentResponse.every_answer_retains_its_actual_source_prefix model start past vocabulary encoding law answer actual
  have lengths := congrArg List.length same
  simp only [IncidentResponse.Answer.birthStages, List.length_append, List.length_singleton] at lengths
  change EventStep.boundary (EventHistory.execute start answer.pastStages) < EventStep.boundary (EventHistory.execute start past)
  rw [IncidentChallenge.execution_advances_the_actual_boundary model start answer.pastStages,
    IncidentChallenge.execution_advances_the_actual_boundary model start past]
  omega

abbrev read := Mandate.Challenge.read (family model start past vocabulary encoding law ready rival more)
  (sourceIndex model start past vocabulary encoding law ready rival more)
  (position model start past vocabulary encoding law ready rival more answer actual)

include actual in
theorem every_journal_answer_generates_its_original_claim :
    ∃ claim : Native.Authority.Challenge (native model start past vocabulary encoding law ready rival more),
      read model start past vocabulary encoding law ready rival more answer actual = some claim ∧
      claim.position = position model start past vocabulary encoding law ready rival more answer actual ∧
      claim.snapshot (family model start past vocabulary encoding law ready rival more)
        (sourceIndex model start past vocabulary encoding law ready rival more) = IncidentWithdrawal.snapshot model start vocabulary encoding law answer ∧
      (⟨claim, Mandate.Challenge.through (family model start past vocabulary encoding law ready rival more)
        (sourceIndex model start past vocabulary encoding law ready rival more) claim (depth model start past vocabulary encoding law ready rival more + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native model start past vocabulary encoding law ready rival more) original) ∈
        (Native.Authority.fullGenerate (native model start past vocabulary encoding law ready rival more)
          (depth model start past vocabulary encoding law ready rival more)).challenges := by
  have original := item_is_original model start vocabulary encoding law answer
  obtain ⟨claim, decoded, pos, installed⟩ := IncidentChallenge.actual_signed_active_item_generates_a_native_claim
    model start (full model start past vocabulary encoding law ready rival more)
    (row model start vocabulary encoding law answer)
    (birth_is_in_the_common_final_source model start past vocabulary encoding law ready rival more answer actual)
    (index model start vocabulary encoding law answer)
    (by rw [original]; exact answer.response.standing) (by rw [original]; exact answer.response.valid)
    (by rw [original]; exact answer.response.active)
  refine ⟨claim, decoded, pos, ?_, installed⟩
  unfold Mandate.Challenge.Claim.snapshot
  rw [pos, position_item_is_original model start past vocabulary encoding law ready rival more answer actual]

def claim : Native.Authority.Challenge (native model start past vocabulary encoding law ready rival more) :=
  match decoded : read model start past vocabulary encoding law ready rival more answer actual with
  | some original => original
  | none => False.elim (by
      obtain ⟨original, existsRead, _⟩ := every_journal_answer_generates_its_original_claim model start past vocabulary encoding law ready rival more answer actual
      rw [decoded] at existsRead
      cases existsRead)

theorem claim_is_the_actual_read : read model start past vocabulary encoding law ready rival more answer actual =
    some (claim model start past vocabulary encoding law ready rival more answer actual) := by
  unfold claim
  split
  · assumption
  · rename_i absent
    obtain ⟨original, existsRead, _⟩ := every_journal_answer_generates_its_original_claim model start past vocabulary encoding law ready rival more answer actual
    rw [absent] at existsRead
    cases existsRead

theorem the_generated_claim_retains_birth_snapshot_and_inventory :
    (claim model start past vocabulary encoding law ready rival more answer actual).position =
        position model start past vocabulary encoding law ready rival more answer actual ∧
    (claim model start past vocabulary encoding law ready rival more answer actual).snapshot
      (family model start past vocabulary encoding law ready rival more) (sourceIndex model start past vocabulary encoding law ready rival more) =
        IncidentWithdrawal.snapshot model start vocabulary encoding law answer ∧
    (⟨claim model start past vocabulary encoding law ready rival more answer actual,
      Mandate.Challenge.through (family model start past vocabulary encoding law ready rival more)
        (sourceIndex model start past vocabulary encoding law ready rival more)
        (claim model start past vocabulary encoding law ready rival more answer actual)
        (depth model start past vocabulary encoding law ready rival more + 2)⟩ :
      Sigma fun original => Native.Authority.ChallengeHistory (native model start past vocabulary encoding law ready rival more) original) ∈
      (Native.Authority.fullGenerate (native model start past vocabulary encoding law ready rival more)
        (depth model start past vocabulary encoding law ready rival more)).challenges := by
  obtain ⟨original, decoded, facts⟩ := every_journal_answer_generates_its_original_claim model start past vocabulary encoding law ready rival more answer actual
  have same := Option.some.inj ((claim_is_the_actual_read model start past vocabulary encoding law ready rival more answer actual).symm.trans decoded)
  rw [same]
  exact facts

def compatible : Bool := decide (IncidentWithdrawal.snapshot model start vocabulary encoding law answer =
  (attemptItem model start past vocabulary encoding law ready).before.technology)

abbrev history := Mandate.Challenge.through (family model start past vocabulary encoding law ready rival more)
  (sourceIndex model start past vocabulary encoding law ready rival more)
  (claim model start past vocabulary encoding law ready rival more answer actual)
  (depth model start past vocabulary encoding law ready rival more + 2)

def targetReady : Bool :=
  match Mandate.Challenge.through (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more)
      (claim model start past vocabulary encoding law ready rival more answer actual)
      (attemptPosition model start past vocabulary encoding law ready rival more).ordinal with
  | .closed .. => true
  | .pending target .. => decide (
      Mandate.Challenge.Later (family model start past vocabulary encoding law ready rival more)
        (sourceIndex model start past vocabulary encoding law ready rival more) (target.claim _ _).position
        (attemptPosition model start past vocabulary encoding law ready rival more) ∧
      ((attemptPosition model start past vocabulary encoding law ready rival more).item _ _).before.technology =
        (target.claim _ _).snapshot _ _)

theorem a_common_paid_attempt_closes_every_ready_actual_target
    (accepted : model.source.code.law.Valid (attemptItem model start past vocabulary encoding law ready).before
      (attemptItem model start past vocabulary encoding law ready).request)
    (available : targetReady model start past vocabulary encoding law ready rival more answer actual = true) :
    (history model start past vocabulary encoding law ready rival more answer actual).isPending _ _ = false := by
  let bound := family model start past vocabulary encoding law ready rival more
  let inputs := sourceIndex model start past vocabulary encoding law ready rival more
  let original := claim model start past vocabulary encoding law ready rival more answer actual
  let attempt := attemptPosition model start past vocabulary encoding law ready rival more
  have unsigned : ¬ Mandate.Challenge.Submission (scope := model.scope) (attempt.item bound inputs).request := by
    rw [attempt_position_item_is_original]
    simp [Mandate.Challenge.Submission, IncidentWithdrawal.action, Mandate.request]
  have noClaim : Mandate.Challenge.read bound inputs attempt = none := by
    simp only [Mandate.Challenge.read, dif_neg unsigned]
  have noRenew : Mandate.Challenge.readReconfirmation bound inputs original attempt = none := by
    simp only [Mandate.Challenge.readReconfirmation, noClaim]
  have signed : Mandate.Challenge.Withdrawal (scope := model.scope) (attempt.item bound inputs).before (attempt.item bound inputs).request := by
    rw [attempt_position_item_is_original]
    exact IncidentWithdrawal.request_has_actual_withdrawal_standing _ _ _ _ _ _ ready
  have valid : (Mandate.law model.base model.scope).Valid (attempt.item bound inputs).before (attempt.item bound inputs).request := by
    rw [attempt_position_item_is_original, ← model.law_exact]
    exact accepted
  have single := IncidentChallenge.actual_trace_items model start (full model start past vocabulary encoding law ready rival more)
    (attemptRow model start past vocabulary encoding law ready rival) (attempt_is_in_the_same_final_source model start past vocabulary encoding law ready rival more)
  have singleton : Mandate.Challenge.positionsAt bound inputs attempt.ordinal = [attempt] :=
    WithdrawalHistory.a_single_item_visit_has_its_unique_actual_position _ _ _
      ((congrArg List.length single).trans (by rw [attempt_items_are_original]; rfl))
  unfold targetReady at available
  have terminal : (Mandate.Challenge.through bound inputs original (attempt.ordinal + 1)).isPending bound inputs = false := by
    rw [Mandate.Challenge.through, singleton]
    simp only [List.foldl_cons, List.foldl_nil]
    cases current : Mandate.Challenge.through bound inputs original attempt.ordinal with
    | closed state archive slots => rfl
    | pending target state slots =>
      rw [current] at available
      have checked := of_decide_eq_true available
      have recognized : Mandate.Challenge.Later bound inputs (target.claim bound inputs).position attempt ∧
          Mandate.Challenge.Withdrawal (scope := model.scope) (attempt.item bound inputs).before (attempt.item bound inputs).request ∧
          (attempt.item bound inputs).before.technology = (target.claim bound inputs).snapshot bound inputs :=
        ⟨checked.1, signed, checked.2⟩
      simp only [Mandate.Challenge.History.receive, noRenew, Mandate.Challenge.readAttempt,
        dif_pos recognized, dif_pos valid, Mandate.Challenge.History.isPending]
  exact WithdrawalHistory.terminal_through_persists bound inputs original (attempt.ordinal + 1) _ terminal
    (IncidentChallenge.actual_item_is_before_the_native_inventory model start
      (full model start past vocabulary encoding law ready rival more) (attemptRow model start past vocabulary encoding law ready rival)
      (attempt_is_in_the_same_final_source model start past vocabulary encoding law ready rival more))

theorem an_incompatible_snapshot_cannot_use_the_common_attempt
    (different : compatible model start past vocabulary encoding law ready answer = false) :
    Mandate.Challenge.readAttempt (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more)
      (claim model start past vocabulary encoding law ready rival more answer actual)
      (attemptPosition model start past vocabulary encoding law ready rival more) = none := by
  have snapshot := (the_generated_claim_retains_birth_snapshot_and_inventory model start past vocabulary encoding law ready rival more answer actual).2.1
  have mismatch : ¬ ((attemptPosition model start past vocabulary encoding law ready rival more).item _ _).before.technology =
      (claim model start past vocabulary encoding law ready rival more answer actual).snapshot _ _ := by
    rw [attempt_position_item_is_original, snapshot]
    exact fun equal => (of_decide_eq_false different) equal.symm
  unfold Mandate.Challenge.readAttempt
  exact dif_neg (fun checked => mismatch checked.2.2)

theorem a_common_paid_attempt_archives_every_compatible_answer
    (accepted : model.source.code.law.Valid (attemptItem model start past vocabulary encoding law ready).before
      (attemptItem model start past vocabulary encoding law ready).request)
    (sameSnapshot : compatible model start past vocabulary encoding law ready answer = true) :
    (history model start past vocabulary encoding law ready rival more answer actual).isPending _ _ = false := by
  have facts := the_generated_claim_retains_birth_snapshot_and_inventory model start past vocabulary encoding law ready rival more answer actual
  have birthActual := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source start
    (full model start past vocabulary encoding law ready rival more) (row model start vocabulary encoding law answer)
    (birth_is_in_the_common_final_source model start past vocabulary encoding law ready rival more answer actual)
  have attemptActual := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source start
    (full model start past vocabulary encoding law ready rival more) (attemptRow model start past vocabulary encoding law ready rival)
    (attempt_is_in_the_same_final_source model start past vocabulary encoding law ready rival more)
  have birthCurrent : MandateEvolution.currentAt model.base model.scope (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more)
      (position model start past vocabulary encoding law ready rival more answer actual).ordinal =
        (row model start vocabulary encoding law answer).before.current := birthActual.1.symm
  have attemptCurrent : MandateEvolution.currentAt model.base model.scope (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more)
      (attemptPosition model start past vocabulary encoding law ready rival more).ordinal =
        (attemptRow model start past vocabulary encoding law ready rival).before.current := attemptActual.1.symm
  have birth : (MandateEvolution.currentAt model.base model.scope (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more)
      (claim model start past vocabulary encoding law ready rival more answer actual).position.ordinal).technology =
        (claim model start past vocabulary encoding law ready rival more answer actual).snapshot _ _ := by
    rw [facts.1, birthCurrent, facts.2.1]
    rfl
  have same : (MandateEvolution.currentAt model.base model.scope (family model start past vocabulary encoding law ready rival more)
      (sourceIndex model start past vocabulary encoding law ready rival more)
      (claim model start past vocabulary encoding law ready rival more answer actual).position.ordinal).technology =
        (MandateEvolution.currentAt model.base model.scope (family model start past vocabulary encoding law ready rival more)
          (sourceIndex model start past vocabulary encoding law ready rival more)
          (attemptPosition model start past vocabulary encoding law ready rival more).ordinal).technology := by
    rw [facts.1, birthCurrent, attemptCurrent]
    exact of_decide_eq_true sameSnapshot
  have single := IncidentChallenge.actual_trace_items model start (full model start past vocabulary encoding law ready rival more)
    (attemptRow model start past vocabulary encoding law ready rival) (attempt_is_in_the_same_final_source model start past vocabulary encoding law ready rival more)
  apply WithdrawalHistory.an_actual_paid_withdrawal_closes_the_complete_native_history
    (family model start past vocabulary encoding law ready rival more) (sourceIndex model start past vocabulary encoding law ready rival more)
    (claim model start past vocabulary encoding law ready rival more answer actual) (attemptPosition model start past vocabulary encoding law ready rival more)
    (by rw [facts.1]; exact birth_precedes_the_common_attempt model start past vocabulary encoding law ready rival more answer actual)
    birth same
    (WithdrawalHistory.a_single_item_visit_has_its_unique_actual_position _ _ _
      ((congrArg List.length single).trans (by rw [attempt_items_are_original]; rfl)))
  · rw [attempt_position_item_is_original, attemptCurrent]
    rfl
  · rw [attempt_position_item_is_original]
    exact IncidentWithdrawal.request_has_actual_withdrawal_standing _ _ _ _ _ _ ready
  · rw [attempt_position_item_is_original, ← model.law_exact]
    exact accepted
  · exact IncidentChallenge.actual_item_is_before_the_native_inventory model start
      (full model start past vocabulary encoding law ready rival more) (attemptRow model start past vocabulary encoding law ready rival)
      (attempt_is_in_the_same_final_source model start past vocabulary encoding law ready rival more)

def entry : Sigma fun original => Native.Authority.ChallengeHistory (native model start past vocabulary encoding law ready rival more) original :=
  Sigma.mk (claim model start past vocabulary encoding law ready rival more answer actual)
    (history model start past vocabulary encoding law ready rival more answer actual)

def inventory := (IncidentResponse.journal model start past vocabulary encoding law).attach.map fun original =>
  entry model start past vocabulary encoding law ready rival more original.val original.property

theorem every_generated_row_is_in_the_same_complete_inventory :
    ∀ entry ∈ inventory model start past vocabulary encoding law ready rival more,
      entry ∈ (Native.Authority.fullGenerate (native model start past vocabulary encoding law ready rival more)
        (depth model start past vocabulary encoding law ready rival more)).challenges := by
  intro entry inside
  obtain ⟨answer, _, rfl⟩ := List.mem_map.mp inside
  exact (the_generated_claim_retains_birth_snapshot_and_inventory model start past vocabulary encoding law ready rival more answer.val answer.property).2.2

theorem inventory_retains_every_response : (inventory model start past vocabulary encoding law ready rival more).length =
    (IncidentResponse.journal model start past vocabulary encoding law).length := by
  simp only [inventory, List.length_map, List.length_attach]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawal
