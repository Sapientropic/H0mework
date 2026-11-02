import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReview

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReviewHistory

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (ready : NativeReview.Ready model start past) (rival : Opponent model.source.code)

abbrev full := past ++ [(NativeReview.protocol model start past ready, rival)]
abbrev native := IncidentChallenge.native model start (full model start past ready rival)
abbrev family := IncidentChallenge.family model start (full model start past ready rival)
abbrev sourceIndex := IncidentChallenge.sourceIndex model start (full model start past ready rival)
abbrev depth := IncidentChallenge.depth model start (full model start past ready rival)
abbrev row := NativeReview.row model start past ready rival
abbrev item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨0, (EventStep.seed (NativeReview.current model start past)).current, NativeReview.action model start past ready.receiver⟩

theorem items_are_original : StageTrace.items (row model start past ready rival) = [item model start past ready] := by
  unfold StageTrace.items
  rw [(NativeReview.the_actual_owner_submits_the_original_member_request model start past ready rival).2]
  rfl

def index : Fin (StageTrace.items (row model start past ready rival)).length :=
  ⟨0, by rw [items_are_original]; exact Nat.zero_lt_succ 0⟩

theorem actual_row_is_in_the_same_final_source : row model start past ready rival ∈
    StageTrace.records start (full model start past ready rival) := by
  rw [full, StageQueue.records_append]
  exact List.mem_append_right _ List.mem_cons_self

abbrev position := IncidentChallenge.position model start (full model start past ready rival)
  (row model start past ready rival) (actual_row_is_in_the_same_final_source model start past ready rival)
  (index model start past ready rival)

theorem position_item_is_original : (position model start past ready rival).item
    (family model start past ready rival) (sourceIndex model start past ready rival) = item model start past ready := by
  rw [IncidentChallenge.position_item_is_the_actual_item]
  simp only [index, List.get_eq_getElem, items_are_original, List.getElem_cons_zero]

theorem the_actual_visit_has_only_the_original_attempt : Mandate.Challenge.positionsAt
    (family model start past ready rival) (sourceIndex model start past ready rival)
    (position model start past ready rival).ordinal = [position model start past ready rival] := by
  apply WithdrawalHistory.a_single_item_visit_has_its_unique_actual_position
  have actual := IncidentChallenge.actual_trace_items model start (full model start past ready rival)
    (row model start past ready rival) (actual_row_is_in_the_same_final_source model start past ready rival)
  exact (congrArg List.length actual).trans (by rw [items_are_original]; rfl)

variable (original : Native.Authority.Challenge (native model start past ready rival))

abbrev history := Mandate.Challenge.through (family model start past ready rival) (sourceIndex model start past ready rival)
  original (depth model start past ready rival + 2)

-- Test the current target of the complete original history, including every intervening reaffirmation.
def targetReady : Bool :=
  match Mandate.Challenge.through (family model start past ready rival) (sourceIndex model start past ready rival)
      original (position model start past ready rival).ordinal with
  | .closed .. => true
  | .pending target .. => decide (
      Mandate.Challenge.Later (family model start past ready rival) (sourceIndex model start past ready rival)
        (target.claim _ _).position (position model start past ready rival) ∧
      ((position model start past ready rival).item _ _).before.technology = (target.claim _ _).snapshot _ _)

theorem a_paid_actual_attempt_closes_every_ready_original
    (accepted : model.source.code.law.Valid (item model start past ready).before (item model start past ready).request)
    (available : targetReady model start past ready rival original = true) :
    (history model start past ready rival original).isPending _ _ = false := by
  let bound := family model start past ready rival
  let inputs := sourceIndex model start past ready rival
  let attempt := position model start past ready rival
  have unsigned : ¬ Mandate.Challenge.Submission (scope := model.scope) (attempt.item bound inputs).request := by
    rw [position_item_is_original]
    simp [Mandate.Challenge.Submission, NativeReview.action, Mandate.request]
  have noClaim : Mandate.Challenge.read bound inputs attempt = none := by
    simp only [Mandate.Challenge.read, dif_neg unsigned]
  have noRenew : Mandate.Challenge.readReconfirmation bound inputs original attempt = none := by
    simp only [Mandate.Challenge.readReconfirmation, noClaim]
  have signed : Mandate.Challenge.Withdrawal (scope := model.scope) (attempt.item bound inputs).before (attempt.item bound inputs).request := by
    rw [position_item_is_original]
    exact NativeReview.actual_withdrawal_standing model start past ready
  have valid : (Mandate.law model.base model.scope).Valid (attempt.item bound inputs).before (attempt.item bound inputs).request := by
    rw [position_item_is_original, ← model.law_exact]
    exact accepted
  unfold targetReady at available
  have terminal : (Mandate.Challenge.through bound inputs original (attempt.ordinal + 1)).isPending bound inputs = false := by
    rw [Mandate.Challenge.through]
    have singleton : Mandate.Challenge.positionsAt bound inputs attempt.ordinal = [attempt] :=
      the_actual_visit_has_only_the_original_attempt model start past ready rival
    rw [singleton]
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
    (IncidentChallenge.actual_item_is_before_the_native_inventory model start (full model start past ready rival)
      (row model start past ready rival) (actual_row_is_in_the_same_final_source model start past ready rival))

theorem a_refused_actual_attempt_preserves_every_original_status
    (denied : ¬ model.source.code.law.Valid (item model start past ready).before (item model start past ready).request) :
    (Mandate.Challenge.through (family model start past ready rival) (sourceIndex model start past ready rival)
      original ((position model start past ready rival).ordinal + 1)).isPending _ _ =
    (Mandate.Challenge.through (family model start past ready rival) (sourceIndex model start past ready rival)
      original (position model start past ready rival).ordinal).isPending _ _ := by
  apply RefusalHistory.an_all_refused_visit_preserves_the_complete_previous_history
  intro candidate member
  rw [the_actual_visit_has_only_the_original_attempt] at member
  have same := List.mem_singleton.mp member
  rw [same, position_item_is_original, ← model.law_exact]
  exact denied

theorem every_original_has_its_complete_native_history :
    (history model start past ready rival original).state.current.history =
      (history model start past ready rival original).state.generated.events :=
  Mandate.Challenge.actual_native_history _ _ _ _

theorem completion_requires_every_original_not_merely_a_paid_request
    (accepted : model.source.code.law.Valid (item model start past ready).before (item model start past ready).request)
    (covered : ∀ entry ∈ NativeReview.inventory model start (full model start past ready rival),
      targetReady model start past ready rival entry.1 = true) :
    NativeReview.complete model start (full model start past ready rival) = true := by
  apply (NativeReview.completion_covers_every_native_original model start _).mpr
  intro entry inside
  have actual := a_paid_actual_attempt_closes_every_ready_original model start past ready rival entry.1 accepted (covered entry inside)
  -- fullGenerate stores precisely `through` for each original, rather than caller-supplied histories.
  obtain ⟨birth, birthInside, mapped⟩ := List.mem_flatMap.mp inside
  obtain ⟨claim, claimInside, same⟩ := List.mem_map.mp mapped
  cases same
  exact actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReviewHistory
