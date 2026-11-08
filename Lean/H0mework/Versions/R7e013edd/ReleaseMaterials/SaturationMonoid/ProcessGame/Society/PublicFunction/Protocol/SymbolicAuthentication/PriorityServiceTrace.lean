import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityOpportunity

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityServiceTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

-- These folds annotate the original runner's chosen edges; they install no rules.
def first : Nat → JointResponse.Stages model → Option Nat
  | 0, _ => none
  | rounds + 1, past => match JointResponse.step model start vocabulary encoding law past with
    | .advance action =>
      if PriorityOpportunity.rejectionKind (JointResponse.kind model start vocabulary encoding law action) then some past.length
      else first rounds (JointResponse.after model start vocabulary encoding law past action)
    | _ => none

def offers : Nat → JointResponse.Stages model → Nat
  | 0, _ => 0
  | rounds + 1, past => match JointResponse.step model start vocabulary encoding law past with
    | .advance action => (if PriorityOpportunity.offered model start vocabulary encoding law past then 1 else 0) +
        offers rounds (JointResponse.after model start vocabulary encoding law past action)
    | _ => 0

theorem a_selected_rejection_is_served_in_every_actual_extension
    (past later : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (rejected : PriorityOpportunity.rejectionKind (JointResponse.kind model start vocabulary encoding law action) = true)
    (ordered : JointResponse.after model start vocabulary encoding law past action <+: later) :
    RejectionService.ServedAt model start vocabulary encoding law later past.length ∧ past.length < later.length := by
  cases action with
  | communication action =>
    cases action with
    | rejection response selected =>
      obtain ⟨tail, same⟩ := ordered
      rw [← same]
      change RejectionService.ServedAt model start vocabulary encoding law ((past ++ [_]) ++ tail) past.length ∧ _
      have cut : ((past ++ [(RejectionResponse.protocol model start past vocabulary encoding law response,
          OriginQueue.environment start)]) ++ tail).take past.length = past := by simp
      constructor
      · unfold RejectionService.ServedAt
        rw [cut]
        refine ⟨response, selected, OriginQueue.environment start, ?_⟩
        simp
      · simp only [JointResponse.after, UnifiedResponse.after, List.length_append, List.length_singleton]
        omega
    | conflict response selected => contradiction
    | retry response selected => contradiction
    | wait live => contradiction
  | withdrawal ready accepted selected => contradiction
  | refused ready denied selected => contradiction
  | wait live => contradiction

theorem the_first_source_selected_service_is_an_actual_row
    (rounds : Nat) (past : JointResponse.Stages model) (n : Nat)
    (found : first model start vocabulary encoding law rounds past = some n) :
    let full := (JointResponseRun.run model start vocabulary encoding law rounds past).stages
    past.length ≤ n ∧ n < full.length ∧ RejectionService.ServedAt model start vocabulary encoding law full n := by
  induction rounds generalizing past with
  | zero => cases found
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [first, actual] at found; contradiction
    | exhausted empty => simp only [first, actual] at found; contradiction
    | advance action =>
      simp only [first, actual] at found
      simp only [JointResponseRun.run, actual]
      split at found
      · cases Option.some.inj found
        have served := a_selected_rejection_is_served_in_every_actual_extension model start vocabulary encoding law past _ action
          (by assumption) (JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law rounds _)
        exact ⟨Nat.le_refl _, served.2, served.1⟩
      · have next := ih (JointResponse.after model start vocabulary encoding law past action) found
        have lower := (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action).length_le
        exact ⟨Nat.le_trans lower next.1, next.2⟩

theorem absent_service_charges_every_actual_offer_to_a_priority_identity
    (rounds : Nat) (past : JointResponse.Stages model)
    (absent : first model start vocabulary encoding law rounds past = none) :
    PriorityOpportunity.count model start vocabulary encoding law past + offers model start vocabulary encoding law rounds past ≤
      PriorityOpportunity.count model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero =>
    simp only [offers, JointResponseRun.run]
    split
    · exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [offers, JointResponseRun.run, actual]; exact Nat.le_refl _
    | exhausted empty => simp only [offers, JointResponseRun.run, actual]; exact Nat.le_refl _
    | advance action =>
      have rejected : PriorityOpportunity.rejectionKind (JointResponse.kind model start vocabulary encoding law action) ≠ true := by
        intro yes
        simp only [first, actual, yes, if_true] at absent
        contradiction
      have tail : first model start vocabulary encoding law rounds (JointResponse.after model start vocabulary encoding law past action) = none := by
        simpa only [first, actual, if_neg rejected] using absent
      have next := ih _ tail
      have kept := PriorityOpportunity.actual_extension_preserves_the_priority_identity_count model start vocabulary encoding law _ _
        (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action)
      simp only [offers, JointResponseRun.run, actual]
      by_cases available : PriorityOpportunity.offered model start vocabulary encoding law past = true
      · obtain ⟨chosen, selected, priority⟩ := PriorityOpportunity.an_actual_local_offer_is_executed_or_spends_a_higher_priority_identity
          model start vocabulary encoding law past available
        have same := JointResponse.Step.advance.inj (selected.symm.trans actual)
        subst chosen
        have conflict := priority.resolve_right rejected
        have spent := PriorityOpportunity.every_actual_conflict_spends_a_distinct_original_identity model start vocabulary encoding law past action conflict
        rw [if_pos available]
        omega
      · rw [if_neg available]
        omega

theorem enough_actual_local_offers_generate_a_bounded_actual_service_row
    (rounds : Nat) (past : JointResponse.Stages model)
    (enough : IncidentInventory.capacity (code := model.source.code) - PriorityOpportunity.count model start vocabulary encoding law past <
      offers model start vocabulary encoding law rounds past) :
    ∃ n, first model start vocabulary encoding law rounds past = some n ∧
      past.length ≤ n ∧ n < (JointResponseRun.run model start vocabulary encoding law rounds past).stages.length ∧
      RejectionService.ServedAt model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages n := by
  cases found : first model start vocabulary encoding law rounds past with
  | some n => exact ⟨n, rfl, the_first_source_selected_service_is_an_actual_row model start vocabulary encoding law rounds past n found⟩
  | none =>
    have paid := absent_service_charges_every_actual_offer_to_a_priority_identity model start vocabulary encoding law rounds past found
    have bound := IncidentRegistration.the_number_of_actual_native_responses_has_the_original_source_budget
      model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages
    change PriorityOpportunity.count model start vocabulary encoding law _ ≤ _ at bound
    omega

structure Ready (rounds : Nat) (past : JointResponse.Stages model) where
  private mk ::
  index : Nat
  selected : first model start vocabulary encoding law rounds past = some index

inductive Result (rounds : Nat) (past : JointResponse.Stages model) where
  | served (ready : Ready model start vocabulary encoding law rounds past)
  | noRejectionEdge (absent : first model start vocabulary encoding law rounds past = none)
      (budget : PriorityOpportunity.count model start vocabulary encoding law past + offers model start vocabulary encoding law rounds past ≤
        IncidentInventory.capacity (code := model.source.code))

def produce (rounds : Nat) (past : JointResponse.Stages model) : Result model start vocabulary encoding law rounds past :=
  match selected : first model start vocabulary encoding law rounds past with
  | some n => .served ⟨n, selected⟩
  | none => .noRejectionEdge selected
      ((absent_service_charges_every_actual_offer_to_a_priority_identity model start vocabulary encoding law rounds past selected).trans
        (IncidentRegistration.the_number_of_actual_native_responses_has_the_original_source_budget
          model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityServiceTrace
