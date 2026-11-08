import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseEligibility
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationWorkBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityClock
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

def tally (prior : JointResponse.Stages model) : JointResponse.Stages model → Nat
  | [] => 0
  | stage :: tail => (if ResponseEligibility.eligible model start vocabulary encoding law prior then 1 else 0) +
      tally (prior ++ [stage]) tail

theorem tally_append (prior first more : JointResponse.Stages model) :
    tally model start vocabulary encoding law prior (first ++ more) =
      tally model start vocabulary encoding law prior first + tally model start vocabulary encoding law (prior ++ first) more := by
  induction first generalizing prior with
  | nil => simp only [tally, List.nil_append, List.append_nil, Nat.zero_add]
  | cons stage tail ih => simp only [List.cons_append, tally, ih, List.append_assoc, List.nil_append, Nat.add_assoc]

theorem tally_is_bounded_by_actual_slot_count (prior more : JointResponse.Stages model) :
    tally model start vocabulary encoding law prior more ≤ more.length := by
  induction more generalizing prior with
  | nil => exact Nat.le_refl _
  | cons stage tail ih =>
    have next := ih (prior ++ [stage])
    simp only [tally, List.length_cons]
    split <;> omega

theorem one_actual_slot_is_paid_by_its_original_dispatch_offer (prior : JointResponse.Stages model)
    (stage : EventHistory.Stage (code := model.source.code)) :
    tally model start vocabulary encoding law prior [stage] ≤
      if PriorityOpportunity.offered model start vocabulary encoding law prior then 1 else 0 := by
  simp only [tally, Nat.add_zero]
  by_cases actual : ResponseEligibility.eligible model start vocabulary encoding law prior = true
  · have offered := ResponseEligibility.an_actual_primitive_eligible_cut_generates_a_priority_offer model start vocabulary encoding law prior actual
    rw [if_pos actual, if_pos offered]
  · rw [if_neg actual]
    exact Nat.zero_le _

def physical (rounds : Nat) (past : JointResponse.Stages model) :=
  tally model start vocabulary encoding law past
    ((JointResponseRun.run model start vocabulary encoding law rounds past).stages.drop past.length)

theorem every_original_nonretry_action_has_one_actual_slot
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (ordinary : RetryExecutionBudget.retryKind (JointResponse.kind model start vocabulary encoding law action) = false) :
    ∃ stage, JointResponse.after model start vocabulary encoding law past action = past ++ [stage] := by
  cases action with
  | communication action =>
    cases action with
    | conflict response selected => exact ⟨_, rfl⟩
    | rejection response selected => exact ⟨_, rfl⟩
    | retry response selected => contradiction
    | wait live => exact ⟨_, rfl⟩
  | withdrawal ready accepted selected => exact ⟨_, rfl⟩
  | refused ready denied selected => exact ⟨_, rfl⟩
  | wait live => exact ⟨_, rfl⟩

theorem an_actual_macro_charges_nondispatch_opportunities_to_its_own_retry_length
    (past more : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (actual : past ++ more = JointResponse.after model start vocabulary encoding law past action) :
    tally model start vocabulary encoding law past more ≤
      (if PriorityOpportunity.offered model start vocabulary encoding law past then 1 else 0) +
        CommunicationWorkBudget.actionCost model start vocabulary encoding law past action := by
  by_cases retry : RetryExecutionBudget.retryKind (JointResponse.kind model start vocabulary encoding law action) = true
  · cases action with
    | communication action =>
      cases action with
      | retry answer selected =>
        have bounded := tally_is_bounded_by_actual_slot_count model start vocabulary encoding law past more
        have length := congrArg List.length actual
        simp only [List.length_append] at length
        change past.length + more.length = answer.stages.length at length
        change _ ≤ _ + (answer.stages.length - past.length)
        omega
      | conflict answer selected => contradiction
      | rejection answer selected => contradiction
      | wait live => contradiction
    | withdrawal ready accepted selected => contradiction
    | refused ready denied selected => contradiction
    | wait live => contradiction
  · have ordinary := every_original_nonretry_action_has_one_actual_slot model start vocabulary encoding law past action (Bool.eq_false_iff.mpr retry)
    obtain ⟨stage, single⟩ := ordinary
    have same : more = [stage] := List.append_cancel_left (actual.trans single)
    subst more
    have bounded := one_actual_slot_is_paid_by_its_original_dispatch_offer model start vocabulary encoding law past stage
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityClock
