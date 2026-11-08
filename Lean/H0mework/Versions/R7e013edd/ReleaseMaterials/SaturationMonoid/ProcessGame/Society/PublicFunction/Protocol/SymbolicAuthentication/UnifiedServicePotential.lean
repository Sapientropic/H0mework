import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServicePotential
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

-- These are actual registrations and confirmed contents in one history, not local recovery censuses.
def used (past : JointResponse.Stages model) :=
  UnifiedResponseBudget.count model start vocabulary encoding law past +
    RetryExecutionBudget.count model start vocabulary encoding law past * CommunicationWorkBudget.slotAllowance model start

def capacity := UnifiedResponseBudget.capacity model +
  RetryProgress.capacity (code := model.source.code) * CommunicationWorkBudget.slotAllowance model start

def remaining (past : JointResponse.Stages model) := capacity model start - used model start vocabulary encoding law past

theorem actual_extension_preserves_used (past later : JointResponse.Stages model) (ordered : past <+: later) :
    used model start vocabulary encoding law past ≤ used model start vocabulary encoding law later := by
  exact Nat.add_le_add
    (UnifiedResponseBudget.count_never_decreases model start vocabulary encoding law past later ordered)
    (Nat.mul_le_mul_right _ (RetryExecutionBudget.count_never_decreases model start vocabulary encoding law past later ordered))

theorem actual_compliant_history_has_the_original_capacity (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay past) :
    used model start vocabulary encoding law past ≤ capacity model start := by
  exact Nat.add_le_add
    (UnifiedResponseBudget.every_actual_compliant_history_has_a_joint_registration_budget model start vocabulary encoding law past delay compliant)
    (Nat.mul_le_mul_right _ (RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law past))

theorem original_selection_is_retained (past : JointResponse.Stages model)
    (action : JointResponse.Action model start vocabulary encoding law past)
    (selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance (.original action)) :
    JointResponse.step model start vocabulary encoding law past = .advance action := by
  unfold UnifiedRecoveryDispatch.step at selected
  split at selected
  · contradiction
  · split at selected
    · split at selected
      · cases selected
      · unfold UnifiedRecoveryDispatch.original at selected
        cases original : JointResponse.step model start vocabulary encoding law past <;> simp_all
    · unfold UnifiedRecoveryDispatch.original at selected
      cases original : JointResponse.step model start vocabulary encoding law past <;> simp_all

theorem complete_communication_has_no_signature_opportunity (past : JointResponse.Stages model)
    (clear : UnifiedResponse.Clear model start vocabulary encoding law past) :
    SignatureEligibility.eligible model start vocabulary encoding law past = false := by
  have rejection : ResponseEligibility.eligible model start vocabulary encoding law past = false := by
    apply Bool.eq_false_iff.mpr
    intro eligible
    have offered := ResponseEligibility.an_actual_primitive_eligible_cut_generates_a_priority_offer
      model start vocabulary encoding law past eligible
    simp only [PriorityOpportunity.offered, clear.2.1, List.isEmpty_nil, Bool.not_true, Bool.false_and] at offered
    contradiction
  simp only [SignatureEligibility.eligible, SignatureEligibility.incident, clear.1, List.head?_nil, rejection, Bool.or_self]

private theorem original_action_cost (past : JointResponse.Stages model)
    (action : JointResponse.Action model start vocabulary encoding law past) :
    used model start vocabulary encoding law past +
      (if UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) then 1 else 0) +
        CommunicationWorkBudget.actionCost model start vocabulary encoding law past action ≤
      used model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) := by
  have ordered := JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action
  have registrations := UnifiedResponseBudget.count_never_decreases model start vocabulary encoding law _ _ ordered
  have confirmations := RetryExecutionBudget.count_never_decreases model start vocabulary encoding law _ _ ordered
  by_cases response : UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) = true
  · have grew := UnifiedResponseBudget.an_actual_response_action_generates_registration_progress model start vocabulary encoding law past action response
    cases action with
    | communication action =>
      cases action <;> simp_all [JointResponse.kind, UnifiedResponse.kind, UnifiedResponseBudget.responseKind,
        CommunicationWorkBudget.actionCost, used]
      all_goals
        have paid := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) confirmations
        omega
    | withdrawal | refused | wait => contradiction
  · have noResponse := Bool.eq_false_iff.mpr response
    simp only [noResponse, Bool.false_eq_true, if_false, Nat.add_zero]
    by_cases retry : RetryExecutionBudget.retryKind (JointResponse.kind model start vocabulary encoding law action) = true
    · have grew := RetryExecutionBudget.every_actual_retry_action_generates_confirmation_progress model start vocabulary encoding law past action retry
      have paid := Nat.mul_le_mul_right (CommunicationWorkBudget.slotAllowance model start) grew
      cases action with
      | communication action =>
        cases action with
        | retry answer selected =>
          have length := CommunicationWorkBudget.each_actual_retry_has_a_uniform_original_roster_cost model start vocabulary encoding law past answer
          simp only [used, CommunicationWorkBudget.actionCost, Nat.add_mul, Nat.one_mul] at paid ⊢
          omega
        | conflict | rejection | wait => contradiction
      | withdrawal | refused | wait => contradiction
    · have cost : CommunicationWorkBudget.actionCost model start vocabulary encoding law past action = 0 := by
        cases action with
        | communication action => cases action <;> first | rfl | contradiction
        | withdrawal | refused | wait => rfl
      rw [cost, Nat.add_zero]
      exact actual_extension_preserves_used model start vocabulary encoding law _ _ ordered

theorem every_selected_macro_pays_for_its_actual_signature_opportunities
    (past more : JointResponse.Stages model)
    (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past = .advance action)
    (actual : past ++ more = UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) :
    used model start vocabulary encoding law past + SignatureClock.tally model start vocabulary encoding law past more ≤
      used model start vocabulary encoding law (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) := by
  cases action with
  | original action =>
    have offered := SignatureClock.each_original_macro_pays_for_its_signature_opportunities model start vocabulary encoding law
      past more action (original_selection_is_retained model start vocabulary encoding law past action selected) actual
    have paid := original_action_cost model start vocabulary encoding law past action
    change _ ≤ used model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action)
    omega
  | recovery answer =>
    have singleton : more = [(NativeRecoveryMaterial.protocol model start past answer.material, OriginQueue.environment start)] :=
      List.append_cancel_left actual
    subst more
    have quiet := complete_communication_has_no_signature_opportunity model start vocabulary encoding law past answer.communication
    simp only [SignatureClock.tally, quiet, Bool.false_eq_true, if_false, Nat.add_zero]
    exact actual_extension_preserves_used model start vocabulary encoding law _ _
      (UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past (.recovery answer))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServicePotential
