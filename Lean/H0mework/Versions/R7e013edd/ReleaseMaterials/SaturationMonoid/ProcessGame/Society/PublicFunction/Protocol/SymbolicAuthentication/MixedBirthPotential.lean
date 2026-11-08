import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthAction

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthPotential
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
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

def funds (past : JointResponse.Stages model) :=
  UnifiedResponseBudget.count model start vocabulary encoding law past +
    RetryExecutionBudget.count model start vocabulary encoding law past * RetryBirthCost.allowance model.source.code
def rank (past : JointResponse.Stages model) :=
  (QueueScheduler.untried model.source.code (OriginQueue.baseline start)
    (EventStep.seed (EventHistory.execute start past)).past).card
def capacity := UnifiedResponseBudget.capacity model +
  RetryProgress.capacity (code := model.source.code) * RetryBirthCost.allowance model.source.code +
    (QueueScheduler.admitted model.source.code).card * QueueBirthSource.cost model.source.code

theorem actual_extension_preserves_funds (past later : JointResponse.Stages model) (ordered : past <+: later) :
    funds model start vocabulary encoding law past ≤ funds model start vocabulary encoding law later :=
  Nat.add_le_add (UnifiedResponseBudget.count_never_decreases model start vocabulary encoding law past later ordered)
    (Nat.mul_le_mul_right _ (RetryExecutionBudget.count_never_decreases model start vocabulary encoding law past later ordered))

omit vocabulary encoding law in
theorem actual_extension_cannot_refill_queue_addresses (past later : JointResponse.Stages model) (ordered : past <+: later) :
    rank model start later ≤ rank model start past := by
  obtain ⟨more, rfl⟩ := ordered
  unfold rank
  rw [OriginQueue.execute_append]
  obtain ⟨events, same⟩ := OriginQueue.an_actual_prefix_retains_the_original_baseline (EventHistory.execute start past) more
  rw [← same]
  exact Finset.card_le_card (QueueScheduler.untried_append_subset model.source.code _ _ _
    (OriginQueue.an_actual_prefix_retains_the_original_baseline start past).length_le)

private theorem zero_birth_is_paid (past : JointResponse.Stages model)
    (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past)
    (zero : MixedBirthAction.births model start vocabulary encoding law past action = 0) :
    MixedBirthAction.births model start vocabulary encoding law past action + funds model start vocabulary encoding law past +
        rank model start (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) * QueueBirthSource.cost model.source.code ≤
      funds model start vocabulary encoding law (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) +
        rank model start past * QueueBirthSource.cost model.source.code := by
  have ordered := UnifiedRecoveryDispatch.every_action_keeps_the_whole_actual_history model start vocabulary encoding law past action
  have paid := actual_extension_preserves_funds model start vocabulary encoding law _ _ ordered
  have queue := Nat.mul_le_mul_right (QueueBirthSource.cost model.source.code)
    (actual_extension_cannot_refill_queue_addresses model start _ _ ordered)
  rw [zero, Nat.zero_add]
  exact Nat.add_le_add paid queue

private theorem response_birth_is_paid (past : JointResponse.Stages model)
    (action : JointResponse.Action model start vocabulary encoding law past)
    (response : UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) = true)
    (born : MixedBirthAction.births model start vocabulary encoding law past (.original action) ≤ 1) :
    MixedBirthAction.births model start vocabulary encoding law past (.original action) + funds model start vocabulary encoding law past +
        rank model start (JointResponse.after model start vocabulary encoding law past action) * QueueBirthSource.cost model.source.code ≤
      funds model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) +
        rank model start past * QueueBirthSource.cost model.source.code := by
  have ordered := JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action
  have registered := UnifiedResponseBudget.an_actual_response_action_generates_registration_progress model start vocabulary encoding law past action response
  have confirmations := Nat.mul_le_mul_right (RetryBirthCost.allowance model.source.code)
    (RetryExecutionBudget.count_never_decreases model start vocabulary encoding law _ _ ordered)
  have queue := Nat.mul_le_mul_right (QueueBirthSource.cost model.source.code)
    (actual_extension_cannot_refill_queue_addresses model start _ _ ordered)
  unfold funds
  omega

theorem an_actual_wait_pays_births_without_spending_a_response_or_retry (past : JointResponse.Stages model) :
    BirthWindow.births model (EventHistory.execute start past) [(SilentWindow.quiet, OriginQueue.environment start)] +
        rank model start (past ++ [(SilentWindow.quiet, OriginQueue.environment start)]) * QueueBirthSource.cost model.source.code ≤
      rank model start past * QueueBirthSource.cost model.source.code := by
  have word := QueueBirthSource.every_actual_wait_pays_its_word_from_a_strict_address_decrease start
    (EventHistory.execute start past) (OriginQueue.an_actual_prefix_retains_the_original_baseline start past).length_le 0
  have born := BirthWindow.actual_single_visit_births_are_paid_by_its_original_word model (EventHistory.execute start past)
    SilentWindow.quiet (OriginQueue.environment start)
  have final : rank model start (past ++ [(SilentWindow.quiet, OriginQueue.environment start)]) =
      QueueBirthSource.rank start (EventHistory.execute start past) 1 := by
    unfold rank
    rw [OriginQueue.execute_append]
    rfl
  rw [final]
  exact Nat.le_trans (Nat.add_le_add_right born _) word

theorem every_actual_mixed_action_pays_its_complete_open_birth_slice (past : JointResponse.Stages model)
    (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :
    MixedBirthAction.births model start vocabulary encoding law past action + funds model start vocabulary encoding law past +
        rank model start (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) * QueueBirthSource.cost model.source.code ≤
      funds model start vocabulary encoding law (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action) +
        rank model start past * QueueBirthSource.cost model.source.code := by
  cases action with
  | recovery answer =>
    exact zero_birth_is_paid model start vocabulary encoding law past _
      (MixedBirthAction.every_actual_recovery_has_no_open_births model start vocabulary encoding law past answer)
  | original action =>
    cases action with
    | withdrawal ready accepted selected =>
      exact zero_birth_is_paid model start vocabulary encoding law past _
        (MixedBirthAction.every_native_withdrawal_or_refusal_has_no_new_births model start past ready)
    | refused ready denied selected =>
      exact zero_birth_is_paid model start vocabulary encoding law past _
        (MixedBirthAction.every_native_withdrawal_or_refusal_has_no_new_births model start past ready)
    | wait live =>
      have born := an_actual_wait_pays_births_without_spending_a_response_or_retry model start past
      have paid := actual_extension_preserves_funds model start vocabulary encoding law past
        (past ++ [(SilentWindow.quiet, OriginQueue.environment start)]) (List.prefix_append _ _)
      dsimp only [MixedBirthAction.births, MixedBirthAction.tail, UnifiedRecoveryDispatch.after, JointResponse.after]
      omega
    | communication action =>
      cases action with
      | wait live =>
        have born := an_actual_wait_pays_births_without_spending_a_response_or_retry model start past
        have paid := actual_extension_preserves_funds model start vocabulary encoding law past
          (past ++ [(SilentWindow.quiet, OriginQueue.environment start)]) (List.prefix_append _ _)
        dsimp only [MixedBirthAction.births, MixedBirthAction.tail, UnifiedRecoveryDispatch.after, JointResponse.after, UnifiedResponse.after]
        omega
      | conflict answer selected =>
        apply response_birth_is_paid model start vocabulary encoding law past _ rfl
        have bound := BirthWindow.actual_single_visit_births_are_paid_by_its_original_word model
          (EventHistory.execute start past) (IncidentResponse.protocol model start past vocabulary encoding law answer) (OriginQueue.environment start)
        rw [IncidentResponse.response_submits_its_original_signature model start past vocabulary encoding law answer (OriginQueue.environment start)] at bound
        exact bound
      | rejection answer selected =>
        apply response_birth_is_paid model start vocabulary encoding law past _ rfl
        have bound := BirthWindow.actual_single_visit_births_are_paid_by_its_original_word model
          (EventHistory.execute start past) (RejectionResponse.protocol model start past vocabulary encoding law answer) (OriginQueue.environment start)
        rw [RejectionResponse.response_submits_its_original_signature model start past vocabulary encoding law answer (OriginQueue.environment start)] at bound
        exact bound
      | retry answer selected =>
        have born := RetryBirthCost.every_actual_retry_funds_all_its_open_births_from_source_cost_words model start past vocabulary encoding law answer
        have ordered := TimedRetry.the_original_history_is_preserved start past vocabulary encoding law answer
        have registrations := UnifiedResponseBudget.count_never_decreases model start vocabulary encoding law _ _ ordered
        have confirmations := Nat.mul_le_mul_right (RetryBirthCost.allowance model.source.code)
          (RetryProgress.every_actual_ready_retry_generates_strict_confirmation_progress encoding start vocabulary law past answer)
        have queue := Nat.mul_le_mul_right (QueueBirthSource.cost model.source.code)
          (actual_extension_cannot_refill_queue_addresses model start _ _ ordered)
        change BirthWindow.births model _ (RetryBirthCost.tail model start past vocabulary encoding law answer) +
          funds model start vocabulary encoding law past + rank model start answer.stages * _ ≤
            funds model start vocabulary encoding law answer.stages + rank model start past * _
        simp only [Nat.add_mul, Nat.one_mul] at confirmations
        change RetryExecutionBudget.count model start vocabulary encoding law past * RetryBirthCost.allowance model.source.code +
          RetryBirthCost.allowance model.source.code ≤ RetryExecutionBudget.count model start vocabulary encoding law answer.stages *
            RetryBirthCost.allowance model.source.code at confirmations
        unfold funds
        omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthPotential
