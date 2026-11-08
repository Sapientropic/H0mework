import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthPotential

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthBudget
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open MixedBirthPotential

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem every_actual_mixed_run_has_a_complete_source_funded_birth_balance
    (rounds : Nat) (past more : JointResponse.Stages model)
    (actual : past ++ more = (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages) :
    BirthWindow.births model (EventHistory.execute start past) more + funds model start vocabulary encoding law past +
        rank model start (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages * QueueBirthSource.cost model.source.code ≤
      funds model start vocabulary encoding law (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages +
        rank model start past * QueueBirthSource.cost model.source.code := by
  induction rounds generalizing past more with
  | zero =>
    have same : (UnifiedRecoveryRun.run model start vocabulary encoding law 0 past).stages = past := by
      simp only [UnifiedRecoveryRun.run]; split_ifs <;> rfl
    rw [same] at actual ⊢
    have empty : more = [] := List.append_cancel_left (actual.trans (List.append_nil past).symm)
    rw [empty, BirthWindow.an_empty_window_has_no_births, Nat.zero_add]
  | succ rounds ih =>
    cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear covered =>
      simp only [UnifiedRecoveryRun.run, selected] at actual ⊢
      have empty : more = [] := List.append_cancel_left (actual.trans (List.append_nil past).symm)
      rw [empty, BirthWindow.an_empty_window_has_no_births, Nat.zero_add]
    | exhausted empty =>
      simp only [UnifiedRecoveryRun.run, selected] at actual ⊢
      have nil : more = [] := List.append_cancel_left (actual.trans (List.append_nil past).symm)
      rw [nil, BirthWindow.an_empty_window_has_no_births, Nat.zero_add]
    | advance action =>
      simp only [UnifiedRecoveryRun.run, selected] at actual
      let next := UnifiedRecoveryDispatch.after model start vocabulary encoding law past action
      let chunk := MixedBirthAction.tail model start vocabulary encoding law past action
      have generated : past ++ chunk = next := MixedBirthAction.tail_is_the_literal_actual_extension model start vocabulary encoding law past action
      obtain ⟨tail, retained⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds next
      have full : more = chunk ++ tail := by
        apply List.append_cancel_left (as := past)
        rw [← List.append_assoc, generated, retained]
        exact actual
      have current : EventHistory.execute (EventHistory.execute start past) chunk = EventHistory.execute start next := by
        rw [← OriginQueue.execute_append, generated]
      have paid := every_actual_mixed_action_pays_its_complete_open_birth_slice model start vocabulary encoding law past action
      have continued := ih next tail retained
      simp only [UnifiedRecoveryRun.run, selected]
      rw [full, BirthWindow.actual_append_has_exact_additive_births, current]
      change BirthWindow.births model _ chunk + BirthWindow.births model _ tail + _ + _ ≤ _
      change BirthWindow.births model _ chunk + _ + rank model start next * _ ≤ _ at paid
      dsimp only [next] at paid continued ⊢
      omega

theorem the_actual_mixed_native_arrivals_have_a_finite_source_capacity
    (rounds : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages) :
    InventoryBirthBudget.arrivals (UnifiedInventorySource.family model)
      (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
      (UnifiedInventoryBudget.first model start past)
      (UnifiedInventoryBudget.span model start vocabulary encoding law rounds past) ≤ capacity model := by
  obtain ⟨tail, actual⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past
  have paid := every_actual_mixed_run_has_a_complete_source_funded_birth_balance model start vocabulary encoding law rounds past tail actual
  have registrations := UnifiedResponseBudget.every_actual_compliant_history_has_a_joint_registration_budget model start vocabulary encoding law _ delay compliant
  have confirmations := Nat.mul_le_mul_right (RetryBirthCost.allowance model.source.code)
    (RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages)
  have addresses : rank model start past ≤ (QueueScheduler.admitted model.source.code).card := Finset.card_le_card Finset.sdiff_subset
  have finiteQueue := Nat.mul_le_mul_right (QueueBirthSource.cost model.source.code) addresses
  have length : tail.length = UnifiedInventoryBudget.span model start vocabulary encoding law rounds past := by
    have same := congrArg List.length actual
    simp only [List.length_append] at same
    unfold UnifiedInventoryBudget.span
    omega
  unfold BirthWindow.births at paid
  rw [← OriginQueue.execute_append, actual, length] at paid
  change InventoryBirthBudget.arrivals (UnifiedInventorySource.family model)
    (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
    (UnifiedInventoryBudget.first model start past) (UnifiedInventoryBudget.span model start vocabulary encoding law rounds past) + _ + _ ≤ _ at paid
  change RetryExecutionBudget.count model start vocabulary encoding law
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages * RetryBirthCost.allowance model.source.code ≤
      RetryProgress.capacity (code := model.source.code) * RetryBirthCost.allowance model.source.code at confirmations
  unfold funds at paid
  unfold capacity
  omega

theorem all_actual_mixed_recoveries_are_funded_by_initial_pending_and_finite_source_capacity
    (rounds : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model)
        (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
        (UnifiedInventoryBudget.first model start past) + capacity model := by
  have actual := UnifiedInventoryBudget.the_actual_mixed_recovery_budget_is_initial_pending_plus_actual_open_births
    model start vocabulary encoding law rounds past
  have births := the_actual_mixed_native_arrivals_have_a_finite_source_capacity model start vocabulary encoding law rounds past delay compliant
  exact actual.trans (Nat.add_le_add_left births _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthBudget
