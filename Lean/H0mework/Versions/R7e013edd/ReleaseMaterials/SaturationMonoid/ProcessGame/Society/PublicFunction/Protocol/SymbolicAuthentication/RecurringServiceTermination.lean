import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawServiceWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecurringServiceTermination
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

def initialPending (past : JointResponse.Stages model) :=
  CompletedInventory.pending (ActualInventoryPrefix.family model)
    (ActualInventoryPrefix.inputs model (EventHistory.execute start past))
    (EventStep.boundary (EventHistory.execute start past))

def serviceCapacity (past : JointResponse.Stages model) := initialPending model start past + MixedBirthPotential.capacity model

def deadline (width : Nat) (past : JointResponse.Stages model) := (serviceCapacity model start past + 1) * width

theorem the_service_budget_is_generated_at_the_original_cut
    (rounds : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages) :
    (NativeServiceTrace.records model start vocabulary encoding law rounds past).length ≤ serviceCapacity model start past := by
  have budget := NativeServiceInventory.the_complete_mixed_service_budget_is_initial_pending_plus_finite_source_capacity
    model start vocabulary encoding law rounds past delay compliant
  obtain ⟨tail, same⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past
  let cursor := EventHistory.execute start past
  have conserved := NativeInventoryPrefix.the_complete_pending_inventory_is_preserved model.source.code
    (ActualInventoryPrefix.family model)
    (inputs := ActualInventoryPrefix.inputs model cursor)
    (nextInputs := ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail))
    (EventStep.boundary cursor) (ActualInventoryPrefix.original_initial_is_preserved cursor tail)
    (ActualInventoryPrefix.actual_events_are_preserved cursor tail) (EventStep.boundary cursor) (Nat.le_refl _)
  have finalExact : UnifiedInventorySource.final model start vocabulary encoding law rounds past = EventHistory.execute cursor tail := by
    change EventHistory.execute start _ = _
    rw [← same, OriginQueue.execute_append]
  change CompletedInventory.pending (UnifiedInventorySource.family model)
    (ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail)) (UnifiedInventoryBudget.first model start past) = _ at conserved
  rw [← finalExact] at conserved
  change _ ≤ CompletedInventory.pending (UnifiedInventorySource.family model)
    (ActualInventoryPrefix.inputs model (UnifiedInventorySource.final model start vocabulary encoding law rounds past))
    (UnifiedInventoryBudget.first model start past) + _ at budget
  rw [conserved] at budget
  exact budget

theorem recurring_raw_service_with_source_reserve_forces_joint_completion
    (width : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (_positive : 0 < width)
    (reserve : deadline model start width past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (available : RawServiceWindow.Available model start vocabulary encoding law (serviceCapacity model start past + 1) width past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start width past) past).stages) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start width past) past).status = .jointComplete := by
  have live := UnifiedRunCost.a_source_reserve_keeps_every_actual_prefix_live model start vocabulary encoding law
    (deadline model start width past) past reserve
  have paid := the_service_budget_is_generated_at_the_original_cut model start vocabulary encoding law
    (deadline model start width past) past delay compliant
  cases status : (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start width past) past).status with
  | jointComplete => rfl
  | exhausted =>
    have empty := UnifiedRecoveryRun.exhausted_runs_have_zero_actual_fuel model start vocabulary encoding law
      (deadline model start width past) past status
    omega
  | observationCut =>
    have full := UnifiedRunPrefix.observation_cut_has_all_its_actual_invocations model start vocabulary encoding law
      (deadline model start width past) past status
    have served := RawServiceWindow.complete_actual_windows_pay_distinct_services model start vocabulary encoding law
      (serviceCapacity model start past + 1) width past available full
    dsimp only [deadline] at paid
    omega

theorem the_original_root_consumes_the_conditionally_completed_execution
    (width : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (positive : 0 < width)
    (reserve : deadline model start width past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (available : RawServiceWindow.Available model start vocabulary encoding law (serviceCapacity model start past + 1) width past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start width past) past).stages) :
    let final := UnifiedInventorySource.final model start vocabulary encoding law (deadline model start width past) past
    let runtime := WithdrawalInquiryRuntime.runtime model final
    JointResponse.Clear model start vocabulary encoding law
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start width past) past).stages ∧
    (∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have status := recurring_raw_service_with_source_reserve_forces_joint_completion model start vocabulary encoding law
    width past delay positive reserve available compliant
  have clear := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law
    (deadline model start width past) past status
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (UnifiedInventorySource.final model start vocabulary encoding law (deadline model start width past) past)
  refine ⟨clear, ?_, rooted.2.2.2.1, rooted.2.2.2.2⟩
  intro row member
  rw [(WithdrawalInquiryRuntime.authority model
    (UnifiedInventorySource.final model start vocabulary encoding law (deadline model start width past) past)).current_exact] at member
  exact (NativeReview.completion_covers_every_native_original model start _).mp clear.2.1 row member

theorem the_original_source_sized_producer_completes_within_the_same_deadline
    (width : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (positive : 0 < width)
    (reserve : deadline model start width past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (available : RawServiceWindow.Available model start vocabulary encoding law (serviceCapacity model start past + 1) width past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start width past) past).stages) :
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete ∧
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages.length ≤
      past.length + deadline model start width past * CommunicationWorkBudget.slotAllowance model start := by
  have complete := recurring_raw_service_with_source_reserve_forces_joint_completion model start vocabulary encoding law
    width past delay positive reserve available compliant
  have room : 1 ≤ CommunicationWorkBudget.slotAllowance model start := by unfold CommunicationWorkBudget.slotAllowance; omega
  have lower := Nat.mul_le_mul_left (deadline model start width past) room
  simp only [Nat.mul_one] at lower
  have inside : deadline model start width past ≤ JointResponse.fuel model start past := by omega
  have same := UnifiedRunPrefix.completed_prefix_is_the_same_full_source_run model start vocabulary encoding law
    (deadline model start width past) past inside complete
  refine ⟨same.2, ?_⟩
  rw [same.1]
  exact UnifiedRunCost.actual_invocations_pay_all_physical_stages model start vocabulary encoding law _ past

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecurringServiceTermination
