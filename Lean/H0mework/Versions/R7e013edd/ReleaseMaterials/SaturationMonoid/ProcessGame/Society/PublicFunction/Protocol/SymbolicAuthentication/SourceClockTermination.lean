import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceServiceWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceClockTermination

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := ForwardResponseClock.width model start

abbrev blocks (past : JointResponse.Stages model) := RecurringServiceTermination.serviceCapacity model start past + 1
abbrev deadline (past : JointResponse.Stages model) := RecurringServiceTermination.deadline model start (width model start) past

theorem the_source_clock_and_persistent_local_material_force_completion
    (past : JointResponse.Stages model) (delay : Nat) (positive : 0 < width model start)
    (reserve : deadline model start past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (persistent : SourceServiceWindow.Persistent model start vocabulary encoding law (blocks model start past) past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start past) past).stages) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start past) past).status = .jointComplete := by
  by_contra incomplete
  have unfinished : ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past (deadline model start past)) := by
    intro clear
    exact incomplete (UnifiedRunPrefix.clear_final_stages_have_joint_complete_status model start vocabulary encoding law _ past clear)
  have live := UnifiedRunCost.a_source_reserve_keeps_every_actual_prefix_live model start vocabulary encoding law
    (deadline model start past) past reserve
  have full : (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start past) past).trace.length = deadline model start past := by
    cases status : (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start past) past).status with
    | jointComplete => exact False.elim (incomplete status)
    | exhausted =>
      have empty := UnifiedRecoveryRun.exhausted_runs_have_zero_actual_fuel model start vocabulary encoding law _ past status
      omega
    | observationCut => exact UnifiedRunPrefix.observation_cut_has_all_its_actual_invocations model start vocabulary encoding law _ past status
  have generated := SourceServiceWindow.persistent_source_material_regenerates_every_unfinished_raw_window
    model start vocabulary encoding law (blocks model start past) past reserve persistent full unfinished
  exact incomplete (RecurringServiceTermination.recurring_raw_service_with_source_reserve_forces_joint_completion
    model start vocabulary encoding law (width model start) past delay positive reserve generated compliant)

theorem the_original_source_sized_producer_has_the_generated_physical_deadline
    (past : JointResponse.Stages model) (delay : Nat) (positive : 0 < width model start)
    (reserve : deadline model start past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (persistent : SourceServiceWindow.Persistent model start vocabulary encoding law (blocks model start past) past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start past) past).stages) :
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete ∧
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages.length ≤
      past.length + deadline model start past * CommunicationWorkBudget.slotAllowance model start := by
  have complete := the_source_clock_and_persistent_local_material_force_completion model start vocabulary encoding law
    past delay positive reserve persistent compliant
  have widthPaid : 1 ≤ CommunicationWorkBudget.slotAllowance model start := by unfold CommunicationWorkBudget.slotAllowance; omega
  have cost := Nat.mul_le_mul_left (deadline model start past) widthPaid
  simp only [Nat.mul_one] at cost
  have same := UnifiedRunPrefix.completed_prefix_is_the_same_full_source_run model start vocabulary encoding law
    (deadline model start past) past (by omega) complete
  refine ⟨same.2, ?_⟩
  rw [same.1]
  exact UnifiedRunCost.actual_invocations_pay_all_physical_stages model start vocabulary encoding law _ past

theorem the_original_root_consumes_all_terminal_originals_ledger_and_own_next
    (past : JointResponse.Stages model) (delay : Nat) (positive : 0 < width model start)
    (reserve : deadline model start past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (persistent : SourceServiceWindow.Persistent model start vocabulary encoding law (blocks model start past) past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (deadline model start past) past).stages) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    JointResponse.Clear model start vocabulary encoding law full ∧
    (∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    past <+: full ∧
    StageAccountability.ledger start vocabulary encoding law past <+: StageAccountability.ledger start vocabulary encoding law full ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start full receiver full.length).receipts) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have complete := (the_original_source_sized_producer_has_the_generated_physical_deadline model start vocabulary encoding law
    past delay positive reserve persistent compliant).1
  have clear := UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law _ past complete
  have native := UnifiedRecoveryConsumer.actual_joint_completion_closes_the_entire_final_root_native_inventory
    model start vocabulary encoding law past complete
  have rooted := UnifiedRecoveryConsumer.the_complete_actual_execution_preserves_incidents_receipts_all_native_histories_ledger_and_next
    model start vocabulary encoding law past
  exact ⟨clear, native, rooted.1, rooted.2.1, rooted.2.2.1, rooted.2.2.2.2.1, rooted.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceClockTermination
