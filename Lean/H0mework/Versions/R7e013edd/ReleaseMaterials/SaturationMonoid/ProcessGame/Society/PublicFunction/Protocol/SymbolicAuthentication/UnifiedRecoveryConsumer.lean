import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryTrace

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryConsumer
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

theorem every_actual_recovery_is_consumed_with_its_own_inventory_ledger_and_next
    (rounds : Nat) (past : JointResponse.Stages model)
    (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law)
    (member : entry ∈ (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries) :
    let bound := RecoveryInventory.family model start entry.past vocabulary encoding law entry.answer
    let inputs := RecoveryInventory.inputs model start entry.past vocabulary encoding law entry.answer
    let cut := RecoveryInventory.cut model start entry.past
    let recovered := NativeRecovery.full model start entry.past vocabulary encoding law entry.answer
    let final := EventHistory.execute start recovered
    let runtime := WithdrawalInquiryRuntime.runtime model final
    let authority := WithdrawalInquiryRuntime.authority model final
    past <+: entry.past ∧ recovered <+: (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages ∧
    CompletedInventory.pending bound inputs (cut + 1) < CompletedInventory.pending bound inputs cut ∧
    CompletedInventory.openBorn bound inputs cut = 0 ∧
    (∃ row ∈ authority.current.challenges, row.1 = entry.answer.original ∧ row.2.isPending _ _ = false) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have actual := UnifiedRecoveryTrace.every_record_is_on_the_same_actual_execution model start vocabulary encoding law rounds past entry member
  have rooted := InventoryProgressConsumer.the_same_original_root_consumes_inventory_descent_history_ledger_and_own_next
    model start entry.past vocabulary encoding law entry.answer
  exact ⟨actual.1, actual.2, rooted.1, rooted.2.1, rooted.2.2.1, rooted.2.2.2.2.1, rooted.2.2.2.2.2⟩

theorem the_complete_actual_execution_preserves_incidents_receipts_all_native_histories_ledger_and_next
    (past : JointResponse.Stages model) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    past <+: full ∧
    StageAccountability.ledger start vocabulary encoding law past <+: StageAccountability.ledger start vocabulary encoding law full ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start full receiver full.length).receipts) ∧
    (∀ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      let carried := Mandate.Challenge.through (WithdrawalInquiryRuntime.family model final)
        (WithdrawalInquiryRuntime.sourceIndex model final) original (WithdrawalInquiryRuntime.depth model final + 2)
      carried.state.current.history = carried.state.generated.events) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have ordered := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law
    (JointResponse.fuel model start past) past
  have retained := ordered
  obtain ⟨more, same⟩ := ordered
  have ledger : StageAccountability.ledger start vocabulary encoding law past <+:
      StageAccountability.ledger start vocabulary encoding law (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages := by
    change past ++ more = (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages at same
    rw [← same, StageAccountability.ledger_extends_by_its_generated_next]
    exact List.prefix_append _ _
  have receipts : ∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages receiver
        (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages.length).receipts := by
    intro receiver
    change past ++ more = (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages at same
    rw [← same]
    exact StagePrefix.receipts_survive_actual_extension start past more vocabulary encoding law receiver
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    (EventHistory.execute start (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages)
  exact ⟨retained, ledger, receipts, rooted.2.1, rooted.2.2.2.1, rooted.2.2.2.2⟩

theorem actual_joint_completion_keeps_the_original_communication_native_and_queue_meaning
    (past : JointResponse.Stages model)
    (complete : (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
    UnifiedResponse.Clear model start vocabulary encoding law full ∧
      NativeReview.complete model start full = true ∧ JointResponse.queueClear model start full = true :=
  UnifiedRecoveryRun.completion_contains_all_original_joint_gates model start vocabulary encoding law _ past complete

theorem actual_joint_completion_closes_the_entire_final_root_native_inventory
    (past : JointResponse.Stages model)
    (complete : (UnifiedRecoveryRun.produce model start vocabulary encoding law past).status = .jointComplete) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
    let final := EventHistory.execute start full
    ∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false := by
  dsimp only
  have closed := (actual_joint_completion_keeps_the_original_communication_native_and_queue_meaning
    model start vocabulary encoding law past complete).2.1
  have all := (NativeReview.completion_covers_every_native_original model start
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages).mp closed
  intro row member
  rw [(WithdrawalInquiryRuntime.authority model
    (EventHistory.execute start (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages)).current_exact] at member
  exact all row member

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryConsumer
