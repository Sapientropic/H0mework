import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryConsumer
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem every_actual_recovery_ends_its_same_original_in_the_final_root_inventory
    (rounds : Nat) (past : JointResponse.Stages model)
    (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law)
    (member : entry ∈ (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries) :
    let final := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    ∃ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      Feedback.Authority.Trace.challengeImage model.source.code (WithdrawalInquiryRuntime.family model final)
        (WithdrawalInquiryRuntime.sourceIndex model final) original =
      Feedback.Authority.Trace.challengeImage model.source.code
        (RecoveryInventory.family model start entry.past vocabulary encoding law entry.answer)
        (RecoveryInventory.inputs model start entry.past vocabulary encoding law entry.answer) entry.answer.original ∧
      ∃ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
        row.1 = original ∧ row.2.isPending _ _ = false := by
  dsimp only
  have actual := (UnifiedRecoveryTrace.every_record_is_on_the_same_actual_execution
    model start vocabulary encoding law rounds past entry member).2
  obtain ⟨tail, same⟩ := actual
  let recovered := NativeRecovery.full model start entry.past vocabulary encoding law entry.answer
  let cursor := EventHistory.execute start recovered
  have factorization : UnifiedInventorySource.final model start vocabulary encoding law rounds past =
      EventHistory.execute cursor tail := by
    change EventHistory.execute start _ = _
    rw [← same, StageQueue.execute_append]
  rw [factorization]
  have boundary : EventStep.boundary cursor = RecoveryInventory.cut model start entry.past + 1 := by
    change EventStep.boundary (EventHistory.execute start (entry.past ++ [_])) = _
    rw [StageQueue.execute_append]
    rfl
  have inside : entry.answer.original.position.ordinal < EventStep.boundary cursor := by
    have old := entry.answer.qualified.old
    change entry.answer.original.position.ordinal < RecoveryInventory.cut model start entry.past at old
    omega
  let target := ActualInventoryPrefix.originalAt model cursor tail entry.answer.original inside
  have ported := ActualInventoryPrefix.the_actual_original_and_its_entire_native_prefix_are_preserved model cursor tail
    entry.answer.original inside (RecoveryInventory.cut model start entry.past + 1) (by omega)
  have locallyClosed := RecoveryInventory.the_selected_old_original_is_terminal_at_the_completed_cut
    model start entry.past vocabulary encoding law entry.answer
  have closed : CompletedInventory.live (ActualInventoryPrefix.family model)
      (ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail))
      (RecoveryInventory.cut model start entry.past + 1) target = false := ported.2.2.trans locallyClosed
  have endBoundary := IncidentChallenge.execution_advances_the_actual_boundary model cursor tail
  have enough : RecoveryInventory.cut model start entry.past + 1 ≤
      WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail) + 2 := by
    dsimp only [EventStep.boundary, WithdrawalInquiryRuntime.depth] at boundary endBoundary ⊢
    omega
  have terminal := WithdrawalHistory.terminal_through_persists (ActualInventoryPrefix.family model)
    (ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail)) target
    (RecoveryInventory.cut model start entry.past + 1) _ closed enough
  have birth : target.position.ordinal < WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail) + 2 := by
    have kept := (Cross.Programme.replacement_same_item_and_snapshot (ActualInventoryPrefix.family model)
      (EventStep.boundary cursor)
      (Feedback.Authority.Trace.ChallengeTransport.items (ActualInventoryPrefix.family model)
        (inputs := ActualInventoryPrefix.inputs model cursor)
        (nextInputs := ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail))
        (EventStep.boundary cursor) (ActualInventoryPrefix.original_initial_is_preserved cursor tail)
        (ActualInventoryPrefix.actual_events_are_preserved cursor tail)) entry.answer.original inside).2.2.2.1
    change target.position.ordinal = entry.answer.original.position.ordinal at kept
    omega
  have admitted := Native.Authority.every_actual_signed_challenge_is_natively_admitted
    (WithdrawalInquiryRuntime.native model (EventHistory.execute cursor tail)) target.position target
    (CompletedInventory.read_own_position _ _ target) (WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail)) birth
  refine ⟨target, ported.1, ⟨target, through _ _ target
    (WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail) + 2)⟩, ?_, rfl, terminal⟩
  rw [(WithdrawalInquiryRuntime.authority model (EventHistory.execute cursor tail)).current_exact]
  exact admitted

theorem the_one_final_root_consumes_the_entire_actual_recovery_budget_ledger_and_next
    (past : JointResponse.Stages model) :
    let rounds := JointResponse.fuel model start past
    let final := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    let begin := UnifiedInventoryBudget.first model start past
    let count := UnifiedInventoryBudget.span model start vocabulary encoding law rounds past
    let runtime := WithdrawalInquiryRuntime.runtime model final
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).recoveries.length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model) source begin +
        InventoryBirthBudget.arrivals (UnifiedInventorySource.family model) source begin count ∧
    CompletedInventory.pending (UnifiedInventorySource.family model) source (begin + count) +
      InventoryBirthBudget.relieved (UnifiedInventorySource.family model) source begin count =
      CompletedInventory.pending (UnifiedInventorySource.family model) source begin +
        InventoryBirthBudget.arrivals (UnifiedInventorySource.family model) source begin count ∧
    (WithdrawalInquiryRuntime.authority model final).current =
      Native.Authority.fullGenerate (WithdrawalInquiryRuntime.native model final) (WithdrawalInquiryRuntime.depth model final) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    (UnifiedInventorySource.final model start vocabulary encoding law (JointResponse.fuel model start past) past)
  exact ⟨UnifiedInventoryBudget.the_actual_mixed_recovery_budget_is_initial_pending_plus_actual_open_births
      model start vocabulary encoding law _ past,
    UnifiedInventoryBudget.the_one_actual_final_source_has_exact_birth_disposition_and_residual_balance
      model start vocabulary encoding law _ past,
    rooted.1, rooted.2.2.2.1, rooted.2.2.2.2⟩

theorem the_full_final_root_census_has_exact_balance_including_its_additional_birth_slice
    (past : JointResponse.Stages model) :
    let rounds := JointResponse.fuel model start past
    let final := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    let begin := UnifiedInventoryBudget.first model start past
    let count := UnifiedInventoryBudget.span model start vocabulary encoding law rounds past + 1
    (((WithdrawalInquiryRuntime.authority model final).current.challenges).filter
      (fun row => row.2.isPending (UnifiedInventorySource.family model) source)).length +
      InventoryBirthBudget.relieved (UnifiedInventorySource.family model) source begin count =
      CompletedInventory.pending (UnifiedInventorySource.family model) source begin +
        InventoryBirthBudget.arrivals (UnifiedInventorySource.family model) source begin count := by
  dsimp only
  rw [(WithdrawalInquiryRuntime.authority model _).current_exact]
  change ((recordsAt (UnifiedInventorySource.family model)
    (UnifiedInventorySource.inputs model start vocabulary encoding law (JointResponse.fuel model start past) past)
    (WithdrawalInquiryRuntime.depth model _ + 2)).filter (fun row => row.2.isPending
      (UnifiedInventorySource.family model)
      (UnifiedInventorySource.inputs model start vocabulary encoding law (JointResponse.fuel model start past) past))).length + _ = _
  rw [← CompletedInventory.pending_is_the_actual_census_pending_length]
  have balance := InventoryBirthBudget.the_complete_source_window_has_exact_birth_disposition_and_residual_balance
    (UnifiedInventorySource.family model) (UnifiedInventorySource.inputs model start vocabulary encoding law (JointResponse.fuel model start past) past)
    (UnifiedInventoryBudget.first model start past)
    (UnifiedInventoryBudget.span model start vocabulary encoding law (JointResponse.fuel model start past) past + 1)
  have census := UnifiedInventoryBudget.the_final_root_census_extends_one_slice_beyond_the_completed_window
    model start vocabulary encoding law (JointResponse.fuel model start past) past
  rw [← Nat.add_assoc, census] at balance
  exact balance

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryConsumer
