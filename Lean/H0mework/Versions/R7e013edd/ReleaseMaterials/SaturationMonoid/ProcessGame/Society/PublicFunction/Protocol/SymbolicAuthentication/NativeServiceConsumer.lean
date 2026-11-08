import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceInventory

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
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

theorem every_actual_service_archives_its_same_original_in_the_final_root
    (rounds : Nat) (past : JointResponse.Stages model) (entry : NativeServiceTrace.Entry model start vocabulary encoding law)
    (member : entry ∈ NativeServiceTrace.records model start vocabulary encoding law rounds past) :
    let last := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    ∃ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model last),
      Feedback.Authority.Trace.challengeImage model.source.code (WithdrawalInquiryRuntime.family model last)
        (WithdrawalInquiryRuntime.sourceIndex model last) original =
      Feedback.Authority.Trace.challengeImage model.source.code (NativeServiceSource.family model)
        (NativeServiceSource.inputs model start vocabulary encoding law entry.past entry.receipt.action) entry.receipt.original ∧
      ∃ row ∈ (WithdrawalInquiryRuntime.authority model last).current.challenges,
        row.1 = original ∧ row.2.isPending _ _ = false := by
  dsimp only
  obtain ⟨tail, same⟩ := (NativeServiceTrace.every_service_record_is_on_the_same_actual_mixed_execution
    model start vocabulary encoding law rounds past entry member).2
  let cursor := NativeServiceSource.after model start vocabulary encoding law entry.past entry.receipt.action
  have factorization : UnifiedInventorySource.final model start vocabulary encoding law rounds past = EventHistory.execute cursor tail := by
    change EventHistory.execute start _ = _
    rw [← same, OriginQueue.execute_append]
  rw [factorization]
  have boundary := (NativeServiceSource.every_record_is_one_actual_native_stage model start vocabulary encoding law entry.past entry.receipt).2
  change EventStep.boundary cursor = NativeServiceSource.visit model start entry.past + 1 at boundary
  have inside : entry.receipt.original.position.ordinal < EventStep.boundary cursor := by
    have old := entry.receipt.old
    omega
  let target := ActualInventoryPrefix.originalAt model cursor tail entry.receipt.original inside
  have ported := ActualInventoryPrefix.the_actual_original_and_its_entire_native_prefix_are_preserved model cursor tail
    entry.receipt.original inside (NativeServiceSource.visit model start entry.past + 1) (Nat.le_of_eq boundary.symm)
  have closed : CompletedInventory.live (ActualInventoryPrefix.family model)
      (ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail))
      (NativeServiceSource.visit model start entry.past + 1) target = false := ported.2.2.trans entry.receipt.terminal
  have endBoundary := IncidentChallenge.execution_advances_the_actual_boundary model cursor tail
  have enough : NativeServiceSource.visit model start entry.past + 1 ≤
      WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail) + 2 := by
    dsimp only [EventStep.boundary, WithdrawalInquiryRuntime.depth] at boundary endBoundary ⊢
    omega
  have terminal := WithdrawalHistory.terminal_through_persists (ActualInventoryPrefix.family model)
    (ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail)) target
    (NativeServiceSource.visit model start entry.past + 1) _ closed enough
  have birth : target.position.ordinal < WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail) + 2 := by
    have kept := (Cross.Programme.replacement_same_item_and_snapshot (ActualInventoryPrefix.family model)
      (EventStep.boundary cursor)
      (Feedback.Authority.Trace.ChallengeTransport.items (ActualInventoryPrefix.family model)
        (inputs := ActualInventoryPrefix.inputs model cursor)
        (nextInputs := ActualInventoryPrefix.inputs model (EventHistory.execute cursor tail))
        (EventStep.boundary cursor) (ActualInventoryPrefix.original_initial_is_preserved cursor tail)
        (ActualInventoryPrefix.actual_events_are_preserved cursor tail)) entry.receipt.original inside).2.2.2.1
    change target.position.ordinal = entry.receipt.original.position.ordinal at kept
    omega
  have admitted := Native.Authority.every_actual_signed_challenge_is_natively_admitted
    (WithdrawalInquiryRuntime.native model (EventHistory.execute cursor tail)) target.position target
    (CompletedInventory.read_own_position _ _ target) (WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail)) birth
  refine ⟨target, ported.1, ⟨target, Mandate.Challenge.through _ _ target
    (WithdrawalInquiryRuntime.depth model (EventHistory.execute cursor tail) + 2)⟩, ?_, rfl, terminal⟩
  rw [(WithdrawalInquiryRuntime.authority model (EventHistory.execute cursor tail)).current_exact]
  exact admitted

theorem the_original_root_consumes_all_actual_services_their_finite_budget_ledger_and_next
    (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages) :
    let rounds := JointResponse.fuel model start past
    let last := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    let runtime := WithdrawalInquiryRuntime.runtime model last
    (NativeServiceTrace.records model start vocabulary encoding law rounds past).length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model)
        (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
        (UnifiedInventoryBudget.first model start past) + MixedBirthPotential.capacity model ∧
    (∀ entry ∈ NativeServiceTrace.records model start vocabulary encoding law rounds past,
      ∃ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model last),
        Feedback.Authority.Trace.challengeImage model.source.code (WithdrawalInquiryRuntime.family model last)
          (WithdrawalInquiryRuntime.sourceIndex model last) original =
        Feedback.Authority.Trace.challengeImage model.source.code (NativeServiceSource.family model)
          (NativeServiceSource.inputs model start vocabulary encoding law entry.past entry.receipt.action) entry.receipt.original ∧
        ∃ row ∈ (WithdrawalInquiryRuntime.authority model last).current.challenges,
          row.1 = original ∧ row.2.isPending _ _ = false) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model last).process.stateAt
      ((WithdrawalInquiryRuntime.facade model last).process.successor runtime.state) := by
  dsimp only
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    (UnifiedInventorySource.final model start vocabulary encoding law (JointResponse.fuel model start past) past)
  exact ⟨NativeServiceInventory.the_complete_mixed_service_budget_is_initial_pending_plus_finite_source_capacity
      model start vocabulary encoding law _ past delay compliant,
    fun entry member => every_actual_service_archives_its_same_original_in_the_final_root model start vocabulary encoding law _ past entry member,
    rooted.2.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceConsumer
