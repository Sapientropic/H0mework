import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeService

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeServiceForward
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : JointResponse.Stages model)


variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem raw_source_admission_forces_an_actual_productive_dispatch
    (source : RawNativeService.Source model start past vocabulary encoding law) :
    (NativeServiceSource.produce model start vocabulary encoding law past).isSome = true := by
  obtain ⟨answer, chosen⟩ := RawNativeService.the_actual_raw_source_forces_the_original_recovery
    model start past vocabulary encoding law source
  have selected := UnifiedRecoveryDispatch.an_actual_native_recovery_is_never_lost_to_the_capacity_precheck
    model start vocabulary encoding law past source.unfinished answer chosen
  have terminal := RecoveryInventory.the_selected_old_original_is_terminal_at_the_completed_cut
    model start past vocabulary encoding law answer
  have productive := CompletedInventory.an_actual_old_terminalization_is_counted
    (RecoveryInventory.family model start past vocabulary encoding law answer)
    (RecoveryInventory.inputs model start past vocabulary encoding law answer)
    (RecoveryInventory.cut model start past) answer.original answer.qualified.old answer.qualified.pending terminal
  have recorded := NativeServiceSource.every_productive_native_visit_is_recorded
    model start vocabulary encoding law past (.recovery answer) selected rfl productive
  unfold NativeServiceSource.produce
  split
  · rename_i action observed
    have same := UnifiedRecoveryDispatch.Step.advance.inj (observed.symm.trans selected)
    subst action
    exact recorded
  · rename_i observed
    have impossible := observed (.recovery answer) selected
    cases impossible

theorem the_next_actual_source_visit_has_its_generated_service_record
    (source : RawNativeService.Source model start past vocabulary encoding law) (rounds : Nat) :
    ∃ entry ∈ NativeServiceTrace.records model start vocabulary encoding law (rounds + 1) past,
      entry.past = past := by
  have produced := raw_source_admission_forces_an_actual_productive_dispatch model start past vocabulary encoding law source
  cases actual : NativeServiceSource.produce model start vocabulary encoding law past with
  | none => rw [actual] at produced; cases produced
  | some receipt =>
    have generated : ∃ entry ∈ NativeServiceTrace.here model start vocabulary encoding law past, entry.past = past := by
      simp only [NativeServiceTrace.here, actual]
      exact ⟨_, List.mem_singleton_self _, rfl⟩
    obtain ⟨entry, member, same⟩ := generated
    refine ⟨entry, ?_, same⟩
    rw [NativeServiceTrace.records, receipt.selected]
    exact List.mem_append_left _ member

theorem the_original_root_consumes_the_generated_service_at_its_exact_original_address
    (source : RawNativeService.Source model start past vocabulary encoding law) :
    let rounds := JointResponse.fuel model start past
    let final := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    let runtime := WithdrawalInquiryRuntime.runtime model final
    (∃ entry ∈ NativeServiceTrace.records model start vocabulary encoding law rounds past,
      entry.past = past ∧
      ∃ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
        Feedback.Authority.Trace.challengeImage model.source.code (WithdrawalInquiryRuntime.family model final)
          (WithdrawalInquiryRuntime.sourceIndex model final) original =
        Feedback.Authority.Trace.challengeImage model.source.code (NativeServiceSource.family model)
          (NativeServiceSource.inputs model start vocabulary encoding law entry.past entry.receipt.action) entry.receipt.original ∧
        ∃ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
          row.1 = original ∧ row.2.isPending _ _ = false) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have live : 0 < JointResponse.fuel model start past := source.material.live
  obtain ⟨entry, member, actual⟩ := the_next_actual_source_visit_has_its_generated_service_record
    model start past vocabulary encoding law source (JointResponse.fuel model start past - 1)
  have rounds : JointResponse.fuel model start past - 1 + 1 = JointResponse.fuel model start past := by omega
  rw [rounds] at member
  have archived := NativeServiceConsumer.every_actual_service_archives_its_same_original_in_the_final_root
    model start vocabulary encoding law _ past entry member
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (UnifiedInventorySource.final model start vocabulary encoding law (JointResponse.fuel model start past) past)
  exact ⟨⟨entry, member, actual, archived⟩, rooted.2.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeServiceForward
