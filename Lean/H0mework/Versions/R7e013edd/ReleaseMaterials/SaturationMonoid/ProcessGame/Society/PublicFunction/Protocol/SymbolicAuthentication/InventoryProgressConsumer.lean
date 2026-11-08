import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InventoryBirthBudget
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoveryConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InventoryProgressConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (answer : NativeRecovery.Ready model start past vocabulary encoding law)

theorem the_actual_recovery_spends_old_inventory_without_an_open_birth :
    let bound := RecoveryInventory.family model start past vocabulary encoding law answer
    let inputs := RecoveryInventory.inputs model start past vocabulary encoding law answer
    let cut := RecoveryInventory.cut model start past
    InventoryBirthBudget.productive bound inputs cut 1 = 1 ∧
    InventoryBirthBudget.arrivals bound inputs cut 1 = 0 ∧
    CompletedInventory.pending bound inputs (cut + 1) < CompletedInventory.pending bound inputs cut := by
  dsimp only
  have closed := CompletedInventory.an_actual_old_terminalization_is_counted _ _ _ answer.original
    answer.qualified.old answer.qualified.pending
    (RecoveryInventory.the_selected_old_original_is_terminal_at_the_completed_cut model start past vocabulary encoding law answer)
  refine ⟨?_, ?_, RecoveryInventory.actual_recovery_strictly_lowers_the_entire_completed_pending_inventory model start past vocabulary encoding law answer⟩
  · simp only [InventoryBirthBudget.productive, Nat.add_zero, if_pos closed]
  · simpa only [InventoryBirthBudget.arrivals, Nat.add_zero, Nat.zero_add] using
      RecoveryInventory.the_actual_recovery_does_not_refill_pending_with_its_own_newborn model start past vocabulary encoding law answer

theorem the_actual_root_census_has_the_same_complete_inventory_count :
    let bound := RecoveryInventory.family model start past vocabulary encoding law answer
    let inputs := RecoveryInventory.inputs model start past vocabulary encoding law answer
    let cut := RecoveryInventory.cut model start past
    let final := EventHistory.execute start (NativeRecovery.full model start past vocabulary encoding law answer)
    (((WithdrawalInquiryRuntime.authority model final).current.challenges).filter
      (fun row => row.2.isPending bound inputs)).length = CompletedInventory.pending bound inputs (cut + 2) := by
  dsimp only
  rw [(WithdrawalInquiryRuntime.authority model
    (EventHistory.execute start (NativeRecovery.full model start past vocabulary encoding law answer))).current_exact]
  change ((Mandate.Challenge.recordsAt _ _ (NativeRecoverySource.depth model start past answer.material + 2)).filter _).length = _
  rw [RecoveryInventory.the_original_root_census_extends_one_slice_beyond_the_completed_cut model start past vocabulary encoding law answer]
  exact (CompletedInventory.pending_is_the_actual_census_pending_length _ _ _).symm

theorem the_complete_root_progress_bound_retains_every_additional_actual_birth :
    let bound := RecoveryInventory.family model start past vocabulary encoding law answer
    let inputs := RecoveryInventory.inputs model start past vocabulary encoding law answer
    let cut := RecoveryInventory.cut model start past
    let final := EventHistory.execute start (NativeRecovery.full model start past vocabulary encoding law answer)
    (((WithdrawalInquiryRuntime.authority model final).current.challenges).filter
      (fun row => row.2.isPending bound inputs)).length + 1 ≤
        CompletedInventory.pending bound inputs cut + CompletedInventory.openBorn bound inputs (cut + 1) := by
  dsimp only
  rw [the_actual_root_census_has_the_same_complete_inventory_count model start past vocabulary encoding law answer]
  have first := CompletedInventory.every_completed_cut_has_exact_source_birth_and_disposition_balance
    (RecoveryInventory.family model start past vocabulary encoding law answer)
    (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past)
  have second := CompletedInventory.every_completed_cut_has_exact_source_birth_and_disposition_balance
    (RecoveryInventory.family model start past vocabulary encoding law answer)
    (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past + 1)
  have noRefill := RecoveryInventory.the_actual_recovery_does_not_refill_pending_with_its_own_newborn model start past vocabulary encoding law answer
  have spent := CompletedInventory.an_actual_old_terminalization_is_counted _ _ _ answer.original
    answer.qualified.old answer.qualified.pending
    (RecoveryInventory.the_selected_old_original_is_terminal_at_the_completed_cut model start past vocabulary encoding law answer)
  change CompletedInventory.pending (RecoveryInventory.family model start past vocabulary encoding law answer)
      (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past + 2) +
    CompletedInventory.closedOld (RecoveryInventory.family model start past vocabulary encoding law answer)
      (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past + 1) =
    CompletedInventory.pending (RecoveryInventory.family model start past vocabulary encoding law answer)
      (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past + 1) +
    CompletedInventory.openBorn (RecoveryInventory.family model start past vocabulary encoding law answer)
      (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past + 1) at second
  change 0 < CompletedInventory.closedOld (RecoveryInventory.family model start past vocabulary encoding law answer)
    (RecoveryInventory.inputs model start past vocabulary encoding law answer) (RecoveryInventory.cut model start past) at spent
  omega

theorem the_same_original_root_consumes_inventory_descent_history_ledger_and_own_next :
    let bound := RecoveryInventory.family model start past vocabulary encoding law answer
    let inputs := RecoveryInventory.inputs model start past vocabulary encoding law answer
    let cut := RecoveryInventory.cut model start past
    let full := NativeRecovery.full model start past vocabulary encoding law answer
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    let authority := WithdrawalInquiryRuntime.authority model final
    CompletedInventory.pending bound inputs (cut + 1) < CompletedInventory.pending bound inputs cut ∧
    CompletedInventory.openBorn bound inputs cut = 0 ∧
    (∃ row ∈ authority.current.challenges, row.1 = answer.original ∧ row.2.isPending _ _ = false) ∧
    full <+: (NativeRecoveryConsumer.reenter model start past vocabulary encoding law answer).stages ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have rooted := NativeRecoveryConsumer.the_original_root_consumes_the_actual_recovery_and_preserves_it_for_joint_reentry
    model start past vocabulary encoding law answer
  exact ⟨RecoveryInventory.actual_recovery_strictly_lowers_the_entire_completed_pending_inventory model start past vocabulary encoding law answer,
    RecoveryInventory.the_actual_recovery_does_not_refill_pending_with_its_own_newborn model start past vocabulary encoding law answer,
    rooted.2.2.1, rooted.2.2.2.2.1, rooted.2.2.2.2.2.1, rooted.2.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InventoryProgressConsumer
