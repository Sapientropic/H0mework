import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NewbornWithdrawal

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryInventory
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

abbrev family := NativeRecoverySource.family model start past answer.material
abbrev inputs := NativeRecoverySource.sourceIndex model start past answer.material
abbrev cut := NativeRecoverySource.ordinal model start past
abbrev first := NativeRecoverySource.position model start past answer.material 0
abbrev second := NativeRecoverySource.position model start past answer.material 1
abbrev newborn := answer.qualified.renewal.target

theorem the_original_root_census_extends_one_slice_beyond_the_completed_cut :
    NativeRecoverySource.depth model start past answer.material = cut model start past := by
  change (EventHistory.execute start (past ++ [_])).source.history.length + 1 +
    (EventHistory.execute start (past ++ [_])).cut = cut model start past
  rw [StageQueue.execute_append]
  change (EventHistory.execute start past).source.history.length + 1 + ((EventHistory.execute start past).cut + 1) =
    (EventHistory.execute start past).source.history.length + 2 + (EventHistory.execute start past).cut
  omega

theorem the_first_actual_item_decodes_the_generated_newborn :
    Mandate.Challenge.read (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (first model start past vocabulary encoding law answer) =
        some (newborn model start past vocabulary encoding law answer) :=
  NewbornWithdrawal.a_decoded_reconfirmation_is_an_actual_claim _ _ answer.original _ answer.qualified.renewal answer.qualified.renewed

theorem the_second_actual_item_does_not_generate_another_claim :
    Mandate.Challenge.read (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (second model start past vocabulary encoding law answer) = none := by
  have actual := NewbornWithdrawal.a_decoded_attempt_is_at_its_actual_position _ _ _ _ answer.qualified.attempt answer.qualified.withdrawn
  have withdrawal := answer.qualified.attempt.signed
  rw [actual] at withdrawal
  exact NewbornWithdrawal.an_actual_withdrawal_is_not_a_new_claim _ _ _ withdrawal

theorem the_actual_visit_has_exactly_one_source_generated_newborn :
    Mandate.Challenge.claimsAt (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (cut model start past) =
        [newborn model start past vocabulary encoding law answer] :=
  NewbornWithdrawal.the_first_of_two_positions_is_the_complete_newborn_slice _ _ _ _ _
    (NativeRecoverySource.the_two_positions_are_the_complete_actual_visit model start past answer.material)
    (the_first_actual_item_decodes_the_generated_newborn model start past vocabulary encoding law answer)
    (the_second_actual_item_does_not_generate_another_claim model start past vocabulary encoding law answer)

theorem the_generated_newborn_is_terminal_in_the_same_actual_visit :
    CompletedInventory.live (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (cut model start past + 1)
      (newborn model start past vocabulary encoding law answer) = false := by
  exact NewbornWithdrawal.the_newborn_at_the_first_position_is_paid_terminal_at_the_second _ _ _ _ _
    (NativeRecoverySource.the_two_positions_are_the_complete_actual_visit model start past answer.material)
    (the_first_actual_item_decodes_the_generated_newborn model start past vocabulary encoding law answer)
    (the_second_actual_item_does_not_generate_another_claim model start past vocabulary encoding law answer)
    answer.qualified.attempt answer.qualified.withdrawn (by rw [← model.law_exact]; exact answer.qualified.paid)

theorem the_selected_old_original_is_terminal_at_the_completed_cut :
    CompletedInventory.live (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (cut model start past + 1) answer.original = false :=
  ReconfirmationClosure.the_two_actual_positions_close_the_same_original _ _ _ _ _
    (NativeRecoverySource.the_two_positions_are_the_complete_actual_visit model start past answer.material)
    answer.qualified.renewal answer.qualified.renewed answer.qualified.forward answer.qualified.noRenewal
    answer.qualified.attempt answer.qualified.withdrawn (by rw [← model.law_exact]; exact answer.qualified.paid)

theorem the_actual_recovery_does_not_refill_pending_with_its_own_newborn :
    CompletedInventory.openBorn (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (cut model start past) = 0 := by
  have born := the_actual_visit_has_exactly_one_source_generated_newborn model start past vocabulary encoding law answer
  have terminal := the_generated_newborn_is_terminal_in_the_same_actual_visit model start past vocabulary encoding law answer
  simp only [CompletedInventory.openBorn, born]
  simp [terminal]

theorem actual_recovery_strictly_lowers_the_entire_completed_pending_inventory :
    CompletedInventory.pending (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (cut model start past + 1) <
    CompletedInventory.pending (family model start past vocabulary encoding law answer)
      (inputs model start past vocabulary encoding law answer) (cut model start past) :=
  CompletedInventory.one_actual_old_terminalization_without_open_newborns_strictly_lowers_the_complete_inventory _ _ _ answer.original
    answer.qualified.old answer.qualified.pending
    (the_selected_old_original_is_terminal_at_the_completed_cut model start past vocabulary encoding law answer)
    (the_actual_recovery_does_not_refill_pending_with_its_own_newborn model start past vocabulary encoding law answer)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryInventory
