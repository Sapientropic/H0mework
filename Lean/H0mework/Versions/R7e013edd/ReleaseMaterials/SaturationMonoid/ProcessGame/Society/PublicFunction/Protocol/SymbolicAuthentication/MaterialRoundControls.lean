import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Action)
open MaterialRoundSource

abbrev parent := OwnedQuorumSource.initial
abbrev old : Bound := ⟨RenewedQuorumMaterial.base,Repayment.Recovery.scope,parent.cursor.source,rfl,rfl⟩
abbrev count := parent.cursor.cut

theorem the_actual_material_reserve_generates_recovery_and_private_readiness :
    (before old count).stock 0 .feedstock = 2 ∧ (before old count).stock 1 .service = 0 ∧
      recovery old count [] = RenewedQuorumMaterial.word ∧
      (prepared old count []).stock 0 .feedstock = 1 ∧ (prepared old count []).stock 1 .service = 3 ∧
      (prepared old count []).claims () 1 2 = 7 ∧ (inspect old count []).isSome = true := by
  decide +kernel

def firstEntry : Ready old count [] := (inspect old count []).get
  the_actual_material_reserve_generates_recovery_and_private_readiness.2.2.2.2.2.2
abbrev first := actual old count [] firstEntry

theorem actual_recovery_is_consumed_by_a_new_paid_quorum :
    MaterialRoundConsumer.status old count [] = .decided true ∧
      (first.source.feedbackState (CommunicationRuntime.actualInput firstEntry.bound (input old count [] firstEntry) 0
        (protocol old count [] firstEntry) (environment old count [] firstEntry)) 6).current.claims () 1 2 = 6 ∧
      (slot old count [] firstEntry).epoch = 22 := by
  decide +kernel

theorem the_second_actual_round_consumes_the_literal_remaining_fuel :
    (before first 6).stock 0 .feedstock = 1 ∧ (before first 6).stock 1 .service = 0 ∧
      recovery first 6 [] = RenewedQuorumMaterial.word ∧ (prepared first 6 []).stock 0 .feedstock = 0 ∧
      (prepared first 6 []).stock 1 .service = 3 ∧ (prepared first 6 []).claims () 1 2 = 6 ∧
      (inspect first 6 []).isSome = true := by
  decide +kernel

def secondEntry : Ready first 6 [] := (inspect first 6 []).get
  the_second_actual_round_consumes_the_literal_remaining_fuel.2.2.2.2.2.2
abbrev second := actual first 6 [] secondEntry

theorem the_second_generated_quorum_does_not_replay_the_first_subject :
    MaterialRoundConsumer.status first 6 [] = .decided true ∧
      (before second 6).claims () 1 2 = 5 ∧ (slot first 6 [] secondEntry).epoch = 31 ∧
      slot old count [] firstEntry ≠ slot first 6 [] secondEntry := by
  decide +kernel

theorem exhausted_material_does_not_create_a_third_paid_window :
    (before second 6).stock 0 .feedstock = 0 ∧ (before second 6).stock 1 .service = 0 ∧
      recovery second 6 [] = [] ∧ preparation second 6 [] = .phaseRefused ∧
      MaterialRoundConsumer.status second 6 [] = .phaseRefused ∧ (prepared second 6 []).claims () 1 2 = 5 := by
  decide +kernel

abbrev forbiddenInput : List Action := [⟨1,[],.reserve 1,[],.transfer 1 0 [(.feedstock,1)]⟩]
theorem an_invalid_raw_input_is_not_laundered_by_a_later_actual_recovery :
    (afterInput old count forbiddenInput).stock 0 .feedstock = 2 ∧
      recovery old count forbiddenInput = RenewedQuorumMaterial.word ∧
      (prepared old count forbiddenInput).stock 0 .feedstock = 1 ∧
      (prepared old count forbiddenInput).stock 1 .service = 3 ∧
      preparation old count forbiddenInput = .historyRefused ∧
      MaterialRoundConsumer.status old count forbiddenInput = .historyRefused := by
  decide +kernel

abbrev held := OpenControlConsumer.finished OpenControlControls.always OpenControlControls.latest
abbrev heldBound : Bound := ⟨RenewedQuorumMaterial.base,Repayment.Recovery.scope,held.cursor.source,rfl,rfl⟩
theorem a_genuinely_withheld_round_reenters_without_resetting_stock_or_claims :
    OpenControlSource.result held = .blocked .missingSourceSubject ∧
      (before heldBound 6).claims () 1 2 = 10 ∧ (before heldBound 6).stock 1 .service = 3 ∧
      recovery heldBound 6 [] = [] ∧ (inspect heldBound 6 []).isSome = true ∧
      MaterialRoundConsumer.status heldBound 6 [] = .decided true := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MaterialRoundControls
