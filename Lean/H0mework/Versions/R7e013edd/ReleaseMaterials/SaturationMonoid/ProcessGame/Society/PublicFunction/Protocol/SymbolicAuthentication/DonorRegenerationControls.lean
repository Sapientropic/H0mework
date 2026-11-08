import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Current Action)
open RoundEpisodeSource
abbrev state (energy labor waste : Nat) : State := ⟨WorkerInputControls.bound true energy labor waste 0,0,[]⟩
abbrev seed := state 1 2 5
abbrev produced := DonorRegenerationSource.generated seed true
abbrev ready (current : State) := UpstreamFeedSource.arrived (DonorRegenerationSource.generated current true) true
abbrev first := DonorRegenerationSource.automatic seed
abbrev second := DonorRegenerationSource.automatic first

theorem no_donor_fuel_is_preinstalled :
    (current seed).stock 0 .feedstock = 0 ∧ (current seed).stock 2 .feedstock = 0 ∧
      (current seed).stock 0 .energy = 1 ∧ (current seed).stock 0 .labor = 2 ∧
      DonorRegenerationLaw.Inputs (current seed) ∧ WorkerInputSource.Needed (current seed) ∧
      DonorRegenerationSource.select seed true = .produced := by decide +kernel

theorem actual_worker_inputs_are_consumed_to_generate_new_donor_fuel :
    DonorRegenerationSource.incoming seed true = DonorRegenerationLaw.word ∧
      (current produced).stock 2 .feedstock = 1 ∧ (current produced).stock 0 .feedstock = 0 ∧
      (current produced).stock 0 .energy = 0 ∧ (current produced).stock 0 .labor = 1 ∧
      (current produced).stock 1 .waste = 4 ∧ (current produced).stock 2 .waste = 0 ∧
      (current produced).stock 2 .energy = 0 ∧ (current produced).stock 2 .labor = 0 ∧
      (current produced).claims () 1 2 = 7 ∧ UpstreamFeedSource.select produced true = .offered := by decide +kernel

theorem successive_actual_rounds_regenerate_fuel_and_preserve_their_production_capacity :
    status (ready seed) (UpstreamProductionSource.command (ready seed)) = .decided true ∧
      (current first).stock 0 .energy = 1 ∧ (current first).stock 0 .labor = 2 ∧
      (current first).stock 1 .waste = 3 ∧ (current first).stock 2 .feedstock = 0 ∧
      (current first).claims () 1 2 = 6 ∧ DonorRegenerationLaw.Inputs (current first) ∧
      status (ready first) (UpstreamProductionSource.command (ready first)) = .decided true ∧
      (current second).stock 0 .energy = 1 ∧ (current second).stock 0 .labor = 2 ∧
      (current second).stock 1 .waste = 1 ∧ (current second).stock 2 .feedstock = 0 ∧
      (current second).claims () 1 2 = 5 ∧
      RoundEpisodeControls.archivedDecisions second.archive = [.decided true,.decided true] := by decide +kernel

abbrev ordinary := UpstreamProductionSource.next seed
theorem omitting_regeneration_consumes_capacity_and_loses_the_next_real_round :
    status seed (UpstreamProductionSource.command seed) = .decided true ∧
      (current ordinary).stock 0 .energy = 0 ∧
      status ordinary (UpstreamProductionSource.command ordinary) = .phaseRefused ∧
      DonorRegenerationSource.select second true = .unavailable ∧
      status (ready second) (UpstreamProductionSource.command (ready second)) = .phaseRefused ∧
      (current (DonorRegenerationSource.automatic second)).claims () 1 2 = 5 := by decide +kernel

theorem missing_raw_inputs_and_a_withheld_interface_submission_are_distinct :
    DonorRegenerationSource.select (state 0 2 5) true = .unavailable ∧
      DonorRegenerationSource.select (state 1 1 5) true = .unavailable ∧
      DonorRegenerationSource.select (state 1 2 2) true = .unavailable ∧
      DonorRegenerationSource.select seed false = .withheld ∧
      (current (DonorRegenerationSource.generated seed false)).stock 2 .feedstock = 0 ∧
      DonorRegenerationSource.select (DonorRegenerationSource.generated seed false) true = .produced ∧
      status (ready (DonorRegenerationSource.generated seed false))
        (UpstreamProductionSource.command (ready (DonorRegenerationSource.generated seed false))) = .decided true := by
  and_intros <;> decide +kernel

abbrev denied : State := ⟨WorkerInputControls.bound false 1 2 5 0,0,[]⟩
abbrev deniedProduction := DonorRegenerationSource.generated denied true
theorem actual_production_does_not_create_a_missing_transfer_permission :
    DonorRegenerationSource.select denied true = .produced ∧
      (current deniedProduction).stock 2 .feedstock = 1 ∧
      UpstreamFeedSource.select deniedProduction true = .permissionDenied ∧
      UpstreamFeedSource.incoming deniedProduction true = [] := by
  and_intros <;> decide +kernel

abbrev forged : List Action := [{WorkerInputLaw.energyLabor with signer := 2},WorkerInputLaw.waste,DonorRegenerationLaw.recycle]
abbrev tampered := rawSource seed forged
abbrev withoutRecipe := rawSource seed WorkerInputLaw.word
theorem wrong_signer_replay_and_deleted_recipe_cannot_mint_donor_fuel_or_completion :
    status seed (normal seed forged) = .historyRefused ∧
      (MaterialRoundSource.before tampered 1).stock 2 .feedstock = 0 ∧
      status seed (normal seed (DonorRegenerationLaw.word ++ DonorRegenerationLaw.word)) = .historyRefused ∧
      (MaterialRoundSource.before withoutRecipe 1).stock 2 .feedstock = 0 := by decide +kernel

def silent (current : State) : Command current :=
  ⟨UpstreamProductionSource.incoming current,(UpstreamProductionSource.command current).localRule,fun _ => fun _ _ _ => none⟩
abbrev stranded := DonorRegenerationSource.next seed true true silent
theorem regenerated_material_does_not_replace_delivery_and_blocked_history_is_preserved :
    status (ready seed) (silent (ready seed)) = .blocked .missingQuorum ∧
      (current stranded).claims () 1 2 = 6 ∧ (current stranded).stock 0 .energy = 1 ∧
      status (ready stranded) (UpstreamProductionSource.command (ready stranded)) = .decided true ∧
      RoundEpisodeControls.archivedDecisions (DonorRegenerationSource.automatic stranded).archive =
        [.blocked .missingQuorum,.decided true] := by decide +kernel

def entry := (RoundEpisodeSource.inspect (ready seed) (UpstreamProductionSource.command (ready seed)).raw).get (by decide +kernel)
abbrev emitter := RoundEpisodeSource.emitter (ready seed) (UpstreamProductionSource.command (ready seed)).raw entry
abbrev input := RoundEpisodeSource.input (ready seed) (UpstreamProductionSource.command (ready seed)).raw entry
abbrev protocol := (UpstreamProductionSource.command (ready seed)).localRule entry
abbrev environment := (UpstreamProductionSource.command (ready seed)).network entry
abbrev vocabulary := RoundEpisodeSource.vocabulary (ready seed) (UpstreamProductionSource.command (ready seed)).raw entry
abbrev encoding := RoundEpisodeSource.encoding (ready seed) (UpstreamProductionSource.command (ready seed)).raw entry
abbrev reception := RoundEpisodeSource.reception (ready seed) (UpstreamProductionSource.command (ready seed)).raw entry
abbrev slot := RoundEpisodeSource.slot (ready seed) (UpstreamProductionSource.command (ready seed)).raw entry
abbrev subject := (ApplicationSubject.resolve emitter input 0 protocol environment vocabulary slot).get (by decide +kernel)
theorem actual_new_subject_is_generated_from_its_own_payment :
    RoundEpisodeSource.outcome (ready seed) (UpstreamProductionSource.command (ready seed)) entry = .decided true subject := by decide +kernel
abbrev paymentResponsibility := RoundEpisodeConsumer.every_completed_round_consumes_its_actual_payment_whole_ledger_and_next
  (ready seed) (UpstreamProductionSource.command (ready seed)) entry true subject actual_new_subject_is_generated_from_its_own_payment
abbrev productionResponsibility := DonorRegenerationConsumer.actual_production_consumes_its_native_ledger_and_next seed true
abbrev supplyResponsibility := DonorRegenerationConsumer.supplyResponsibility seed true true
abbrev preparationResponsibility := DonorRegenerationConsumer.preparationResponsibility seed true true
abbrev blockedResponsibility := RoundEpisodeConsumer.every_communication_attempt_consumes_native_responsibility_even_when_blocked
  (ready seed) (silent (ready seed)) entry 0

theorem production_does_not_supply_missing_timing_or_quorum :
    SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding ⟨fun _ _ => slot,0⟩ 0 6 6 slot 1 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding reception 0 6 6 slot 2 = .blocked .missingQuorum := by
  and_intros <;> decide +kernel
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationControls
