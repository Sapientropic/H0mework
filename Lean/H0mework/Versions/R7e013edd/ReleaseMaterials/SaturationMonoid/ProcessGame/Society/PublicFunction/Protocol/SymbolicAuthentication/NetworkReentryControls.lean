import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryControls
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource NetworkReentrySource NetworkReentryConsumer

abbrev seed : State := ⟨DonorRegenerationControls.seed,[]⟩
abbrev delayed : Callbacks := ActualRoundNetworkControls.delayed
abbrev deviation : Callbacks := ActualRoundNetworkControls.deviation
abbrev silent : Callbacks := ActualRoundNetworkControls.silent
abbrev first := next seed true true {} delayed
abbrev second := next first true true {} deviation
abbrev third := next second true true {} latest

def firstNet : Network := (NetworkReentrySource.inspect seed true true {}).get (by decide +kernel)
def secondNet : Network := (NetworkReentrySource.inspect first true true {}).get (by decide +kernel)
abbrev firstAttempt := execute firstNet (delayed firstNet)
abbrev secondAttempt := execute secondNet (deviation secondNet)
def firstSubject := (ActualRoundNetworkConsumer.completion firstNet).get (by decide +kernel)
def secondSubject := (ActualRoundNetworkConsumer.completion secondNet).get (by decide +kernel)

def outcomes (state : State) : List (Option Bool) := state.evidence.map fun attempt =>
  match decision attempt with
  | .blocked _ => none
  | .decided agreed _ => some agreed

theorem both_new_rounds_use_the_literal_previous_actual_endpoint :
    first = ⟨after firstAttempt,[firstAttempt]⟩ ∧
      second = ⟨after secondAttempt,first.evidence ++ [secondAttempt]⟩ := by
  exact ⟨admitted_next_uses_the_actual_network_endpoint seed true true {} delayed firstNet (Option.some_get _).symm,
    admitted_next_uses_the_actual_network_endpoint first true true {} deviation secondNet (Option.some_get _).symm⟩

theorem adaptive_actual_rounds_pay_twice_and_regenerate_without_resetting_the_claim :
    outcomes first = [some true] ∧ outcomes second = [some true,some true] ∧
      (current seed).claims () 1 2 = 7 ∧ (current first).claims () 1 2 = 6 ∧ (current second).claims () 1 2 = 5 ∧
      (current first).stock 0 .energy = 1 ∧ (current first).stock 0 .labor = 2 ∧
      (current first).stock 1 .waste = 3 ∧ (current second).stock 1 .waste = 1 ∧
      firstSubject.1.scope ≠ secondSubject.1.scope ∧
      (material secondNet (actual secondNet (deviation secondNet) 1) (deviation secondNet 1)).call =
        .external (some ⟨.activate 0,by decide⟩) ∧
      StageTransport.admission (material secondNet (actual secondNet (deviation secondNet) 1) (deviation secondNet 1)) = none := by
  and_intros <;> decide +kernel

theorem all_compliant_first_endpoints_have_original_paid_reproduction_inputs :
    replenishable firstNet = true := by decide +kernel

theorem arbitrary_compliant_first_callbacks_generate_the_next_actual_paid_feed
    (callbacks : Nat → Opponent (code firstNet)) (within : Within firstNet callbacks (window firstNet)) :
    let state := after (execute firstNet callbacks)
    DonorRegenerationSource.incoming state true = DonorRegenerationLaw.word ∧
      RoundEpisodeSource.current (DonorRegenerationSource.generated state true) =
        DonorRegenerationLaw.successor (RoundEpisodeSource.current state) ∧
      UpstreamFeedSource.select (DonorRegenerationSource.generated state true) true = .offered :=
  every_compliant_endpoint_generates_actual_paid_donor_fuel_and_feed firstNet
    all_compliant_first_endpoints_have_original_paid_reproduction_inputs (by
      rw [admitted_network_preserves_the_original_material_law,
        admitted_network_uses_the_actual_prepared_state seed true true {} firstNet (Option.some_get _).symm]
      rfl) callbacks within

theorem both_actual_rounds_have_generated_completion_and_compliant_callbacks :
    ActualRoundNetworkConsumer.completion firstNet = some firstSubject ∧
      ActualRoundNetworkConsumer.completion secondNet = some secondSubject ∧
      Within firstNet (delayed firstNet) (window firstNet) ∧
      Within secondNet (deviation secondNet) (window secondNet) := by
  refine ⟨(Option.some_get _).symm,(Option.some_get _).symm,?_,?_⟩
  all_goals exact (ActualRoundNetworkControls.conforms_iff _ _).mp (by decide +kernel)

abbrev firstResponsibility := ActualRoundNetworkConsumer.generated_completion_consumes_actual_payment_whole_ledger_and_next
  firstNet firstSubject both_actual_rounds_have_generated_completion_and_compliant_callbacks.1
  (delayed firstNet) both_actual_rounds_have_generated_completion_and_compliant_callbacks.2.2.1
abbrev secondResponsibility := ActualRoundNetworkConsumer.generated_completion_consumes_actual_payment_whole_ledger_and_next
  secondNet secondSubject both_actual_rounds_have_generated_completion_and_compliant_callbacks.2.1
  (deviation secondNet) both_actual_rounds_have_generated_completion_and_compliant_callbacks.2.2.2
abbrev firstNative := completed_occurrence_consumes_its_native_ledger_and_next firstAttempt
abbrev secondNative := completed_occurrence_consumes_its_native_ledger_and_next secondAttempt

abbrev blocked := next seed true true {} silent
abbrev recovered := next blocked true true {} delayed

theorem blocked_readout_keeps_the_actual_payment_and_can_reenter_a_real_next_round :
    outcomes blocked = [none] ∧ (current blocked).claims () 1 2 = 6 ∧
      outcomes recovered = [none,some true] ∧ (current recovered).claims () 1 2 = 5 := by
  and_intros <;> decide +kernel

theorem exhausted_source_and_withheld_supply_do_not_manufacture_a_decision :
    DonorRegenerationSource.select second.episode true = .unavailable ∧
      NetworkReentrySource.inspect second true true {} = none ∧
      outcomes third = [some true,some true] ∧ (current third).claims () 1 2 = 5 ∧
      DonorRegenerationSource.select seed.episode false = .withheld ∧
      (RoundEpisodeSource.current (DonorRegenerationSource.generated seed.episode false)).stock 2 .feedstock = 0 ∧
      NetworkReentrySource.inspect seed true false {} = none := by
  and_intros <;> decide +kernel

abbrev archivesSurvive := every_later_callback_keeps_all_original_archives seed
abbrev attemptsSurvive := every_later_callback_keeps_all_actual_attempts seed
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentryControls
