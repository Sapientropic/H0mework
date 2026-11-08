import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Current Action)
open RoundEpisodeSource UpstreamFeedSource

def initial (fuel : Nat) : Current := {UpstreamProductionControls.initial 0 with
  stock := fun party good => if party = 2 ∧ good = .feedstock then fuel
    else (UpstreamProductionControls.initial 0).stock party good}
abbrev code (released : Bool) (fuel : Nat) := {WorkerInputControls.code released 0 1 3 0 with initial := initial fuel}
abbrev source (released : Bool) (fuel : Nat) : Machine Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
    (Mandate.State Delegation.Funded.Party Bool) Unit where
  code := code released fuel
  reference := fun _ _ => []
  reference_generated := by
    apply (code released fuel).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code released fuel).publicPrefix
  original := (code released fuel).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev model (released : Bool) (fuel : Nat) : MaterialRoundSource.Bound :=
  ⟨FuelMandateLaw.base released,Repayment.Recovery.scope,source released fuel,rfl,rfl⟩
abbrev seed : State := ⟨model true 1,0,[]⟩
abbrev missing : State := ⟨model true 0,0,[]⟩
abbrev denied : State := ⟨model false 1,0,[]⟩
abbrev exhausted := UpstreamProductionSource.next seed
abbrev refilled := arrived exhausted true
abbrev recovered := automatic exhausted true
abbrev declined := automatic exhausted false

theorem an_actual_failed_endpoint_generates_its_own_external_resource_demand :
    status seed (UpstreamProductionSource.command seed) = .phaseRefused ∧
      (current exhausted).stock 0 .feedstock = 0 ∧ (current exhausted).stock 2 .feedstock = 1 ∧
      (current exhausted).claims () 1 2 = 7 ∧ select exhausted true = .offered ∧
      incoming exhausted true = [UpstreamFeedLaw.request] := by decide +kernel

theorem original_transfer_pays_the_donor_before_original_production :
    (current refilled).stock 0 .feedstock = 1 ∧ (current refilled).stock 2 .feedstock = 0 ∧
      (current refilled).stock 0 .energy = 0 ∧ (current refilled).stock 0 .labor = 1 ∧
      (current refilled).claims () 1 2 = 7 ∧
      UpstreamProductionSource.incoming refilled = UpstreamProductionLaw.word := by decide +kernel

theorem the_actual_new_round_consumes_the_supply_into_authenticated_quorum :
    status refilled (UpstreamProductionSource.command refilled) = .decided true ∧
      (current recovered).stock 0 .feedstock = 0 ∧ (current recovered).stock 2 .feedstock = 0 ∧
      (current recovered).stock 0 .energy = 1 ∧ (current recovered).stock 0 .labor = 2 ∧
      (current recovered).claims () 1 2 = 6 ∧
      RoundEpisodeControls.archivedDecisions recovered.archive = [.decided true] ∧
      recovered.archive.length = 12 := by decide +kernel

theorem the_same_actor_can_decline_then_submit_from_its_actual_later_state :
    select exhausted false = .withheld ∧ status (arrived exhausted false)
      (UpstreamProductionSource.command (arrived exhausted false)) = .phaseRefused ∧
      (current declined).stock 2 .feedstock = 1 ∧ select declined true = .offered ∧
      status (arrived declined true) (UpstreamProductionSource.command (arrived declined true)) = .decided true := by decide +kernel

theorem missing_material_and_closed_permission_are_separate_refusals :
    select missing true = .primitiveMissing ∧ incoming missing true = [] ∧
      select denied true = .permissionDenied ∧ incoming denied true = [] ∧
      status (arrived missing true) (UpstreamProductionSource.command (arrived missing true)) = .phaseRefused := by
  and_intros <;> decide +kernel

abbrev forged : List Action := [{UpstreamFeedLaw.request with signer := 0}]
abbrev forgery := rawSource exhausted forged
abbrev replay := rawSource exhausted [UpstreamFeedLaw.request,UpstreamFeedLaw.request]
theorem impersonation_and_replay_leave_actual_refusal_history :
    status exhausted (normal exhausted forged) = .historyRefused ∧
      (MaterialRoundSource.before forgery (exhausted.cut+1)).stock 2 .feedstock = 1 ∧
      status exhausted (normal exhausted [UpstreamFeedLaw.request,UpstreamFeedLaw.request]) = .historyRefused ∧
      (MaterialRoundSource.before replay (exhausted.cut+1)).stock 2 .feedstock = 0 := by decide +kernel

def silent (state : State) : Command state :=
  ⟨UpstreamProductionSource.incoming state,(UpstreamProductionSource.command state).localRule,fun _ => fun _ _ _ => none⟩
abbrev stranded := RoundEpisodeSource.next refilled (silent refilled)
theorem paid_supply_does_not_replace_delivery_or_erase_the_blocked_attempt :
    status refilled (silent refilled) = .blocked .missingQuorum ∧
      (current stranded).claims () 1 2 = 6 ∧
      status stranded (UpstreamProductionSource.command stranded) = .decided true ∧
      RoundEpisodeControls.archivedDecisions (UpstreamProductionSource.next stranded).archive =
        [.blocked .missingQuorum,.decided true] := by decide +kernel
def entry := (RoundEpisodeSource.inspect refilled (UpstreamProductionSource.command refilled).raw).get (by decide +kernel)
abbrev emitter := RoundEpisodeSource.emitter refilled (UpstreamProductionSource.command refilled).raw entry
abbrev input := RoundEpisodeSource.input refilled (UpstreamProductionSource.command refilled).raw entry
abbrev protocol := (UpstreamProductionSource.command refilled).localRule entry
abbrev environment := (UpstreamProductionSource.command refilled).network entry
abbrev vocabulary := RoundEpisodeSource.vocabulary refilled (UpstreamProductionSource.command refilled).raw entry
abbrev encoding := RoundEpisodeSource.encoding refilled (UpstreamProductionSource.command refilled).raw entry
abbrev reception := RoundEpisodeSource.reception refilled (UpstreamProductionSource.command refilled).raw entry
abbrev slot := RoundEpisodeSource.slot refilled (UpstreamProductionSource.command refilled).raw entry
abbrev subject := (ApplicationSubject.resolve emitter input 0 protocol environment vocabulary slot).get (by decide +kernel)

theorem the_new_subject_is_generated_from_its_actual_payment :
    RoundEpisodeSource.outcome refilled (UpstreamProductionSource.command refilled) entry = .decided true subject := by decide +kernel

abbrev paidResponsibility := RoundEpisodeConsumer.every_completed_round_consumes_its_actual_payment_whole_ledger_and_next
  refilled (UpstreamProductionSource.command refilled) entry true subject the_new_subject_is_generated_from_its_actual_payment
abbrev feedResponsibility := UpstreamFeedConsumer.every_feed_occurrence_consumes_its_native_responsibility_ledger_and_next exhausted true
abbrev preparationResponsibility := UpstreamFeedConsumer.productionConsumes exhausted true
abbrev blockedResponsibility := RoundEpisodeConsumer.every_communication_attempt_consumes_native_responsibility_even_when_blocked
  refilled (silent refilled) entry 0

theorem actual_supply_does_not_supply_missing_timing_or_quorum :
    SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding
      ⟨fun _ _ => slot,0⟩ 0 6 6 slot 1 = .blocked .missingQuorum ∧
      SubjectQuorum.produce emitter input 0 protocol environment vocabulary encoding reception 0 6 6 slot 2 = .blocked .missingQuorum := by
  and_intros <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedControls
