import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 240000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionControls
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open RecycledQuorumMaterial (Current Action)
open RoundEpisodeSource

def initial (fuel : Nat) : Current := {WorkerInputControls.initial 0 1 3 0 with
  stock := fun party good => if party = 0 ∧ good = .feedstock then fuel else (WorkerInputControls.initial 0 1 3 0).stock party good}
abbrev code (fuel : Nat) := {WorkerInputControls.code true 0 1 3 0 with initial := initial fuel}
abbrev source (fuel : Nat) : Machine Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
    (Mandate.State Delegation.Funded.Party Bool) Unit where
  code := code fuel
  reference := fun _ _ => []
  reference_generated := by
    apply (code fuel).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := (code fuel).publicPrefix
  original := (code fuel).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev model (fuel : Nat) : MaterialRoundSource.Bound := ⟨FuelMandateLaw.base true,Repayment.Recovery.scope,source fuel,rfl,rfl⟩
abbrev funded : State := ⟨model 1,0,[]⟩
abbrev empty : State := ⟨model 0,0,[]⟩
abbrev first := UpstreamProductionSource.next funded
abbrev second := UpstreamProductionSource.next first

theorem no_initial_energy_is_hidden_in_the_new_source :
    (current funded).stock 0 .energy = 0 ∧ (current funded).stock 0 .labor = 1 ∧
      (current funded).stock 0 .feedstock = 1 ∧ WorkerInputSource.Needed (current funded) ∧
      ¬ WorkerInputLaw.Inputs (current funded) ∧ UpstreamProductionLaw.Inputs (current funded) := by decide +kernel

theorem the_actual_production_calls_the_uniform_material_consumer :
    WorkerInputSource.incoming (rawSource funded (UpstreamProductionSource.incoming funded)) (funded.cut+1) = WorkerInputLaw.word ∧
      let finish := MaterialRoundSource.prepared (supplied funded (UpstreamProductionSource.incoming funded)) (count funded)
        (arrival funded (UpstreamProductionSource.incoming funded))
      finish.stock 0 .feedstock = 0 ∧
      finish.stock 0 .energy = (current funded).stock 0 .energy+1 ∧
      finish.stock 0 .labor = (current funded).stock 0 .labor+1 ∧
      finish.stock 1 .waste = (current funded).stock 1 .waste-1 ∧
      finish.stock 1 .service = (current funded).stock 1 .service+3 ∧
      finish.stock 2 .energy = (current funded).stock 2 .energy ∧
      finish.stock 2 .labor = (current funded).stock 2 .labor ∧
      finish.claims = (current funded).claims ∧ finish.technology = (current funded).technology :=
  UpstreamProductionConsumer.actual_production_is_consumed_by_original_worker_fuel_and_service_steps funded rfl
    no_initial_energy_is_hidden_in_the_new_source.2.2.2.1
    no_initial_energy_is_hidden_in_the_new_source.2.2.2.2.1
    no_initial_energy_is_hidden_in_the_new_source.2.2.2.2.2

theorem actual_upstream_production_enables_two_fresh_paid_rounds :
    status funded (UpstreamProductionSource.command funded) = .decided true ∧
      (current first).stock 0 .energy = 1 ∧ (current first).stock 0 .labor = 2 ∧
      (current first).claims () 1 2 = 6 ∧ status first (UpstreamProductionSource.command first) = .decided true ∧
      UpstreamProductionSource.incoming first = [] ∧ (current second).claims () 1 2 = 5 ∧
      (current second).stock 0 .energy = 0 ∧ (current second).stock 0 .labor = 1 ∧
      RoundEpisodeControls.archivedDecisions second.archive = [.decided true,.decided true] := by decide +kernel

abbrev ordinaryFirst := RoundEpisodeSource.next funded (normal funded)
theorem deleting_early_production_loses_the_second_real_round :
    status funded (normal funded) = .decided true ∧
      status ordinaryFirst (normal ordinaryFirst) = .phaseRefused ∧
      (current ordinaryFirst).claims () 1 2 = 6 ∧
      status empty (UpstreamProductionSource.command empty) = .phaseRefused ∧
      status second (UpstreamProductionSource.command second) = .phaseRefused := by decide +kernel

abbrev forged : List Action := [{UpstreamProductionLaw.request with signer := 2}]
abbrev corrupt := RoundEpisodeSource.next funded (normal funded forged)
theorem wrong_signer_and_replay_leave_their_real_refusal_history :
    status funded (normal funded forged) = .historyRefused ∧
      status corrupt (UpstreamProductionSource.command corrupt) = .historyRefused ∧
      status funded (normal funded (UpstreamProductionLaw.word ++ UpstreamProductionLaw.word)) = .historyRefused := by decide +kernel

def silent (state : State) : Command state :=
  ⟨UpstreamProductionSource.incoming state,(UpstreamProductionSource.command state).localRule,fun _ => fun _ _ _ => none⟩
abbrev delayed := RoundEpisodeSource.next funded (silent funded)
theorem real_production_does_not_replace_delivery_or_erase_the_blocked_round :
    status funded (silent funded) = .blocked .missingQuorum ∧
      (current delayed).claims () 1 2 = 6 ∧
      status delayed (UpstreamProductionSource.command delayed) = .decided true ∧
      RoundEpisodeControls.archivedDecisions (UpstreamProductionSource.next delayed).archive = [.blocked .missingQuorum,.decided true] := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionControls
