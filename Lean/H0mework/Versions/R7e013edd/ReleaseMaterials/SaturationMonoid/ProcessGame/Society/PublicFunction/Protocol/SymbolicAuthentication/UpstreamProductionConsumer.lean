import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RecycledQuorumMaterial (Current Action material)
open RoundEpisodeSource
open UpstreamProductionSource (incoming command after)

variable (state : State)
theorem actual_production_is_consumed_by_original_worker_fuel_and_service_steps
    (same : state.model.source.code.law = UpstreamProductionLaw.law)
    (needed : WorkerInputSource.Needed (current state))
    (missing : ¬ WorkerInputLaw.Inputs (current state))
    (inputs : UpstreamProductionLaw.Inputs (current state)) :
    WorkerInputSource.incoming (rawSource state (incoming state)) (state.cut+1) = WorkerInputLaw.word ∧
      let finish := MaterialRoundSource.prepared (supplied state (incoming state)) (count state) (arrival state (incoming state))
      finish.stock 0 .feedstock = 0 ∧
      finish.stock 0 .energy = (current state).stock 0 .energy+1 ∧
      finish.stock 0 .labor = (current state).stock 0 .labor+1 ∧
      finish.stock 1 .waste = (current state).stock 1 .waste-1 ∧
      finish.stock 1 .service = (current state).stock 1 .service+3 ∧
      finish.stock 2 .energy = (current state).stock 2 .energy ∧
      finish.stock 2 .labor = (current state).stock 2 .labor ∧
      finish.claims = (current state).claims ∧ finish.technology = (current state).technology := by
  have generated := UpstreamProductionSource.primitive_fuel_and_labor_generate_the_actual_upstream_production state same needed missing inputs
  have stillNeeded : WorkerInputSource.Needed (after state) := by
    rw [generated.2.2.1]
    simpa only [WorkerInputSource.Needed,UpstreamProductionLaw.successor,
      show (2 : Delegation.Funded.Party) ≠ 0 by decide, false_and,ite_false,sub_zero,add_zero] using needed
  have worker := WorkerInputSource.a_funded_actual_deficit_generates_the_worker_inputs
    (rawSource state (incoming state)) (state.cut+1) same stillNeeded generated.2.2.2.1
  have consumed := WorkerInputConsumer.actual_upstream_inputs_are_consumed_once_by_the_original_fuel_and_service_producer
    (rawSource state (incoming state)) (state.cut+1) same stillNeeded generated.2.2.2.1
  change _ ∧ _
  refine ⟨worker.1,?_⟩
  dsimp only at consumed ⊢
  have before_eq : WorkerInputSource.before (rawSource state (incoming state)) (state.cut+1) =
      UpstreamProductionLaw.successor (current state) := generated.2.2.1
  rw [before_eq] at consumed
  have fuel := FuelMaterialSource.the_full_preparation_conserves_supplier_fuel_and_pays_the_upstream_worker
    (WorkerInputSource.arrived (rawSource state (incoming state)) (state.cut+1)) ((state.cut+1)+1)
    same worker.2.2.1
  have fuel0 : (MaterialRoundSource.prepared (supplied state (incoming state)) (count state) (arrival state (incoming state))).stock 0 .feedstock = 0 := by
    rw [fuel.1]
    change (WorkerInputSource.afterInput (rawSource state (incoming state)) (state.cut+1)).stock 0 .feedstock = 0
    rw [worker.2.1,before_eq]
    simp [WorkerInputLaw.successor,UpstreamProductionLaw.successor,inputs.fuel]
  obtain ⟨energy,labor,waste,service,_,workerEnergy,workerLabor,claims,technology⟩ := consumed
  refine ⟨fuel0,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · convert energy using 1
    simp [UpstreamProductionLaw.successor]
    ring
  · convert labor using 1
    simp [UpstreamProductionLaw.successor]
    ring
  · simpa [UpstreamProductionLaw.successor] using waste
  · simpa [UpstreamProductionLaw.successor] using service
  · simpa [UpstreamProductionLaw.successor] using workerEnergy
  · simpa [UpstreamProductionLaw.successor] using workerLabor
  · exact claims
  · exact technology

theorem production_and_all_preparation_attempts_use_their_original_native_ledger_and_next :
    RoundEpisodeConsumer.NativeConsumed (rawSource state (incoming state)) (MaterialRoundSource.depth state.model state.cut)
      (produce state (command state)).rawDisposition ∧
    RoundEpisodeConsumer.NativeConsumed (supplied state (incoming state)) (MaterialRoundSource.depth (rawSource state (incoming state)) (state.cut+1))
      (produce state (command state)).upstreamDisposition ∧
    RoundEpisodeConsumer.NativeConsumed (MaterialRoundSource.supplied (supplied state (incoming state)) (count state) (arrival state (incoming state)))
      (MaterialRoundSource.depth (supplied state (incoming state)) (count state)) (produce state (command state)).fuelDisposition ∧
    RoundEpisodeConsumer.NativeConsumed (residual state (incoming state)) (MaterialRoundSource.depth (supplied state (incoming state)) (count state)+1)
      (produce state (command state)).recoveryDisposition :=
  RoundEpisodeConsumer.all_four_real_preparation_occurrences_consume_their_own_ledger_and_next state (command state)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionConsumer
