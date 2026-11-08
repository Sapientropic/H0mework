import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RecycledQuorumMaterial (Current Action)
open RoundEpisodeSource

-- Read the actual endpoint; do not ask for a Ready witness or an energy allocation.
def incoming (state : State) : List Action :=
  if WorkerInputSource.Needed (current state) ∧ ¬ WorkerInputLaw.Inputs (current state) ∧
      UpstreamProductionLaw.Inputs (current state) then UpstreamProductionLaw.word else []
abbrev command (state : State) : Command state := normal state (incoming state)
abbrev after (state : State) := WorkerInputSource.before (rawSource state (incoming state)) (state.cut+1)
abbrev next (state : State) := RoundEpisodeSource.next state (command state)
abbrev controller : Controller := fun state => command state

variable (state : State)
theorem primitive_fuel_and_labor_generate_the_actual_upstream_production
    (same : state.model.source.code.law = UpstreamProductionLaw.law)
    (needed : WorkerInputSource.Needed (current state))
    (missing : ¬ WorkerInputLaw.Inputs (current state))
    (inputs : UpstreamProductionLaw.Inputs (current state)) :
    incoming state = UpstreamProductionLaw.word ∧
      ((rawSource state (incoming state)).source.actualExecution (MaterialRoundSource.depth state.model state.cut)).submitted = UpstreamProductionLaw.word ∧
      after state = UpstreamProductionLaw.successor (current state) ∧
      WorkerInputLaw.Inputs (after state) ∧
      ∀ item ∈ state.model.source.code.law.rawItems (current state) (incoming state),
        state.model.source.code.law.Valid item.before item.request := by
  have selected : incoming state = UpstreamProductionLaw.word := by simp [incoming,needed,missing,inputs]
  have actual := Machine.Continuation.actual_next state.model.source state.cut (incoming state)
  have endpoint : after state = state.model.source.code.law.next (current state) (incoming state) := by
    change (Machine.Continuation.extend state.model.source state.cut (incoming state)).currentAt
      (MaterialRoundSource.depth state.model state.cut+2) = _
    exact actual
  rw [same,selected,(UpstreamProductionLaw.actual_next _ inputs).1] at endpoint
  exact ⟨selected,by rw [Machine.Continuation.submitted,selected],endpoint,
    endpoint ▸ UpstreamProductionLaw.original_production_generates_the_previously_assumed_worker_inputs _ inputs,
    by rw [same,selected];exact (UpstreamProductionLaw.actual_next _ inputs).2⟩

theorem no_worker_deficit_does_not_pay_for_unneeded_production
    (stocked : ¬ WorkerInputSource.Needed (current state)) : incoming state = [] := by simp [incoming,stocked]

theorem insufficient_actual_production_inputs_do_not_emit_a_fake_supply
    (absent : ¬ UpstreamProductionLaw.Inputs (current state)) : incoming state = [] := by simp [incoming,absent]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionSource
