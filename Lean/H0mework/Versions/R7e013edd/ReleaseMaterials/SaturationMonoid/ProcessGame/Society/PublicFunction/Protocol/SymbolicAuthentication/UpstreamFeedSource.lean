import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedLaw
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RecycledQuorumMaterial (Current Action)
open RoundEpisodeSource

inductive Selection where
  | idle | withheld | primitiveMissing | permissionDenied | offered
  deriving DecidableEq

def Demand (state : State) : Prop := WorkerInputSource.Needed (current state) ∧
  ¬ WorkerInputLaw.Inputs (current state) ∧ ¬ UpstreamProductionLaw.Inputs (current state)
instance (state : State) : Decidable (Demand state) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- `submit` is an external interface instruction; existing law admission and actual debit
-- supply its material meaning. It is not a signature or an inferred motive.
def select (state : State) (submit : Bool) : Selection :=
  if Demand state then
    if submit then
      if UpstreamFeedLaw.Resources (current state) then
        if state.model.source.code.law.Valid (current state) UpstreamFeedLaw.request then .offered
        else .permissionDenied
      else .primitiveMissing
    else .withheld
  else .idle

def incoming (state : State) (submit : Bool) : List Action :=
  if select state submit = .offered then [UpstreamFeedLaw.request] else []
abbrev arrivalModel (state : State) (submit : Bool) := rawSource state (incoming state submit)
abbrev disposition (state : State) (submit : Bool) :=
  Native.Authority.fullGenerate (arrivalModel state submit) (MaterialRoundSource.depth state.model state.cut)

def arrived (state : State) (submit : Bool) : State :=
  ⟨arrivalModel state submit,state.cut+1,state.archive ++
    [.native (arrivalModel state submit) (MaterialRoundSource.depth state.model state.cut) (disposition state submit)]⟩
abbrev next (state : State) (submit : Bool) (control : Controller) :=
  RoundEpisodeSource.next (arrived state submit) (control (arrived state submit))
abbrev automatic (state : State) (submit : Bool) := next state submit UpstreamProductionSource.controller

def run (initial : State) (submit : State → Bool) (control : Controller) : Nat → State :=
  Nat.rec initial fun _ state => next state (submit state) control

theorem offered_uses_actual_material_and_permission (state : State) (submit : Bool)
    (selected : select state submit = .offered) :
    Demand state ∧ submit = true ∧ UpstreamFeedLaw.Resources (current state) ∧
      state.model.source.code.law.Valid (current state) UpstreamFeedLaw.request := by
  unfold select at selected
  split at selected <;> try contradiction
  rename_i demand
  split at selected <;> try contradiction
  rename_i submitted
  split at selected <;> try contradiction
  rename_i resources
  split at selected <;> try contradiction
  exact ⟨demand,submitted,resources,by assumption⟩

theorem primitive_resources_generate_the_offer (state : State)
    (same : state.model.source.code.law = UpstreamProductionLaw.law)
    (demand : Demand state) (resources : UpstreamFeedLaw.Resources (current state)) :
    select state true = .offered := by
  have paid : state.model.source.code.law.Valid (current state) UpstreamFeedLaw.request :=
    same ▸ UpstreamFeedLaw.valid _ resources
  simp [select,demand,resources,paid]

theorem actual_arrival (state : State) (submit : Bool) :
    ((arrivalModel state submit).source.actualExecution (MaterialRoundSource.depth state.model state.cut)).submitted = incoming state submit ∧
      ((arrivalModel state submit).source.actualExecution (MaterialRoundSource.depth state.model state.cut)).before = current state ∧
      current (arrived state submit) = state.model.source.code.law.next (current state) (incoming state submit) := by
  refine ⟨Machine.Continuation.submitted _ _ _,Machine.Continuation.before _ _ _,?_⟩
  change (Machine.Continuation.extend state.model.source state.cut (incoming state submit)).currentAt
    (MaterialRoundSource.depth state.model state.cut+2) = _
  exact Machine.Continuation.actual_next _ _ _

theorem generated_primitive_inputs (state : State) (submit : Bool)
    (same : state.model.source.code.law = UpstreamProductionLaw.law)
    (selected : select state submit = .offered) :
    incoming state submit = [UpstreamFeedLaw.request] ∧
      current (arrived state submit) = UpstreamFeedLaw.successor (current state) ∧
      UpstreamProductionLaw.Inputs (current (arrived state submit)) ∧
      WorkerInputSource.Needed (current (arrived state submit)) ∧
      ¬ WorkerInputLaw.Inputs (current (arrived state submit)) := by
  obtain ⟨demand,_,resources,paid⟩ := offered_uses_actual_material_and_permission state submit selected
  have word : incoming state submit = [UpstreamFeedLaw.request] := by simp [incoming,selected]
  have after := (actual_arrival state submit).2.2
  rw [word,UpstreamFeedLaw.actual_next _ _ paid (by rw [same];rfl)] at after
  exact ⟨word,after,after ▸ UpstreamFeedLaw.new_inputs _ resources,
    after ▸ UpstreamFeedLaw.needed_is_preserved _ demand.1,
    after ▸ UpstreamFeedLaw.worker_inputs_are_still_missing_before_production _ resources⟩

theorem generated_supply_is_consumed_by_original_upstream_production (state : State) (submit : Bool)
    (same : state.model.source.code.law = UpstreamProductionLaw.law)
    (selected : select state submit = .offered) :
    UpstreamProductionSource.incoming (arrived state submit) = UpstreamProductionLaw.word ∧
      ((rawSource (arrived state submit) (UpstreamProductionSource.incoming (arrived state submit))).source.actualExecution
        (MaterialRoundSource.depth (arrived state submit).model (arrived state submit).cut)).submitted = UpstreamProductionLaw.word ∧
      WorkerInputLaw.Inputs (UpstreamProductionSource.after (arrived state submit)) := by
  have inputs := generated_primitive_inputs state submit same selected
  have generated := UpstreamProductionSource.primitive_fuel_and_labor_generate_the_actual_upstream_production
    (arrived state submit) same inputs.2.2.2.1 inputs.2.2.2.2 inputs.2.2.1
  exact ⟨generated.1,generated.2.1,generated.2.2.2.1⟩

theorem refusal_is_not_a_material_arrival (state : State) (submit : Bool)
    (refused : select state submit ≠ .offered) :
    incoming state submit = [] ∧
      (current (arrived state submit)).stock = (current state).stock ∧
      (current (arrived state submit)).claims = (current state).claims := by
  have word : incoming state submit = [] := by simp [incoming,refused]
  rw [(actual_arrival state submit).2.2,word]
  exact ⟨rfl,rfl,rfl⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamFeedSource
