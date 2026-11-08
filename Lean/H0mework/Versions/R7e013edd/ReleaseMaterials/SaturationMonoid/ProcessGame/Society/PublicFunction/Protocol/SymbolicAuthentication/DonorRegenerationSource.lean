import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RecycledQuorumMaterial (Current Action)
open RoundEpisodeSource

inductive Selection where
  | idle | withheld | unavailable | rejected | produced
  deriving DecidableEq

def select (state : State) (submit : Bool) : Selection :=
  if WorkerInputSource.Needed (current state) then
    if submit then
      if DonorRegenerationLaw.Inputs (current state) then
        if (state.model.source.code.law.rawItems (current state) DonorRegenerationLaw.word).all
          (fun item => decide (state.model.source.code.law.Valid item.before item.request)) then .produced
        else .rejected
      else .unavailable
    else .withheld
  else .idle

def incoming (state : State) (submit : Bool) : List Action :=
  if select state submit = .produced then DonorRegenerationLaw.word else []
abbrev productionModel (state : State) (submit : Bool) := rawSource state (incoming state submit)
abbrev disposition (state : State) (submit : Bool) := Native.Authority.fullGenerate
  (productionModel state submit) (MaterialRoundSource.depth state.model state.cut)
def generated (state : State) (submit : Bool) : State :=
  ⟨productionModel state submit,state.cut+1,state.archive ++
    [.native (productionModel state submit) (MaterialRoundSource.depth state.model state.cut) (disposition state submit)]⟩
abbrev next (state : State) (produce feed : Bool) (control : Controller) :=
  UpstreamFeedSource.next (generated state produce) feed control
abbrev automatic (state : State) := next state true true UpstreamProductionSource.controller

def run (initial : State) (produce feed : State → Bool) (control : Controller) : Nat → State :=
  Nat.rec initial fun _ state => next state (produce state) (feed state) control

theorem original_primitive_inputs_generate_actual_production (state : State)
    (same : state.model.source.code.law = DonorRegenerationLaw.law)
    (needed : WorkerInputSource.Needed (current state))
    (inputs : DonorRegenerationLaw.Inputs (current state)) : select state true = .produced := by
  have admitted : (state.model.source.code.law.rawItems (current state) DonorRegenerationLaw.word).all
      (fun item => decide (state.model.source.code.law.Valid item.before item.request)) = true := by
    rw [same]
    exact List.all_eq_true.mpr (by
      intro item member
      exact decide_eq_true_eq.mpr ((DonorRegenerationLaw.actual_next _ inputs).2 item member))
  simp [select,needed,inputs]
  intro item member
  exact decide_eq_true_eq.mp (List.all_eq_true.mp admitted item member)

theorem actual_production (state : State) (submit : Bool) :
    ((productionModel state submit).source.actualExecution (MaterialRoundSource.depth state.model state.cut)).submitted = incoming state submit ∧
      ((productionModel state submit).source.actualExecution (MaterialRoundSource.depth state.model state.cut)).before = current state ∧
      current (generated state submit) = state.model.source.code.law.next (current state) (incoming state submit) := by
  refine ⟨Machine.Continuation.submitted _ _ _,Machine.Continuation.before _ _ _,?_⟩
  change (Machine.Continuation.extend state.model.source state.cut (incoming state submit)).currentAt
    (MaterialRoundSource.depth state.model state.cut+2) = _
  exact Machine.Continuation.actual_next _ _ _

theorem actual_new_donor_fuel_generates_the_original_feed (state : State)
    (same : state.model.source.code.law = DonorRegenerationLaw.law)
    (needed : WorkerInputSource.Needed (current state))
    (inputs : DonorRegenerationLaw.Inputs (current state)) :
    incoming state true = DonorRegenerationLaw.word ∧
      current (generated state true) = DonorRegenerationLaw.successor (current state) ∧
      UpstreamFeedSource.select (generated state true) true = .offered := by
  have selected := original_primitive_inputs_generate_actual_production state same needed inputs
  have word : incoming state true = DonorRegenerationLaw.word := by simp [incoming,selected]
  have after := (actual_production state true).2.2
  rw [word,same,(DonorRegenerationLaw.actual_next _ inputs).1] at after
  have demand : UpstreamFeedSource.Demand (generated state true) := by
    rw [show UpstreamFeedSource.Demand (generated state true) =
      (WorkerInputSource.Needed (current (generated state true)) ∧
      ¬ WorkerInputLaw.Inputs (current (generated state true)) ∧
      ¬ UpstreamProductionLaw.Inputs (current (generated state true))) from rfl,after]
    exact DonorRegenerationLaw.new_fuel_leaves_the_worker_deficit_visible _ inputs needed
  have resources : UpstreamFeedLaw.Resources (current (generated state true)) :=
    after ▸ DonorRegenerationLaw.new_fuel_has_original_paid_inputs _ inputs
  exact ⟨word,after,UpstreamFeedSource.primitive_resources_generate_the_offer _ same demand resources⟩

theorem refused_production_preserves_actual_stock_and_claims (state : State) (submit : Bool)
    (refused : select state submit ≠ .produced) :
    incoming state submit = [] ∧ (current (generated state submit)).stock = (current state).stock ∧
      (current (generated state submit)).claims = (current state).claims := by
  have word : incoming state submit = [] := by simp [incoming,refused]
  rw [(actual_production state submit).2.2,word]
  exact ⟨rfl,rfl,rfl⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationSource
