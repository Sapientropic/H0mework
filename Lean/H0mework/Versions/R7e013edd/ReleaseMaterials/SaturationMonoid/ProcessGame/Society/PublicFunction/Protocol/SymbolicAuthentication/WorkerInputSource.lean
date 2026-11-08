import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RecycledQuorumMaterial (Current Action)
open MaterialRoundSource (Bound)

def Needed (current : Current) : Prop :=
  current.stock 2 .waste < 1 ∨ current.stock 2 .energy < 1 ∨ current.stock 2 .labor < 1
instance (current : Current) : Decidable (Needed current) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
variable (old : Bound) (count : Nat)
abbrev before := MaterialRoundSource.before old count
def incoming : List Action := if Needed (before old count) ∧ WorkerInputLaw.Inputs (before old count) then WorkerInputLaw.word else []
abbrev arrived : Bound :=
  ⟨old.base,old.scope,Machine.Continuation.extend old.source count (incoming old count),old.law_exact,old.task_exact⟩
abbrev afterInput := MaterialRoundSource.before (arrived old count) (count+1)
abbrev nextArrival := FuelMaterialSource.incoming (arrived old count) (count+1)
abbrev status := FuelMaterialSource.status (arrived old count) (count+1)

structure Result : Type where
  private mk ::
  upstream : Native.Authority.FullDisposition (arrived old count) (MaterialRoundSource.depth old count)
  upstream_exact : upstream = Native.Authority.fullGenerate (arrived old count) (MaterialRoundSource.depth old count)
  next : MaterialRoundConsumer.Result (arrived old count) (count+1) (nextArrival old count)
  next_exact : next = FuelMaterialSource.produce (arrived old count) (count+1)
def produce : Result old count :=
  ⟨Native.Authority.fullGenerate (arrived old count) (MaterialRoundSource.depth old count),rfl,
    FuelMaterialSource.produce (arrived old count) (count+1),rfl⟩

theorem the_upstream_word_is_an_actual_occurrence_at_the_original_endpoint :
    ((arrived old count).source.actualExecution (MaterialRoundSource.depth old count)).submitted = incoming old count ∧
      ((arrived old count).source.actualExecution (MaterialRoundSource.depth old count)).before = before old count ∧
      afterInput old count = old.source.code.law.next (before old count) (incoming old count) := by
  refine ⟨Machine.Continuation.submitted old.source count _,Machine.Continuation.before old.source count _,?_⟩
  have actual := Machine.Continuation.actual_next old.source count (incoming old count)
  have ordinal : MaterialRoundSource.depth (arrived old count) (count+1)+1 = MaterialRoundSource.depth old count+2 := by
    change old.source.history.length+1+(count+1)+1 = old.source.history.length+1+count+2
    omega
  change (arrived old count).source.currentAt _ = _
  rw [ordinal]
  exact actual

theorem a_funded_actual_deficit_generates_the_worker_inputs
    (same : old.source.code.law = WorkerInputLaw.law)
    (needed : Needed (before old count)) (inputs : WorkerInputLaw.Inputs (before old count)) :
    incoming old count = WorkerInputLaw.word ∧
      afterInput old count = WorkerInputLaw.successor (before old count) ∧
      FuelMaterialSource.Inputs (afterInput old count) ∧
      ∀ item ∈ old.source.code.law.rawItems (before old count) (incoming old count), old.source.code.law.Valid item.before item.request := by
  have selected : incoming old count = WorkerInputLaw.word := by simp [incoming,needed,inputs]
  have actual := (the_upstream_word_is_an_actual_occurrence_at_the_original_endpoint old count).2.2
  rw [same,selected,(WorkerInputLaw.actual_next _ inputs).1] at actual
  exact ⟨selected,actual,actual ▸ WorkerInputLaw.upstream_transfers_generate_all_original_worker_and_material_inputs _ inputs,
    by rw [same,selected];exact (WorkerInputLaw.actual_next _ inputs).2⟩

theorem existing_worker_inputs_do_not_pay_for_an_unneeded_transfer
    (unneeded : ¬ Needed (before old count)) : incoming old count = [] := by simp [incoming,unneeded]

theorem missing_upstream_resources_do_not_emit_a_transfer
    (missing : ¬ WorkerInputLaw.Inputs (before old count)) : incoming old count = [] := by simp [incoming,missing]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WorkerInputSource
