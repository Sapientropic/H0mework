import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Input

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
open Institutions.Capitalism.Universal.Source.Program
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry.Planning
noncomputable section

/-- Internal continuation retains the same received occurrence and raw residual basis. -/
def KeepsBasis (first last : Current) : Prop :=
  ∀ basis,first.origin = some basis →
    ∃ carried,last.origin = some carried ∧ carried.first = basis.first ∧ carried.pending = basis.pending

theorem KeepsBasis.refl (state : Current) : KeepsBasis state state :=
  fun basis received => ⟨basis,received,rfl,rfl⟩

theorem KeepsBasis.trans {first middle last : Current}
    (earlier : KeepsBasis first middle) (later : KeepsBasis middle last) : KeepsBasis first last := by
  intro basis received
  obtain ⟨mid,found,firstSame,pendingSame⟩ := earlier basis received
  obtain ⟨final,foundFinal,firstFinal,pendingFinal⟩ := later mid found
  exact ⟨final,foundFinal,firstFinal.trans firstSame,pendingFinal.trans pendingSame⟩

theorem after_keeps_basis (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) : KeepsBasis state (after state made) := by
  intro basis received
  have carried := after_carries_the_same_received_basis state made basis received
  have kept := basis.advance_keeps_the_received_basis
    (fun _ => Service.Actual.reconstructedNative state.ready.2 state.cursor.pending made)
  exact ⟨_,carried,kept⟩

theorem repaired_keeps_basis {state : Current} (made : Refusal.Result state) :
    KeepsBasis state made.nextCurrent := by
  intro basis received
  exact ⟨_,made.next_current_has_its_received_basis,
    (made.repair_keeps_the_original_received_basis basis received).1,
    (made.repair_keeps_the_original_received_basis basis received).2⟩

theorem Step.keeps_the_received_basis {state : Current} (step : Step state) : KeepsBasis state step.target := by
  cases original : step.original <;> cases repaired : step.recovery
  · simp only [Step.target,Step.transition,original,repaired]
    exact fun basis received => ⟨basis,received,rfl,rfl⟩
  · simp only [Step.target,Step.transition,original,repaired]
    exact repaired_keeps_basis _
  · simp only [Step.target,Step.transition,original,repaired]
    exact after_keeps_basis _ _
  · simp only [Step.target,Step.transition,original,repaired]
    exact after_keeps_basis _ _

theorem Run.keeps_the_received_basis {state : Current} {count : Nat} (run : Run state count) :
    KeepsBasis state run.finishCurrent := by
  induction run with
  | observed state => exact KeepsBasis.refl state
  | blocked step generated blocked => exact step.keeps_the_received_basis
  | entered step generated live later ih => exact step.keeps_the_received_basis.trans ih

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
