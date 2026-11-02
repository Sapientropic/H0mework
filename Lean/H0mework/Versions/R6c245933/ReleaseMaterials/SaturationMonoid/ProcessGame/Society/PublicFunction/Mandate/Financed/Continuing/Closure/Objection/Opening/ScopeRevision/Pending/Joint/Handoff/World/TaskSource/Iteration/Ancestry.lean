import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Origin

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
open Institutions.Capitalism.Universal.Source.Program
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry.Planning
noncomputable section

def basisKeys {packet : Packet} (basis : FutureOrigin packet) : List (Packet × List Action) :=
  (basis.first,basis.pending) :: basis.ancestors.map (fun old => (old.first,old.pending))

theorem basis_keys_advance {first last : Packet} (basis : FutureOrigin first)
    (native : Unit → Input.Event.Evolution first last) : basisKeys (basis.advance native) = basisKeys basis := by
  simp only [basisKeys,FutureOrigin.advance,List.map_map,ReceivedBasis.advance,Function.comp_def]

def KeepsAncestry (first last : Current) : Prop :=
  ∀ basis,first.origin = some basis →
    ∃ carried,last.origin = some carried ∧ basisKeys basis <:+ basisKeys carried

theorem KeepsAncestry.refl (state : Current) : KeepsAncestry state state :=
  fun basis found => ⟨basis,found,List.suffix_refl _⟩

theorem KeepsAncestry.trans {first middle last : Current}
    (earlier : KeepsAncestry first middle) (later : KeepsAncestry middle last) : KeepsAncestry first last := by
  intro basis found
  obtain ⟨mid,midFound,firstKept⟩ := earlier basis found
  obtain ⟨final,finalFound,laterKept⟩ := later mid midFound
  exact ⟨final,finalFound,firstKept.trans laterKept⟩

theorem after_keeps_every_basis (state : Current) {cache : Owned.PublicTask.Local.Inquiry.Frame state.task}
    (made : GlobalPolicy.Service state.task cache) : KeepsAncestry state (after state made) := by
  intro basis received
  refine ⟨_,after_carries_the_same_received_basis state made basis received,?_⟩
  have same := basis_keys_advance basis
    (fun _ => Service.Actual.reconstructedNative state.ready.2 state.cursor.pending made)
  exact ⟨[],(List.nil_append _).trans same.symm⟩

theorem repair_keeps_every_basis {state : Current} (made : Refusal.Result state) :
    KeepsAncestry state made.nextCurrent := by
  intro basis received
  refine ⟨_,made.next_current_has_its_received_basis,?_⟩
  have same : basisKeys made.nextOrigin = basisKeys basis := by
    simp only [Refusal.Result.nextOrigin,received]
    exact basis_keys_advance _ _
  exact ⟨[],(List.nil_append _).trans same.symm⟩

theorem Step.keeps_every_received_basis {state : Current} (step : Step state) : KeepsAncestry state step.target := by
  cases original : step.original <;> cases repaired : step.recovery
  · simp only [Step.target,Step.transition,original,repaired]
    exact fun basis received => ⟨basis,received,List.suffix_refl _⟩
  · simp only [Step.target,Step.transition,original,repaired]
    exact repair_keeps_every_basis _
  · simp only [Step.target,Step.transition,original,repaired]
    exact after_keeps_every_basis _ _
  · simp only [Step.target,Step.transition,original,repaired]
    exact after_keeps_every_basis _ _

theorem Run.keeps_every_received_basis {state : Current} {count : Nat} (run : Run state count) :
    KeepsAncestry state run.finishCurrent := by
  induction run with
  | observed state => exact KeepsAncestry.refl state
  | blocked step generated blocked => exact step.keeps_every_received_basis
  | entered step generated live later ih => exact step.keeps_every_received_basis.trans ih

namespace Incoming

theorem Result.keeps_every_earlier_received_basis {state : Current} {word : List Action}
    (made : Result state word) : KeepsAncestry state made.target := by
  intro basis received
  refine ⟨_,made.origin_is_the_same_post_response,?_⟩
  have same : basisKeys ((FutureOrigin.receiveAfter state.origin made.response).advance (fun _ => made.rebuilt.native)) =
      [(made.response.next.saved,made.response.report.residual)] ++ basisKeys basis := by
    calc
      _ = basisKeys (FutureOrigin.receiveAfter state.origin made.response) := basis_keys_advance _ _
      _ = _ := by
        simp only [FutureOrigin.receiveAfter,received,basisKeys,List.map_cons,List.map_map,
          ReceivedBasis.advance,FutureOrigin.basis,Function.comp_def,List.cons_append,List.nil_append]
        rfl
  exact ⟨_,same.symm⟩

theorem Round.keeps_every_earlier_received_basis {state : Current} {word : List Action}
    (made : Round state word) : KeepsAncestry state made.target :=
  made.received.keeps_every_earlier_received_basis.trans made.step.keeps_every_received_basis

theorem Run.keeps_every_earlier_received_basis {state : Current} {words : List (List Action)}
    (run : Run state words) : KeepsAncestry state run.finish := by
  induction run with
  | observed state => exact KeepsAncestry.refl state
  | entered made generated tail ih => exact made.keeps_every_earlier_received_basis.trans ih

end Incoming
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Current
