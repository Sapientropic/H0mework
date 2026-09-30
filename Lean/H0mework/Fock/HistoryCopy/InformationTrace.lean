import H0mework.Fock.PrimeFieldCalculation.ContinuationSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyInventory

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private def retainedIndex (runtime : LivingRuntimeState process)
    (actor : FamilyModel.Fock.Index (inventoryBound runtime)) (count : Nat) :
    Fin (NativeWindow.bound (runtime.advance count).current.visit.current + 1) :=
  ⟨actor.val, by
    have present := actor.isLt
    have initial := runtime_bound (inventoryBound runtime)
    have root := inventory_bound runtime
    have target := inventory_bound (runtime.advance count)
    change NativeWindow.bound (runtime.advance count).current.visit.current = (runtime.advance count).state at target
    have future := congrArg (fun current : LivingRuntimeState process => current.state) (advance_original runtime count)
    rw [runtimeAt_state] at future
    change (runtime.advance count).state = runtime.state + count at future
    have sourceLimit : actor.val < runtime.state + 1 :=
      present.trans_eq (congrArg (fun n : Nat => n + 1) (initial.trans root))
    have increasing : runtime.state + 1 ≤ (runtime.state + count) + 1 :=
      Nat.add_le_add_right (Nat.le_add_right runtime.state count) 1
    exact (sourceLimit.trans_le increasing).trans_eq
      (congrArg (fun n : Nat => n + 1) (future.symm.trans target.symm))⟩

theorem normal_copy_cost (runtime : LivingRuntimeState process)
    (actor : FamilyModel.Fock.Index (inventoryBound runtime)) :
    let material := NativeCopy.Fock.material (inventoryBound runtime) actor
    inventoryCost material (normal runtime).targetRuntime.state = inventoryCost material runtime.state +
      ∑ step ∈ Finset.range ((frontier runtime).stageCount + 1), increment material (runtime.advance step).state := by
  let material := NativeCopy.Fock.material (inventoryBound runtime) actor
  have evolve (count : Nat) (inside : count ≤ (frontier runtime).stageCount + 1) :
      inventoryCost material (runtime.advance count).state = inventoryCost material runtime.state +
        ∑ step ∈ Finset.range count, increment material (runtime.advance step).state := by
    induction count with
    | zero => simp [LivingRuntimeState.advance]
    | succ count previous =>
        have generated := ((realization runtime).operationAt ⟨count, by omega⟩).2.2.2.2 (retainedIndex runtime actor count)
        change inventoryCost material (runtime.advance (count + 1)).state =
          inventoryCost material (runtime.advance count).state + increment material (runtime.advance count).state at generated
        rw [generated, previous (by omega), Finset.sum_range_succ]
        ring
  exact evolve ((frontier runtime).stageCount + 1) le_rfl

theorem generated_next_copy_cost (runtime : LivingRuntimeState process)
    (actor : FamilyModel.Fock.Index (inventoryBound runtime)) :
    let material := NativeCopy.Fock.material (inventoryBound runtime) actor
    inventoryCost material (normal runtime).targetRuntime.tick.next.state = inventoryCost material runtime.state +
      ∑ step ∈ Finset.range ((frontier runtime).stageCount + 2), increment material (runtime.advance step).state := by
  let material := NativeCopy.Fock.material (inventoryBound runtime) actor
  change inventoryCost material (normal runtime).targetRuntime.tick.next.state = inventoryCost material runtime.state +
    ∑ step ∈ Finset.range ((frontier runtime).stageCount + 2), increment material (runtime.advance step).state
  have fresh := cost_step material (runtime.advance ((frontier runtime).stageCount + 1)).state
  change inventoryCost material (normal runtime).targetRuntime.tick.next.state =
    inventoryCost material (normal runtime).targetRuntime.state +
      increment material (runtime.advance ((frontier runtime).stageCount + 1)).state at fresh
  rw [fresh, normal_copy_cost]
  conv_rhs => rw [Finset.sum_range_succ]
  ring

end
end SourceCopyInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
