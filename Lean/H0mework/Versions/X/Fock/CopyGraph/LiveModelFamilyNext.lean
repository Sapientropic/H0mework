import H0mework.Versions.X.Fock.CopyGraph.LiveModelFamilyModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyLiveModelFamily

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def previousIndex (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime.tick.next))
    (old : index.val ≤ inventoryBound runtime) : Index (inventoryBound runtime) :=
  ⟨index.val, by have bound := runtime_bound (inventoryBound runtime); omega⟩

theorem previous_retained (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime.tick.next))
    (old : index.val ≤ inventoryBound runtime) : currentIndex runtime (previousIndex runtime index old) 1 = index :=
  Fin.ext (current_index_val runtime (previousIndex runtime index old) 1)

theorem newborn_position (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime.tick.next))
    (fresh : ¬ index.val ≤ inventoryBound runtime) : index.val = inventoryBound runtime + 1 := by
  have inside := index.isLt
  have bound := runtime_bound (inventoryBound runtime.tick.next)
  have next := SourceGraphRecurrence.advance_depth runtime 1
  change inventoryBound runtime.tick.next = inventoryBound runtime + 1 at next
  omega

theorem newborn_material (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime.tick.next))
    (fresh : ¬ index.val ≤ inventoryBound runtime) :
    NativeCopy.Fock.material (inventoryBound runtime.tick.next) index =
      (runtimePayload (inventoryBound runtime)).nativeWrite.target := by
  have born := window_actor_factorizes (inventoryBound runtime + 1) (FamilyModel.Fock.newestIndex (inventoryBound runtime))
  have last : (FamilyModel.Fock.newestIndex (inventoryBound runtime)).val = inventoryBound runtime + 1 :=
    runtime_bound (inventoryBound runtime + 1)
  have same := congrArg (fun position : Nat =>
    ((runtimeAt position).current.visit.current : CanonicalUnitArithmeticRoot.Current))
      ((newborn_position runtime index fresh).trans last.symm)
  exact (actor_birth runtime.tick.next index).1.trans
    (same.trans (born.1.symm.trans (FamilyModel.Fock.newest_material (inventoryBound runtime))))

def next (runtime : LivingRuntimeState process)
    (previous : (index : Index (inventoryBound runtime)) →
      Model SourceJointClockGraph.action.toLinearMap (observer runtime index 0))
    (index : Index (inventoryBound runtime.tick.next)) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime.tick.next index 0) :=
  if old : index.val ≤ inventoryBound runtime then
    castModel (congrArg (fun actor => observer runtime.tick.next actor 0) (previous_retained runtime index old))
      (oldNext runtime (previousIndex runtime index old) (previous (previousIndex runtime index old)))
  else projection SourceJointClockGraph.action.toLinearMap (observer runtime.tick.next index 0) (sourceValue runtime.tick.next)

theorem next_source (runtime : LivingRuntimeState process)
    (previous : (index : Index (inventoryBound runtime)) →
      Model SourceJointClockGraph.action.toLinearMap (observer runtime index 0))
    (generated : ∀ index, previous index = projection SourceJointClockGraph.action.toLinearMap (observer runtime index 0) (sourceValue runtime))
    (index : Index (inventoryBound runtime.tick.next)) :
    next runtime previous index =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime.tick.next index 0) (sourceValue runtime.tick.next) := by
  unfold next
  split_ifs with old
  · rw [generated, old_next_source, cast_model_projection]
  · rfl

theorem family_next (runtime : LivingRuntimeState process) : next runtime (family runtime) = family runtime.tick.next := by
  funext index
  exact (next_source runtime (family runtime) (family_source runtime) index).trans (family_source runtime.tick.next index).symm

end
end SourceCopyLiveModelFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
