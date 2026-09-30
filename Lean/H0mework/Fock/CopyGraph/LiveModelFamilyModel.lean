import H0mework.Fock.CopyGraph.LiveModelFamilySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyLiveModelFamily

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def castModel {first second : SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier} (same : first = second) :
    Model SourceJointClockGraph.action.toLinearMap first → Model SourceJointClockGraph.action.toLinearMap second :=
  Eq.mp (congrArg (Model SourceJointClockGraph.action.toLinearMap) same)

theorem cast_model_projection {first second : SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier}
    (same : first = second) (value : SourceJointClockGraph.Carrier) :
    castModel same (projection SourceJointClockGraph.action.toLinearMap first value) =
      projection SourceJointClockGraph.action.toLinearMap second value := by
  cases same
  rfl

def birthCache (position : Nat) : (elapsed : Nat) →
    Model SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) elapsed)
  | 0 => projection SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) 0)
      (sourceValue (runtimeAt position))
  | elapsed + 1 => SourceCopyNativeModelStep.cache (runtimeAt position) (birthIndex position) elapsed

theorem birth_cache_source (position elapsed : Nat) :
    birthCache position elapsed =
      projection SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) elapsed)
        (sourceValue ((runtimeAt position).advance elapsed)) := by
  cases elapsed with
  | zero => rfl
  | succ elapsed => exact SourceCopyNativeModelStep.cache_source _ _ elapsed

def family (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime index 0) :=
  castModel (observer_birth runtime index).symm (birthCache index.val (age runtime index))

theorem family_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    family runtime index = projection SourceJointClockGraph.action.toLinearMap (observer runtime index 0) (sourceValue runtime) := by
  rw [family, birth_cache_source, cast_model_projection, birth_reaches_current]

-- The first material is read from the original source. Later materials reuse
-- the existing Model update and its actual additional samples.
def birthNext (position : Nat) : (elapsed : Nat) →
    Model SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) elapsed) →
      Model SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) (elapsed + 1))
  := by
    intro elapsed
    cases elapsed with
    | zero => exact fun _ => SourceCopyNativeModelStep.cache (runtimeAt position) (birthIndex position) 0
    | succ elapsed =>
      change Model SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) (elapsed + 1)) →
        Model SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) (elapsed + 2))
      exact fun previous => SourceCopyNativeModelStep.advanceModel (runtimeAt position) (birthIndex position) elapsed previous
        (SourceCopyFutureUpdate.samples (runtimeAt position) (birthIndex position) elapsed
          (sourceValue ((runtimeAt position).advance (elapsed + 1))))

theorem birth_next_source (position elapsed : Nat) :
    birthNext position elapsed
      (projection SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) elapsed)
        (sourceValue ((runtimeAt position).advance elapsed))) =
      projection SourceJointClockGraph.action.toLinearMap (observer (runtimeAt position) (birthIndex position) (elapsed + 1))
        (sourceValue ((runtimeAt position).advance (elapsed + 1))) := by
  cases elapsed with
  | zero => exact SourceCopyNativeModelStep.cache_source _ _ 0
  | succ elapsed => exact SourceCopyNativeModelStep.native_model_next _ _ elapsed (elapsed + 1)

theorem birth_next_cache (position elapsed : Nat) :
    birthNext position elapsed (birthCache position elapsed) = birthCache position (elapsed + 1) := by
  cases elapsed <;> rfl

theorem observer_next_birth (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    observer runtime.tick.next (currentIndex runtime index 1) 0 =
      observer (runtimeAt index.val) (birthIndex index.val) (age runtime index + 1) := by
  apply observer_identified (runtimeAt index.val) runtime.tick.next (birthIndex index.val) (currentIndex runtime index 1)
  · exact congrArg (fun current : LivingRuntimeState process => current.tick.next) (birth_reaches_current runtime index)
  · exact (current_index_val runtime index 1).symm

def oldNext (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (previous : Model SourceJointClockGraph.action.toLinearMap (observer runtime index 0)) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime.tick.next (currentIndex runtime index 1) 0) :=
  castModel (observer_next_birth runtime index).symm
    (birthNext index.val (age runtime index) (castModel (observer_birth runtime index) previous))

theorem old_next_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    oldNext runtime index (projection SourceJointClockGraph.action.toLinearMap (observer runtime index 0) (sourceValue runtime)) =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime.tick.next (currentIndex runtime index 1) 0)
        (sourceValue runtime.tick.next) := by
  rw [oldNext, cast_model_projection]
  have oldSource : sourceValue runtime = sourceValue ((runtimeAt index.val).advance (age runtime index)) :=
    congrArg sourceValue (birth_reaches_current runtime index).symm
  rw [oldSource]
  rw [birth_next_source, cast_model_projection]
  congr 1
  exact congrArg (fun current : LivingRuntimeState process => sourceValue current.tick.next) (birth_reaches_current runtime index)

end
end SourceCopyLiveModelFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
