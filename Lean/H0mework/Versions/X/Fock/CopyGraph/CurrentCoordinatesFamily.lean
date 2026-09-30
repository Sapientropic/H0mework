import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesAccount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def maximumIndex (runtime : LivingRuntimeState process) : Index (inventoryBound runtime) :=
  Fin.last (NativeWindow.bound (runtimeAt (inventoryBound runtime)).current.visit.current)

theorem maximum_index_val (runtime : LivingRuntimeState process) : (maximumIndex runtime).val = inventoryBound runtime :=
  runtime_bound (inventoryBound runtime)

theorem cutoff_le (runtime : LivingRuntimeState process) (left right : Index (inventoryBound runtime)) (steps : Nat)
    (ordered : left.val ≤ right.val) : cutoff runtime left steps ≤ cutoff runtime right steps := by
  simp only [cutoff, SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right ordered 1)) 1

theorem cutoff_le_maximum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    cutoff runtime index steps ≤ cutoff runtime (maximumIndex runtime) steps := by
  apply cutoff_le
  have inside := index.isLt
  have bound := runtime_bound (inventoryBound runtime)
  rw [maximum_index_val]
  omega

def coordinateInclusion (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    Fin (cutoff runtime index 0 + 1) → Fin (cutoff runtime (maximumIndex runtime) 0 + 1) :=
  fun coordinate => ⟨coordinate.val, lt_of_lt_of_le coordinate.isLt (Nat.add_le_add_right (cutoff_le_maximum runtime index 0) 1)⟩

def restrictCoordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    Coordinates runtime (maximumIndex runtime) 0 →ₗ[ℂ] Coordinates runtime index 0 where
  toFun value := (fun coordinate => value.1 (coordinateInclusion runtime index coordinate), value.2.1, value.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    restrictCoordinates runtime index (sourceRead runtime (maximumIndex runtime) 0 target) = sourceRead runtime index 0 target := rfl

def jointObserver (runtime : LivingRuntimeState process) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] (Index (inventoryBound runtime) → SourceJointClockGraph.Carrier) :=
  LinearMap.pi (fun index => observer runtime index 0)

theorem joint_kernel (runtime : LivingRuntimeState process) :
    LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (jointObserver runtime)) =
      LinearMap.ker (sourceRead runtime (maximumIndex runtime) 0) := by
  apply le_antisymm
  · intro target invisible
    have component : target ∈ LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap
        (observer runtime (maximumIndex runtime) 0)) := by
      apply (mem_kernel_iff _ _ target).mpr
      intro ticks
      exact congrFun ((mem_kernel_iff _ _ target).mp invisible ticks) (maximumIndex runtime)
    rwa [kernel_exact runtime (maximumIndex runtime) 0] at component
  · apply invariant_submodule_le_kernel SourceJointClockGraph.action.toLinearMap (jointObserver runtime)
      (LinearMap.ker (sourceRead runtime (maximumIndex runtime) 0))
    · intro target invisible
      ext index
      apply observer_zero runtime index 0 target
      have actual := congrArg (restrictCoordinates runtime index) invisible
      rwa [restrict_source, map_zero] at actual
    · intro target invisible
      exact source_zero_next runtime (maximumIndex runtime) 0 target invisible

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
