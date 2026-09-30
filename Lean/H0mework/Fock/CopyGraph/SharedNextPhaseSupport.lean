import H0mework.Fock.CopyGraph.SharedNextFlow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyPhaseRecovery

open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyNativeModelStep (sourceValue)
open SourceCopyTimeModel (hilbert)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_hilbert (runtime : LivingRuntimeState process) (coordinate : Nat) :
    hilbert (sourceValue runtime) coordinate = if coordinate = runtime.state then 1 else 0 := by
  rw [sourceValue, SourceOperationNative.point, SourceOperationNative.statePoint, SourceClockComplex.ofNative_single]
  simp only [Int.cast_one]
  change SourceSuccessorBoundary.readWord (Finsupp.single runtime.state (1 : ℂ)) coordinate = _
  rw [SourceSuccessorBoundary.readWord_coordinate]
  simp only [Finsupp.single_apply, eq_comm]

theorem native_tail_zero (runtime : LivingRuntimeState process) :
    residual runtime (maximumIndex runtime) 0 (sourceValue runtime) = 0 := by
  have included : runtime.state ≤ cutoff runtime (maximumIndex runtime) 0 := by
    have bound := SourceCopyCurrentCoordinates.maximum_cutoff runtime
    rw [inventory_bound] at bound
    have low := Nat.mul_le_mul_right (runtime.state + 1) (Nat.succ_le_succ (Nat.zero_le runtime.state))
    change 1 * (runtime.state + 1) ≤ (runtime.state + 1) * (runtime.state + 1) at low
    rw [one_mul, ← pow_two] at low
    apply Nat.le_of_succ_le_succ
    change runtime.state + 1 ≤ cutoff runtime (maximumIndex runtime) 0 + 1
    rw [bound]
    exact low
  apply (SourceCopyCurrentCoordinates.complete_fibre runtime (maximumIndex runtime) 0 _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyCurrentCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyCurrentCoordinates.residual_outside _ _ _ _ _ beyond, native_hilbert,
      if_neg (ne_of_gt (lt_of_le_of_lt included beyond))]
    rfl

end
end SourceCopyPhaseRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
