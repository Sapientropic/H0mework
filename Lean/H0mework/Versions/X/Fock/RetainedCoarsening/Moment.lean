import H0mework.Versions.X.Fock.RetainedCoarsening.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (Frame At)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

def moment (runtime : LivingRuntimeState process) (frame : At runtime Fine) (forget : Fine → Coarse)
    (coarse : Coarse) : SourceJointClockGraph.Carrier :=
  ∑ key ∈ frame.keys, if forget key = coarse then ((frame.native key).1 : ℂ) • SourceRetainedReceiver.value runtime frame key else 0

theorem value_moment (runtime : LivingRuntimeState process) (frame : At runtime Fine) (forget : Fine → Coarse)
    (coarse : Coarse) :
    SourceRetainedReceiver.value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse =
      ((SourceConditionalNativeMerge.inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse : ℂ)⁻¹) •
        moment runtime frame forget coarse := by
  rw [value_merge, moment, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro key _
  by_cases selected : forget key = coarse
  · simp only [weight, if_pos selected, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, mul_smul]
    rw [smul_comm]
  · simp only [weight, if_neg selected, Rat.cast_zero, zero_smul, smul_zero]

theorem count_zero_moment (runtime : LivingRuntimeState process) (frame : At runtime Fine) (forget : Fine → Coarse)
    (coarse : Coarse)
    (empty : SourceConditionalNativeMerge.inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse = 0) :
    moment runtime frame forget coarse = 0 := by
  apply Finset.sum_eq_zero
  intro key inside
  have term : (if forget key = coarse then (frame.native key).1 else 0) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun key _ => Nat.zero_le (if forget key = coarse then (frame.native key).1 else 0))).mp empty key inside
  by_cases selected : forget key = coarse
  · simp only [if_pos selected] at term ⊢
    rw [term, Nat.cast_zero, zero_smul]
  · exact if_neg selected

theorem counted_value (runtime : LivingRuntimeState process) (frame : At runtime Fine) (forget : Fine → Coarse)
    (coarse : Coarse) :
    (SourceConditionalNativeMerge.inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse : ℂ) •
      SourceRetainedReceiver.value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse =
        moment runtime frame forget coarse := by
  by_cases empty : SourceConditionalNativeMerge.inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse = 0
  · rw [empty, Nat.cast_zero, zero_smul, count_zero_moment runtime frame forget coarse empty]
  · rw [value_moment, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr empty), one_smul]

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
