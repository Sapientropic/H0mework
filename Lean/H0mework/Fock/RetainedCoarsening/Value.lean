import H0mework.Fock.RetainedCoarsening.Count

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (At next value)
open SourceGeneratedAcquisitionContinuation
open SourceConditionalNativeMerge (inventoryCount)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

theorem merged_next_value (runtime : LivingRuntimeState process) (frame : At runtime Fine) (forget : Fine → Coarse)
    (added : Fine) (coarse : Coarse)
    (outside : ∀ key, key ∉ frame.keys → (frame.native key).1 = 0) :
    value runtime.tick.next
      (merge (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val (next runtime frame added) forget) coarse =
        value runtime.tick.next
          (next runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) (forget added)) coarse := by
  rw [value_moment, count_next runtime frame forget added coarse outside, moment_next runtime frame forget added coarse outside,
    SourceRetainedReceiver.next_value]
  change _ = if coarse = forget added then
    value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse +
      (((inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse + 1 : Nat) : ℚ)⁻¹ : ℂ) •
        (SourceConditionalInventory.born (inventoryBound runtime) -
          value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse)
    else value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) coarse
  by_cases selected : forget added = coarse
  · simp only [if_pos selected, if_pos selected.symm, Rat.cast_natCast]
    rw [← counted_value runtime frame forget coarse]
    let total := inventoryCount frame.keys forget (inventoryBound runtime) frame.native coarse
    have scalar : (((total + 1 : Nat) : ℂ)⁻¹) * (total : ℂ) = 1 - (((total + 1 : Nat) : ℂ)⁻¹) := by
      have nonzero : ((total + 1 : Nat) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      field_simp
      push_cast
      ring
    dsimp only [total] at scalar
    simp only [smul_add, smul_smul, scalar, sub_smul, one_smul, smul_sub]
    abel
  · simp only [if_neg selected, if_neg (Ne.symm selected), add_zero]
    exact (value_moment runtime frame forget coarse).symm

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
