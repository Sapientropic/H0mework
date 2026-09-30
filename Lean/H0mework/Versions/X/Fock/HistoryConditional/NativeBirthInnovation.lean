import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthError

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

private theorem innovation_energy (count : Nat) (before added : SourceJointClockGraph.Carrier) :
    (count : ℝ) * ‖before - (before + (((count + 1 : Nat) : ℂ)⁻¹) • (added - before))‖ ^ 2 +
      ‖added - (before + (((count + 1 : Nat) : ℂ)⁻¹) • (added - before))‖ ^ 2 =
        (count : ℝ) / (count + 1) * ‖added - before‖ ^ 2 := by
  have nonzero : (count : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero count
  have coefficient : (1 : ℂ) - ((count + 1 : Nat) : ℂ)⁻¹ = (count : ℂ) / (count + 1) := by
    push_cast
    field_simp
    ring
  have added_residual :
      added - (before + (((count + 1 : Nat) : ℂ)⁻¹) • (added - before)) =
        ((count : ℂ) / (count + 1)) • (added - before) := by
    rw [← coefficient, sub_smul, one_smul]
    abel
  rw [norm_sub_rev before, add_sub_cancel_left, added_residual]
  rw [show (count : ℂ) + 1 = ((count + 1 : Nat) : ℂ) by push_cast; rfl]
  simp only [norm_smul, mul_pow, norm_inv, norm_div, Complex.norm_natCast]
  push_cast
  have nonzeroReal : (count : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

def innovation (runtime : LivingRuntimeState process) (read : Nat → Key) : ℝ :=
  let count := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1
  (count : ℝ) / (count + 1) *
    ‖SourceConditionalInventory.born (inventoryBound runtime) -
      SourceConditionalNativePosterior.decoder runtime read (read (inventoryBound runtime + 1))‖ ^ 2

theorem minimum_update (runtime : LivingRuntimeState process) (read : Nat → Key) :
    total runtime.tick.next read = total runtime read + innovation runtime read := by
  rw [minimum_difference, add_assoc, decoder_next, if_pos rfl]
  simp only [Rat.cast_natCast]
  rw [innovation_energy]
  rfl

omit [DecidableEq Key] in
theorem mean_update_energy (count : Nat) (before added : SourceJointClockGraph.Carrier) :
    (count : ℝ) * ‖before - (before + (((count + 1 : Nat) : ℂ)⁻¹) • (added - before))‖ ^ 2 +
      ‖added - (before + (((count + 1 : Nat) : ℂ)⁻¹) • (added - before))‖ ^ 2 =
        (count : ℝ) / (count + 1) * ‖added - before‖ ^ 2 :=
  innovation_energy count before added

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
