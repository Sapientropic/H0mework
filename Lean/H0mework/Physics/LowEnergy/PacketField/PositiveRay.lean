import H0mework.Physics.LowEnergy.PacketField.Alignment
import H0mework.Physics.LowEnergy.PacketField.Lift

/-! The actual paired frame is constant on positive rays. Radial window
derivatives can therefore consume it without differentiating an angular chart. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open Rotation
noncomputable section

theorem momentumRadius_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    momentumRadius (r • k) = r * momentumRadius k := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg positive.le (Real.sqrt_nonneg _))).mp
  change (momentumRadius (r • k))^2 = (r * momentumRadius k)^2
  rw [mul_pow, momentumRadius_square, momentumRadius_square]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem transverseRadius_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    transverseRadius (r • k) = r * transverseRadius k := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg positive.le (Real.sqrt_nonneg _))).mp
  change (transverseRadius (r • k))^2 = (r * transverseRadius k)^2
  rw [mul_pow, transverseRadius_square, transverseRadius_square]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem firstNonzero_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    firstNonzero (r • k) = r * firstNonzero k := by
  have scaled (i : Fin 3) : r * k i ≠ 0 ↔ k i ≠ 0 :=
    mul_ne_zero_iff.trans (and_iff_right positive.ne')
  simp only [firstNonzero, Pi.smul_apply, smul_eq_mul, scaled]
  split_ifs <;> rfl

theorem lineSign_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    lineSign (r • k) = lineSign k := by
  simp only [lineSign, firstNonzero_pos_smul r positive]
  rcases lt_trichotomy (firstNonzero k) 0 with neg | zero | pos
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg positive neg), Real.sign_of_neg neg]
  · rw [zero, mul_zero]
  · rw [Real.sign_of_pos (mul_pos positive pos), Real.sign_of_pos pos]

theorem representative_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    representative (r • k) = r • representative k := by
  simp only [representative, lineSign_pos_smul r positive]
  exact smul_comm _ _ _

theorem borelParameters_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    borelParameters (r • k) = borelParameters k := by
  have firstC : firstCosine (r • k) = firstCosine k := by
    simp only [firstCosine, transverseRadius_pos_smul r positive,
      Pi.smul_apply, smul_eq_mul, mul_eq_zero, positive.ne', false_or]
    split_ifs
    · rfl
    · rw [mul_div_mul_left _ _ positive.ne']
  have firstS : firstSine (r • k) = firstSine k := by
    simp only [firstSine, transverseRadius_pos_smul r positive,
      Pi.smul_apply, smul_eq_mul, mul_eq_zero, positive.ne', false_or]
    split_ifs
    · rfl
    · rw [mul_div_mul_left _ _ positive.ne']
  simp only [borelParameters, momentumRadius_pos_smul r positive,
    transverseRadius_pos_smul r positive, Pi.smul_apply, smul_eq_mul,
    mul_div_mul_left _ _ positive.ne', firstC, firstS]

theorem pairedParameters_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    pairedParameters (r • k) = pairedParameters k := by
  rw [pairedParameters, representative_pos_smul r positive,
    borelParameters_pos_smul r positive]
  rfl

theorem pairedRotation_pos_smul (r : ℝ) (positive : 0 < r) (k : Fin 3 → ℝ) :
    pairedRotation (r • k) = pairedRotation k := by
  change borelRotation (representative (r • k)) = borelRotation (representative k)
  rw [representative_pos_smul r positive]
  simp only [borelRotation, borelParameters_pos_smul r positive]

theorem pairedCircleAction_pos_smul {ι : Type*} [Fintype ι]
    (circleY circleZ : CircleData ι) (r : ℝ) (positive : 0 < r)
    (k : Fin 3 → ℝ) (field : ι → ℂ) :
    circleAction circleZ (pairedParameters (r • k)).2
      (circleAction circleY (pairedParameters (r • k)).1 field) =
    circleAction circleZ (pairedParameters k).2
      (circleAction circleY (pairedParameters k).1 field) := by
  rw [pairedParameters_pos_smul r positive]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
