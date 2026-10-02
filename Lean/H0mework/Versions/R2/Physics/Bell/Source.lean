import H0mework.Versions.R2.Physics.Bell.Effects

/-! The original occupied matter field generates the joint Born law at every point. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

theorem joint_probability (ax az bx bz : ℝ) (aunit : ax^2 + az^2 = 1)
    (bunit : bx^2 + bz^2 = 1) :
    effectWeight 0 (jointEffect ax az bx bz aunit bunit) =
      (1 - (ax * bx + az * bz)) / 4 := by
  have exactValue : evaluation 0 (jointEffect ax az bx bz aunit bunit).matrix =
      ((1 - (ax * bx + az * bz)) / 4 : ℝ) := by
    simp [jointEffect, projectorEffect, evaluation, vectorEvaluation, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Source.vector_zero, spinPairCoefficients,
      Fin.sum_univ_four, Fin.sum_univ_two, spinProjector, axisProjector]
    ring
  exact congrArg Complex.re exactValue

theorem joint_probability_at (point : BasePoint) (ax az bx bz : ℝ)
    (aunit : ax^2 + az^2 = 1) (bunit : bx^2 + bz^2 = 1) :
    effectWeight point (jointEffect ax az bx bz aunit bunit) =
      (1 - (ax * bx + az * bz)) / 4 := by
  have upper := Source.phase_star_mul frequency point
  have lower := Source.phase_star_mul (-frequency) point
  change starRingEnd ℂ (upperPhase point) * upperPhase point = 1 at upper
  change starRingEnd ℂ (lowerPhase point) * lowerPhase point = 1 at lower
  have exactValue : evaluation point (jointEffect ax az bx bz aunit bunit).matrix =
      ((1 - (ax * bx + az * bz)) / 4 : ℝ) := by
    simp [jointEffect, projectorEffect, evaluation, vectorEvaluation, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Source.vector, Source.amplitude, spinPairCoefficients,
      Fin.sum_univ_four, Fin.sum_univ_two, spinProjector, axisProjector]
    linear_combination (1 - (ax : ℂ)*bx - (az : ℂ)*bz) / 8 * upper +
      (1 - (ax : ℂ)*bx - (az : ℂ)*bz) / 8 * lower
  exact congrArg Complex.re exactValue

end
end SaturationMonoid.PhysicsCore.Stage10.Bell
