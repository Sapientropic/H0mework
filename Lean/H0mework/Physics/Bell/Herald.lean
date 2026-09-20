import H0mework.Physics.Bell.Probabilities

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

def preparedVector (plus : Bool) (point : BasePoint) : Source.Index → ℂ :=
  if plus then right 0 1 *ᵥ Source.vector point else Source.vector point

theorem color_z_action (v : Source.Index → ℂ) (i : Source.Index) :
    (right 0 1 *ᵥ v) i = (if i.2 = 0 then 1 else -1) * v i := by
  rcases i with ⟨spin, color⟩
  fin_cases color <;>
    simp [right, axis, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

theorem preparedVector_normalized (plus : Bool) (point : BasePoint) :
    (∑ i, star (preparedVector plus point i) * preparedVector plus point i) = 1 := by
  cases plus
  · exact Source.vector_inner_self point
  · change (∑ i, star ((right 0 1 *ᵥ Source.vector point) i) *
        ((right 0 1 *ᵥ Source.vector point) i)) = 1
    simp_rw [color_z_action]
    have same : ∀ i : Source.Index,
        star ((if i.2 = 0 then (1 : ℂ) else -1) * Source.vector point i) *
          ((if i.2 = 0 then (1 : ℂ) else -1) * Source.vector point i) =
            star (Source.vector point i) * Source.vector point i := by
      intro i
      split_ifs <;> simp
    simpa only [same] using Source.vector_inner_self point

def preparedWeight (plus : Bool) (point : BasePoint) (effect : Effect) : ℝ :=
  (vectorEvaluation (preparedVector plus point) effect.matrix).re

theorem reflected_joint_probability (point : BasePoint) (ax az bx bz : ℝ)
    (aunit : ax^2 + az^2 = 1) (bunit : bx^2 + bz^2 = 1) :
    preparedWeight true point (jointEffect ax az bx bz aunit bunit) =
      (1 + ax * bx - az * bz) / 4 := by
  have upper := Source.phase_star_mul frequency point
  have lower := Source.phase_star_mul (-frequency) point
  change starRingEnd ℂ (upperPhase point) * upperPhase point = 1 at upper
  change starRingEnd ℂ (lowerPhase point) * lowerPhase point = 1 at lower
  have exactValue : vectorEvaluation (preparedVector true point)
      (jointEffect ax az bx bz aunit bunit).matrix =
        ((1 + ax * bx - az * bz) / 4 : ℝ) := by
    simp [preparedVector, jointEffect, projectorEffect, vectorEvaluation, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Source.vector, Source.amplitude,
      spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two,
      spinProjector, axisProjector, right, axis]
    linear_combination (1 + (ax : ℂ)*bx - (az : ℂ)*bz) / 8 * upper +
      (1 + (ax : ℂ)*bx - (az : ℂ)*bz) / 8 * lower
  exact congrArg Complex.re exactValue

def heraldAxis (plus : Bool) (b : Axis) : Axis := if plus then b.reflected else b

theorem herald_probability (plus : Bool) (point : BasePoint) (a b : Axis) (x y : Bool) :
    preparedWeight plus point (outcomeEffect a b x y) =
      probability a (heraldAxis plus b) x y := by
  cases plus
  · exact probability_from_source point a b x y
  · rw [outcomeEffect, reflected_joint_probability]
    simp only [Axis.signed, probability, heraldAxis, if_true, Axis.reflected]
    ring


end
end SaturationMonoid.PhysicsCore.Stage10.Bell
