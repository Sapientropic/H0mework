import H0mework.Versions.R2.Physics.Bell.Runtime

/-! Fixed color-X preparation reads the same source in the phi+ frame.
The preparation operation requires no stochastic herald or outcome selection. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

def phiVector (point : BasePoint) : Source.Index → ℂ :=
  right 1 0 *ᵥ preparedVector true point

def colorXFrame (b : Axis) : Axis := ⟨b.x, -b.z, by simpa using b.unit⟩

theorem color_x_action (v : Source.Index → ℂ) (spin : Fin 4) (color : Fin 2) :
    (right 1 0 *ᵥ v) (spin, color) = if color=0 then v (spin, 1) else v (spin, 0) := by
  fin_cases color <;>
    simp [right, axis, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply]

theorem phiVector_normalized (point : BasePoint) :
    (∑ i, star (phiVector point i) * phiVector point i) = 1 := by
  have h := preparedVector_normalized true point
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at h ⊢
  simp only [phiVector, color_x_action]
  simpa [add_comm] using h

theorem phi_joint_probability (point : BasePoint) (ax az bx bz : ℝ)
    (aunit : ax^2+az^2=1) (bunit : bx^2+bz^2=1) :
    (vectorEvaluation (phiVector point) (jointEffect ax az bx bz aunit bunit).matrix).re =
      (1+ax*bx+az*bz)/4 := by
  have upper := Source.phase_star_mul frequency point
  have lower := Source.phase_star_mul (-frequency) point
  change starRingEnd ℂ (upperPhase point) * upperPhase point = 1 at upper
  change starRingEnd ℂ (lowerPhase point) * lowerPhase point = 1 at lower
  have h : vectorEvaluation (phiVector point) (jointEffect ax az bx bz aunit bunit).matrix =
      ((1+ax*bx+az*bz)/4 : ℝ) := by
    simp [phiVector, preparedVector, jointEffect, projectorEffect, vectorEvaluation, Matrix.mulVec,
      Matrix.mul_apply,
      dotProduct, Fintype.sum_prod_type, Source.vector, Source.amplitude,
      spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two,
      spinProjector, axisProjector, right, axis]
    linear_combination (1+(ax:ℂ)*bx+(az:ℂ)*bz)/8*upper +
      (1+(ax:ℂ)*bx+(az:ℂ)*bz)/8*lower
  exact congrArg Complex.re h

theorem phi_from_fixed_family (point : BasePoint) (a b : Axis) (x y : Bool) :
    (vectorEvaluation (phiVector point) (outcomeEffect a b x y).matrix).re =
      probability a (heraldAxis true (colorXFrame b)) x y := by
  rw [outcomeEffect, phi_joint_probability]
  simp only [probability, Axis.signed, heraldAxis, if_true, Axis.reflected, colorXFrame]
  ring

theorem phi_from_original_runtime (point : BasePoint) (a b : Axis) (x y : Bool) :
    (vectorEvaluation (right 1 0 *ᵥ (right 0 1 *ᵥ Runtime.tick.answer point))
      (outcomeEffect a b x y).matrix).re =
      probability a (heraldAxis true (colorXFrame b)) x y := by
  rw [Runtime.tick_vector]
  exact phi_from_fixed_family point a b x y

structure DeterministicPreparationPrediction : Prop extends SameOccurrenceBellPrediction where
  phiNormalized : ∀ point, (∑ i, star (phiVector point i) * phiVector point i) = 1
  phiBorn : ∀ point a b x y,
    (vectorEvaluation (phiVector point) (outcomeEffect a b x y).matrix).re =
      probability a (heraldAxis true (colorXFrame b)) x y
  phiCurrent : ∀ point a b x y,
    (vectorEvaluation (right 1 0 *ᵥ (right 0 1 *ᵥ Runtime.tick.answer point))
      (outcomeEffect a b x y).matrix).re =
      probability a (heraldAxis true (colorXFrame b)) x y

theorem deterministicPreparationPrediction : DeterministicPreparationPrediction where
  toSameOccurrenceBellPrediction := sameOccurrenceBellPrediction
  phiNormalized := phiVector_normalized
  phiBorn := phi_from_fixed_family
  phiCurrent := phi_from_original_runtime

end
end SaturationMonoid.PhysicsCore.Stage10.Bell
