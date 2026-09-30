import H0mework.Physics.Dirac.PointwiseDiracSpinConnectionLift

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeDiagonalCoframe

open PhysicsCore PointwiseLorentzianCoframeJet

noncomputable section

def jet (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ) :
    PointwiseLorentzianCoframeJet where
  coframe := Matrix.diagonal coefficient
  derivative := fun direction => Matrix.diagonal (derivative direction)

theorem sign_square (index : Fin 4) : minkowskiInternalSign index ^ 2 = 1 := by
  simp [minkowskiInternalSign]

theorem sign_nonzero (index : Fin 4) : minkowskiInternalSign index ≠ 0 := by
  unfold minkowskiInternalSign
  split_ifs <;> norm_num

theorem metric_diagonal (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ) :
    (jet coefficient derivative).metric =
      Matrix.diagonal (fun index => minkowskiInternalSign index * coefficient index ^ 2) := by
  simp only [metric, jet, lorentzianMetricOfCoframe, Matrix.diagonal_transpose,
    minkowskiInternalMetric_eq_diagonal_sign, Matrix.diagonal_mul_diagonal]
  congr 1
  funext index
  ring

theorem metric_inverse (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ)
    (nonzero : ∀ index, coefficient index ≠ 0) :
    (jet coefficient derivative).metric⁻¹ =
      Matrix.diagonal (fun index => (minkowskiInternalSign index * coefficient index ^ 2)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [metric_diagonal, Matrix.diagonal_mul_diagonal]
  have cancel : (fun index => (minkowskiInternalSign index * coefficient index ^ 2) *
      (minkowskiInternalSign index * coefficient index ^ 2)⁻¹) = fun _ => 1 := by
    funext index
    exact mul_inv_cancel₀ (mul_ne_zero (sign_nonzero index) (pow_ne_zero 2 (nonzero index)))
  rw [cancel]
  rfl

theorem metric_derivative (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ)
    (direction first second : Fin 4) :
    (jet coefficient derivative).metricDerivative direction first second =
      if first = second then 2 * minkowskiInternalSign first * coefficient first * derivative direction first
      else 0 := by
  classical
  unfold metricDerivative
  calc
    _ = ∑ index : Fin 4, if index = first then
        (if first = second then 2 * minkowskiInternalSign first * coefficient first * derivative direction first
        else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases a : index = first <;> by_cases b : first = second <;> subst_vars <;>
        simp_all [jet, Matrix.diagonal_apply]
      ring
    _ = _ := by simp

def spinConnection (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ) :
    PointwiseLorentzSpinConnection := fun direction first second =>
  (if direction = first then derivative second first / coefficient second else 0) -
    (if direction = second then minkowskiInternalSign first * minkowskiInternalSign second *
      derivative first second / coefficient first else 0)

theorem affine_connection (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ)
    (nonzero : ∀ index, coefficient index ≠ 0)
    (upper direction lower : Fin 4) :
    (jet coefficient derivative).leviCivitaConnection upper direction lower =
      (minkowskiInternalSign upper * coefficient upper ^ 2)⁻¹ *
        (((if lower = upper then 2 * minkowskiInternalSign lower * coefficient lower * derivative direction lower else 0) +
          (if direction = upper then 2 * minkowskiInternalSign direction * coefficient direction * derivative lower direction else 0) -
          (if direction = lower then 2 * minkowskiInternalSign direction * coefficient direction * derivative upper direction else 0)) / 2) := by
  simp only [leviCivitaConnection, leviCivitaConnectionVector, metric_inverse coefficient derivative nonzero,
    Matrix.mulVec_diagonal, loweredLeviCivitaVector, loweredLeviCivitaConnection, metric_derivative]

theorem spin_connection (coefficient : Fin 4 → ℝ) (derivative : Fin 4 → Fin 4 → ℝ)
    (nonzero : ∀ index, coefficient index ≠ 0) :
    (jet coefficient derivative).lorentzSpinConnection = spinConnection coefficient derivative := by
  funext direction first second
  have coframe_inverse : (jet coefficient derivative).coframe⁻¹ =
      Matrix.diagonal (fun index => (coefficient index)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp [jet, Matrix.diagonal_mul_diagonal, nonzero]
  simp only [lorentzSpinConnection, lorentzSpinConnectionMatrix,
    coordinateConnectionMatrix, affineConnectionMatrix, coframeDerivativeMatrix, coframe_inverse]
  simp only [jet, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.of_apply]
  change (coefficient first * (jet coefficient derivative).leviCivitaConnection first direction second -
    Matrix.diagonal (derivative direction) first second) * (coefficient second)⁻¹ = _
  rw [affine_connection coefficient derivative nonzero]
  simp only [spinConnection, Matrix.diagonal_apply]
  split_ifs <;> subst_vars <;> try contradiction
  all_goals field_simp [nonzero, sign_nonzero]
  all_goals ring_nf
  all_goals simp only [sign_square, mul_one, sub_self]

end
end SaturationMonoid.NavierStokes.NativeDiagonalCoframe
