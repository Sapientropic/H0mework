import H0mework.NavierStokes.MaterialJets.Color

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeBalancedJetCoefficients

open NativePauliControl NativePauliMotherAction NativeCartanConstitutive NativeBalancedColorControl

noncomputable section

def curl (derivative : Fin 4 → Vector) : Vector :=
  ![derivative 2 2 - derivative 3 1, derivative 3 0 - derivative 1 2, derivative 1 1 - derivative 2 0]

def pairing (first second : Vector) : ℝ := ∑ index, first index * second index

def temporalProjection (velocity tangent : Vector) : Vector :=
  fun index => tangent index - pairing velocity tangent / weight velocity * velocity index

def helicityCoefficient (velocity : Vector) (derivative : Fin 4 → Vector) : ℝ :=
  4 * pairing velocity (curl derivative) / denominator velocity

private theorem log_temporal (velocity : Vector) (derivative : Fin 4 → Vector) :
    3 / 2 * NativePauliJet.logDerivative velocity derivative 0 = pairing velocity (derivative 0) / weight velocity := by
  change 3 / 2 * (4 * pairing velocity (derivative 0) / (3 * (2 * weight velocity))) = _
  field_simp [(weight_pos velocity).ne']
  ring

theorem target_scalar (velocity : Vector) (derivative : Fin 4 → Vector) :
    imagScalar (-NativePauliJet.freeResponse velocity derivative) = 0 := by
  simp [imagScalar, NativePauliJet.freeResponse, NativePauliJet.tangent, hermitianBlock,
    spinAction, spinPrincipal, pauli, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  ring

theorem target_real (velocity : Vector) (derivative : Fin 4 → Vector) (index : Fin 3) :
    realVector (-NativePauliJet.freeResponse velocity derivative) index =
      -temporalProjection velocity (derivative 0) index := by
  have reduce : realVector (-NativePauliJet.freeResponse velocity derivative) index =
      -derivative 0 index + 3 / 2 * NativePauliJet.logDerivative velocity derivative 0 * velocity index := by
    fin_cases index <;>
      simp [realVector, NativePauliJet.freeResponse, NativePauliJet.tangent, hermitianBlock,
        spinAction, spinPrincipal, pauli, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring
  rw [reduce, log_temporal]
  simp [temporalProjection]
  ring

theorem target_imaginary (velocity : Vector) (derivative : Fin 4 → Vector) (index : Fin 3) :
    imagVector (-NativePauliJet.freeResponse velocity derivative) index = -2 * weight velocity * curl derivative index := by
  have reduce : imagVector (-NativePauliJet.freeResponse velocity derivative) index =
      -NativePauliJet.density velocity * curl derivative index := by
    fin_cases index <;>
      simp [imagVector, NativePauliJet.freeResponse, NativePauliJet.tangent, hermitianBlock,
        spinAction, spinPrincipal, pauli, curl, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring
  rw [reduce]
  simp only [NativePauliJet.density, weight, squared]
  ring

def coefficients (velocity : Vector) (derivative : Fin 4 → Vector) : Fin 4 → Fin 3 → ℝ :=
  let w := curl derivative
  let q := temporalProjection velocity (derivative 0)
  let e := helicityCoefficient velocity derivative
  !![-2 * w 0 + e * velocity 0, -2 * w 1 + e * velocity 1, -2 * w 2 + e * velocity 2;
     e - 2 * w 0 * velocity 0, q 2 / 2 - 2 * w 0 * velocity 1, -q 1 / 2 - 2 * w 0 * velocity 2;
     -q 2 / 2 - 2 * w 1 * velocity 0, e - 2 * w 1 * velocity 1, q 0 / 2 - 2 * w 1 * velocity 2;
     q 1 / 2 - 2 * w 2 * velocity 0, -q 0 / 2 - 2 * w 2 * velocity 1, e - 2 * w 2 * velocity 2]

/-- The complete original response is realized with one velocity factor in the spatial curl coefficients. -/
theorem coefficients_eq_control (velocity : Vector) (derivative : Fin 4 → Vector) :
    coefficients velocity derivative = NativeBalancedColorControl.control velocity (-NativePauliJet.freeResponse velocity derivative) := by
  ext direction color
  change coefficients velocity derivative direction color =
    NativePauliControl.coefficients
      (NativeBalancedColorControl.temporal velocity (-NativePauliJet.freeResponse velocity derivative))
      (NativeBalancedColorControl.rotation velocity (-NativePauliJet.freeResponse velocity derivative))
      (NativeBalancedColorControl.isotropic velocity (-NativePauliJet.freeResponse velocity derivative)) direction color +
    (![0, NativeBalancedColorControl.symmetric velocity (-NativePauliJet.freeResponse velocity derivative) 0,
      NativeBalancedColorControl.symmetric velocity (-NativePauliJet.freeResponse velocity derivative) 1,
      NativeBalancedColorControl.symmetric velocity (-NativePauliJet.freeResponse velocity derivative) 2] :
        Fin 4 → Fin 3 → ℝ) direction color
  fin_cases direction <;> fin_cases color <;>
    simp [coefficients, NativePauliControl.coefficients,
      NativeBalancedColorControl.temporal, NativeBalancedColorControl.rotation,
      NativeBalancedColorControl.isotropic, NativeBalancedColorControl.symmetric,
      target_scalar, target_real, target_imaginary,
      helicityCoefficient, pairing, cross_apply, Fin.sum_univ_three]
  all_goals field_simp [(weight_pos velocity).ne', (denominator_pos velocity).ne']
  all_goals ring

theorem temporalProjection_energy (velocity tangent : Vector) :
    squared (temporalProjection velocity tangent) = squared tangent -
      (2 + squared velocity) / weight velocity ^ 2 * pairing velocity tangent ^ 2 := by
  simp only [squared, temporalProjection, pairing, Fin.sum_univ_three]
  field_simp [(weight_pos velocity).ne']
  simp only [weight, squared, Fin.sum_univ_three]
  ring

theorem temporalProjection_bound (velocity tangent : Vector) :
    squared (temporalProjection velocity tangent) ≤ squared tangent := by
  rw [temporalProjection_energy]
  have nonnegative : 0 ≤ squared velocity := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have payment : 0 ≤ (2 + squared velocity) / weight velocity ^ 2 * pairing velocity tangent ^ 2 := by positivity
  linarith

theorem temporal_energy (velocity : Vector) (derivative : Fin 4 → Vector) :
    (∑ color, coefficients velocity derivative 0 color ^ 2) = 4 * squared (curl derivative) -
      48 * pairing velocity (curl derivative)^2 / denominator velocity ^ 2 := by
  simp only [coefficients, Fin.sum_univ_three]
  simp [helicityCoefficient, squared, pairing, denominator, Fin.sum_univ_three]
  field_simp
  ring

theorem temporal_bound (velocity : Vector) (derivative : Fin 4 → Vector) :
    (∑ color, coefficients velocity derivative 0 color ^ 2) ≤ 4 * squared (curl derivative) := by
  rw [temporal_energy]
  have payment : 0 ≤ 48 * pairing velocity (curl derivative)^2 / denominator velocity ^ 2 := by positivity
  linarith

theorem spatial_energy (velocity : Vector) (derivative : Fin 4 → Vector) :
    (∑ direction : Fin 3, ∑ color, coefficients velocity derivative direction.succ color ^ 2) =
      squared (temporalProjection velocity (derivative 0)) / 2 +
        4 * squared velocity * squared (curl derivative) +
        2 * pairing (temporalProjection velocity (derivative 0)) (crossProduct velocity (curl derivative)) -
        16 * squared velocity * pairing velocity (curl derivative)^2 / denominator velocity ^ 2 := by
  simp [coefficients, helicityCoefficient, squared, pairing, cross_apply, Fin.sum_univ_three]
  field_simp [(denominator_pos velocity).ne']
  simp only [denominator, Fin.sum_univ_three]
  ring

private theorem cross_pairing_bound (velocity first second : Vector) :
    2 * pairing first (crossProduct velocity second) ≤ squared first + squared velocity * squared second := by
  have nonnegative : 0 ≤ squared (first - crossProduct velocity second) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have expansion : squared (first - crossProduct velocity second) = squared first -
      2 * pairing first (crossProduct velocity second) + squared velocity * squared second - pairing velocity second ^ 2 := by
    simp [squared, pairing, cross_apply, Fin.sum_univ_three]
    ring
  rw [expansion] at nonnegative
  nlinarith [sq_nonneg (pairing velocity second)]

theorem spatial_bound (velocity : Vector) (derivative : Fin 4 → Vector) :
    (∑ direction : Fin 3, ∑ color, coefficients velocity derivative direction.succ color ^ 2) ≤
      3 / 2 * squared (derivative 0) + 5 * squared velocity * squared (curl derivative) := by
  rw [spatial_energy]
  have nonnegative : 0 ≤ squared velocity := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have payment : 0 ≤ 16 * squared velocity * pairing velocity (curl derivative)^2 / denominator velocity ^ 2 := by positivity
  have cross := cross_pairing_bound velocity (temporalProjection velocity (derivative 0)) (curl derivative)
  have projection := temporalProjection_bound velocity (derivative 0)
  linarith

theorem response_eq_original (velocity : Vector) (derivative : Fin 4 → Vector) :
    action velocity (coefficients velocity derivative) =
      action velocity (NativePauliControl.control velocity (-NativePauliJet.freeResponse velocity derivative)) := by
  rw [coefficients_eq_control, NativeBalancedColorControl.control_action, NativePauliControl.control_action]

end
end SaturationMonoid.NavierStokes.NativeBalancedJetCoefficients
