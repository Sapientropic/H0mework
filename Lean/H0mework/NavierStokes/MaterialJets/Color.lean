import H0mework.NavierStokes.ConstitutiveAction.Occurrence

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeBalancedColorControl

open NativePauliControl NativePauliMotherAction NativeCartanConstitutive

noncomputable section

def weight (velocity : Vector) : ℝ := 1 + squared velocity

theorem weight_pos (velocity : Vector) : 0 < weight velocity := by
  have nonnegative : 0 ≤ squared velocity := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold weight
  positivity

def isotropic (velocity : Vector) (response : Block) : ℝ :=
  imagScalar response / denominator velocity -
    2 * (∑ index, velocity index * imagVector response index) / (weight velocity * denominator velocity)

def temporal (velocity : Vector) (response : Block) : Vector :=
  fun index => imagVector response index / weight velocity + isotropic velocity response * velocity index

def rotation (velocity : Vector) (response : Block) : Vector :=
  fun index => -realVector response index - (crossProduct velocity (imagVector response)) index / weight velocity

def symmetric (velocity : Vector) (response : Block) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun first second =>
    (velocity first * imagVector response second + imagVector response first * velocity second) / (2 * weight velocity)

def control (velocity : Vector) (response : Block) : Fin 4 → Fin 3 → ℝ :=
  NativePauliControl.coefficients (temporal velocity response) (rotation velocity response) (isotropic velocity response) +
    ![0, symmetric velocity response 0, symmetric velocity response 1, symmetric velocity response 2]

private theorem symmetric_action (velocity : Vector) (symmetric : Matrix (Fin 3) (Fin 3) ℝ)
    (self : symmetric.transpose = symmetric) :
    action velocity ![0, symmetric 0, symmetric 1, symmetric 2] =
      pauliExpansion (Complex.I * ((Matrix.trace symmetric : ℝ) : ℂ))
        (fun index => Complex.I * ((2 * (∑ other, symmetric index other * velocity other) -
          Matrix.trace symmetric * velocity index : ℝ) : ℂ)) := by
  have off (first second : Fin 3) : symmetric first second = symmetric second first := by
    exact (congrArg (fun matrix => matrix second first) self)
  ext row column
  fin_cases row <;> fin_cases column <;> apply Complex.ext <;>
    simp [action, spinPrincipal, hermitianBlock, pauliExpansion, pauli, Matrix.trace,
      Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im,
      off 1 0, off 2 0, off 2 1] <;> ring

private theorem action_add (velocity : Vector) (first second : Fin 4 → Fin 3 → ℝ) :
    action velocity (first + second) = action velocity first + action velocity second := by
  ext row column
  simp [action, add_mul, Finset.sum_add_distrib]

private theorem symmetric_trace (velocity : Vector) (response : Block) :
    Matrix.trace (symmetric velocity response) =
      (∑ index, velocity index * imagVector response index) / weight velocity := by
  simp [Matrix.trace, symmetric, Fin.sum_univ_three]
  ring

private theorem symmetric_product (velocity : Vector) (response : Block) (index : Fin 3) :
    (∑ other, symmetric velocity response index other * velocity other) =
      (velocity index * (∑ other, velocity other * imagVector response other) +
        imagVector response index * squared velocity) / (2 * weight velocity) := by
  simp [symmetric, squared, Fin.sum_univ_three]
  ring

private theorem rotation_dot (velocity : Vector) (response : Block) :
    (∑ index, rotation velocity response index * velocity index) =
      -(∑ index, velocity index * realVector response index) := by
  simp [rotation, Fin.sum_univ_three, cross_apply]
  ring

private theorem real_response (velocity : Vector) (response : Block) (index : Fin 3) :
    -rotation velocity response index - crossProduct velocity (temporal velocity response) index =
      realVector response index := by
  fin_cases index <;> simp [rotation, temporal, cross_apply] <;> ring

private theorem imaginary_scalar (velocity : Vector) (response : Block) :
    (∑ index, temporal velocity response index * velocity index) + 3 * isotropic velocity response +
      Matrix.trace (symmetric velocity response) = imagScalar response := by
  rw [symmetric_trace]
  simp only [temporal, isotropic, Fin.sum_univ_three]
  field_simp [(weight_pos velocity).ne', (denominator_pos velocity).ne']
  simp only [weight, squared, denominator, Fin.sum_univ_three]
  ring

private theorem imaginary_vector (velocity : Vector) (response : Block) (index : Fin 3) :
    temporal velocity response index - isotropic velocity response * velocity index +
      (2 * (∑ other, symmetric velocity response index other * velocity other) -
        Matrix.trace (symmetric velocity response) * velocity index) = imagVector response index := by
  rw [symmetric_trace, symmetric_product]
  simp only [temporal]
  field_simp [(weight_pos velocity).ne']
  simp only [weight]
  ring

private theorem expansion_add (first second : ℂ) (left right : Fin 3 → ℂ) :
    pauliExpansion first left + pauliExpansion second right = pauliExpansion (first + second) (left + right) := by
  simp only [pauliExpansion, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  module

theorem control_action (velocity : Vector) (response : Block) :
    action velocity (control velocity response) = response - (phaseResidual velocity response : ℂ) • 1 := by
  have symmetric_self : (symmetric velocity response).transpose = symmetric velocity response := by
    ext first second
    simp only [symmetric, Matrix.transpose_apply]
    ring
  rw [control, action_add, action_normal_form, symmetric_action velocity _ symmetric_self, expansion_add]
  rw [← NativePauliControl.control_action velocity response, NativePauliControl.control,
    action_normal_form, NativePauliControl.control_real_scalar, NativePauliControl.control_imag_scalar]
  simp only [NativePauliControl.control_real_vector, NativePauliControl.control_imag_vector]
  congr 1
  · rw [rotation_dot, ← imaginary_scalar velocity response]
    push_cast
    ring
  · funext index
    simp only [Pi.add_apply, real_response]
    rw [← imaginary_vector velocity response index]
    push_cast
    ring

end
end SaturationMonoid.NavierStokes.NativeBalancedColorControl
