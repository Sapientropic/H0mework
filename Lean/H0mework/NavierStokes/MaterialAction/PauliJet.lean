import H0mework.NavierStokes.MaterialAction.MotherAction

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativePauliJet

open NativePauliControl NativePauliMotherAction

noncomputable section

def density (velocity : Vector) : ℝ := 2 * (1 + ∑ direction, velocity direction ^ 2)

theorem density_pos (velocity : Vector) : 0 < density velocity := by
  unfold density
  have nonnegative : 0 ≤ ∑ direction, velocity direction ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

def tangent (derivative : Vector) : Block :=
  ∑ direction, (derivative direction : ℂ) • pauli direction

def logDerivative (velocity : Vector) (derivative : Fin 4 → Vector) (direction : Fin 4) : ℝ :=
  4 * (∑ component, velocity component * derivative direction component) / (3 * density velocity)

/-- The source coframe's complete normalized free Dirac response, including its spin contraction. -/
def freeResponse (velocity : Vector) (derivative : Fin 4 → Vector) : Block :=
  tangent (derivative 0) - (((3 / 2 : ℝ) * logDerivative velocity derivative 0 : ℝ) : ℂ) • hermitianBlock velocity +
    (density velocity : ℂ) • ∑ direction : Fin 3, spinAction (tangent (derivative direction.succ)) direction.succ

theorem phase_add (velocity : Vector) (first second : Block) :
    phaseResidual velocity (first + second) = phaseResidual velocity first + phaseResidual velocity second := by
  simp [phaseResidual, realScalar, realVector, Fin.sum_univ_three, Complex.mul_re]
  ring

theorem phase_smul (velocity : Vector) (scalar : ℝ) (target : Block) :
    phaseResidual velocity ((scalar : ℂ) • target) = scalar * phaseResidual velocity target := by
  simp [phaseResidual, realScalar, realVector, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  ring

theorem phase_sub (velocity : Vector) (first second : Block) :
    phaseResidual velocity (first - second) = phaseResidual velocity first - phaseResidual velocity second := by
  rw [sub_eq_add_neg, show -second = ((-1 : ℝ) : ℂ) • second by simp, phase_add, phase_smul]
  ring

theorem phase_tangent (velocity derivative : Vector) :
    phaseResidual velocity (tangent derivative) = ∑ direction, velocity direction * derivative direction := by
  simp [phaseResidual, realScalar, realVector, tangent, pauli, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]

theorem phase_matter (velocity : Vector) :
    phaseResidual velocity (hermitianBlock velocity) = density velocity / 2 := by
  simp [phaseResidual, realScalar, realVector, hermitianBlock, pauli, density, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im]
  ring

theorem phase_spatial (velocity derivative : Vector) (direction : Fin 3) :
    phaseResidual velocity (spinAction (tangent derivative) direction.succ) = derivative direction := by
  fin_cases direction <;>
    simp [phaseResidual, realScalar, realVector, spinAction, spinPrincipal, tangent, pauli,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]

theorem freeResponse_phase (velocity : Vector) (derivative : Fin 4 → Vector) :
    phaseResidual velocity (freeResponse velocity derivative) =
      density velocity * ∑ direction : Fin 3, derivative direction.succ direction := by
  simp only [freeResponse, phase_add, phase_sub, phase_smul, phase_tangent, phase_matter]
  simp only [Fin.sum_univ_three, phase_add, phase_spatial]
  simp only [logDerivative, Fin.sum_univ_three]
  field_simp [(density_pos velocity).ne']
  ring

/-- The explicit original color connection cancels the entire free response except the actual divergence. -/
theorem controlled_response (velocity : Vector) (derivative : Fin 4 → Vector) :
    lowerMatter (freeResponse velocity derivative) +
      wholeAction velocity (control velocity (-freeResponse velocity derivative)) =
      (density velocity * ∑ direction : Fin 3, derivative direction.succ direction : ℂ) • lowerMatter 1 := by
  rw [controlled_wholeAction, map_neg,
    show -freeResponse velocity derivative = ((-1 : ℝ) : ℂ) • freeResponse velocity derivative by simp,
    phase_smul, freeResponse_phase]
  push_cast
  module

end
end SaturationMonoid.NavierStokes.NativePauliJet
