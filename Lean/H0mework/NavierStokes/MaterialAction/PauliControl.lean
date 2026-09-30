import H0mework.Physics.SpinPair.Dirac

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativePauliControl

open PhysicsCore PhysicsCore.Stage9C.Material.SpinPair

noncomputable section

abbrev Vector := Fin 3 → ℝ
abbrev Block := Matrix (Fin 2) (Fin 2) ℂ

def pauli : Fin 3 → Block
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

def hermitianBlock (velocity : Vector) : Block :=
  1 + ∑ direction, (velocity direction : ℂ) • pauli direction

def pauliExpansion (scalar : ℂ) (vector : Fin 3 → ℂ) : Block :=
  scalar • 1 + ∑ direction, vector direction • pauli direction

def spinPrincipal : Fin 4 → Block := ![1, pauli 0, pauli 1, pauli 2]

def coefficients (temporal rotation : Vector) (isotropic : ℝ) : Fin 4 → Fin 3 → ℝ :=
  !![temporal 0, temporal 1, temporal 2;
     isotropic, rotation 2 / 2, -(rotation 1 / 2);
     -(rotation 2 / 2), isotropic, rotation 0 / 2;
     rotation 1 / 2, -(rotation 0 / 2), isotropic]

/-- All twelve coefficients act on the original two occupied color states. -/
def action (velocity : Vector) (control : Fin 4 → Fin 3 → ℝ) : Block :=
  fun row column => ∑ spacetime, ∑ color, (control spacetime color : ℂ) *
    ∑ first : Fin 2, ∑ second : Fin 2,
      spinPrincipal spacetime row first * hermitianBlock velocity first second *
        (Complex.I * pauli color second column)

theorem action_normal_form (velocity temporal rotation : Vector) (isotropic : ℝ) :
    action velocity (coefficients temporal rotation isotropic) =
      pauliExpansion
        ((∑ direction, rotation direction * velocity direction : ℝ) +
          Complex.I * (((∑ direction, temporal direction * velocity direction) + 3 * isotropic : ℝ) : ℂ))
        (fun direction => (-(rotation direction) - (crossProduct velocity temporal) direction : ℝ) +
          Complex.I * ((temporal direction - isotropic * velocity direction : ℝ) : ℂ)) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    apply Complex.ext <;>
    simp [action, coefficients, spinPrincipal, hermitianBlock, pauliExpansion, pauli,
      Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two, cross_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

def realScalar (target : Block) : ℝ := (target 0 0 + target 1 1).re / 2
def imagScalar (target : Block) : ℝ := (target 0 0 + target 1 1).im / 2
def realVector (target : Block) : Vector :=
  ![(target 0 1 + target 1 0).re / 2,
    (Complex.I * (target 0 1 - target 1 0)).re / 2,
    (target 0 0 - target 1 1).re / 2]
def imagVector (target : Block) : Vector :=
  ![(target 0 1 + target 1 0).im / 2,
    (Complex.I * (target 0 1 - target 1 0)).im / 2,
    (target 0 0 - target 1 1).im / 2]

theorem target_expansion (target : Block) :
    target = pauliExpansion (realScalar target + Complex.I * imagScalar target)
      (fun direction => realVector target direction + Complex.I * imagVector target direction) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    apply Complex.ext <;>
    simp [pauliExpansion, realScalar, imagScalar, realVector, imagVector, pauli,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

def denominator (velocity : Vector) : ℝ := 3 + ∑ direction, velocity direction ^ 2

theorem denominator_pos (velocity : Vector) : 0 < denominator velocity := by
  unfold denominator
  have nonneg : 0 ≤ ∑ direction, velocity direction ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

def isotropic (velocity : Vector) (target : Block) : ℝ :=
  (imagScalar target - ∑ direction, velocity direction * imagVector target direction) / denominator velocity

def temporal (velocity : Vector) (target : Block) : Vector :=
  fun direction => imagVector target direction + isotropic velocity target * velocity direction

def rotation (velocity : Vector) (target : Block) : Vector :=
  fun direction => -(realVector target direction) - (crossProduct velocity (imagVector target)) direction

/-- The connection coefficients are computed from the complete requested matrix response. -/
def control (velocity : Vector) (target : Block) : Fin 4 → Fin 3 → ℝ :=
  coefficients (temporal velocity target) (rotation velocity target) (isotropic velocity target)

def phaseResidual (velocity : Vector) (target : Block) : ℝ :=
  realScalar target + ∑ direction, velocity direction * realVector target direction

theorem control_real_scalar (velocity : Vector) (target : Block) :
    (∑ direction, rotation velocity target direction * velocity direction) =
      -(∑ direction, velocity direction * realVector target direction) := by
  simp [rotation, Fin.sum_univ_three, cross_apply]
  ring

theorem control_real_vector (velocity : Vector) (target : Block) (direction : Fin 3) :
    -(rotation velocity target direction) - (crossProduct velocity (temporal velocity target)) direction =
      realVector target direction := by
  fin_cases direction <;> simp [rotation, temporal, cross_apply] <;> ring

theorem control_imag_scalar (velocity : Vector) (target : Block) :
    (∑ direction, temporal velocity target direction * velocity direction) + 3 * isotropic velocity target =
      imagScalar target := by
  have paid : isotropic velocity target * denominator velocity =
      imagScalar target - ∑ direction, velocity direction * imagVector target direction :=
    div_mul_cancel₀ _ (denominator_pos velocity).ne'
  simp only [temporal, denominator, Fin.sum_univ_three] at paid ⊢
  nlinarith

theorem control_imag_vector (velocity : Vector) (target : Block) (direction : Fin 3) :
    temporal velocity target direction - isotropic velocity target * velocity direction =
      imagVector target direction := by simp [temporal]

/-- The source color action realizes every response except its exact scalar phase obstruction. -/
theorem control_action (velocity : Vector) (target : Block) :
    action velocity (control velocity target) = target - (phaseResidual velocity target : ℂ) • 1 := by
  rw [control, action_normal_form, control_real_scalar, control_imag_scalar]
  simp only [control_real_vector, control_imag_vector]
  have scalar : ((-(∑ direction, velocity direction * realVector target direction) : ℝ) : ℂ) +
      Complex.I * imagScalar target =
      (realScalar target + Complex.I * imagScalar target) - (phaseResidual velocity target : ℂ) := by
    unfold phaseResidual
    push_cast
    ring
  rw [scalar]
  calc
    _ = pauliExpansion (realScalar target + Complex.I * imagScalar target)
        (fun direction => realVector target direction + Complex.I * imagVector target direction) -
        (phaseResidual velocity target : ℂ) • 1 := by
      unfold pauliExpansion
      module
    _ = _ := congrArg (fun matrix : Block => matrix - (phaseResidual velocity target : ℂ) • 1)
      (target_expansion target).symm

theorem phaseResidual_pairing (velocity : Vector) (target : Block) :
    2 * phaseResidual velocity target =
      (∑ row : Fin 2, ∑ column : Fin 2, star (hermitianBlock velocity row column) * target row column).re := by
  simp [phaseResidual, realScalar, realVector, hermitianBlock, pauli,
    Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  ring

end
end SaturationMonoid.NavierStokes.NativePauliControl
