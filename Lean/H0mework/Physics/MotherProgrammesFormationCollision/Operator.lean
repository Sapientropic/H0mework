import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import H0mework.Physics.MotherProgrammesFormation.Dyadic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContactCollision

open Matrix

noncomputable section

/-- The actual complement exchanges the two channels. -/
def J : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def primitive : Circle := ⟨J 0 0 - J 0 1, by
  apply mem_sphere_zero_iff_norm.mpr
  norm_num [J]⟩

theorem primitive_eq : primitive = -1 := by
  apply Circle.ext
  norm_num [primitive, J]

theorem primitive_involution : primitive ^ 2 = 1 := by
  apply Circle.ext
  norm_num [primitive_eq]

theorem primitive_effective : primitive ≠ 1 := by
  intro same
  have values := congrArg (fun phase : Circle => (phase : ℂ)) same
  norm_num [primitive_eq] at values

def rootPhase : Circle := DyadicFormation.step primitive

theorem rootPhase_coe : (rootPhase : ℂ) = Complex.I := by
  rw [rootPhase, DyadicFormation.step, primitive_eq]
  simp [Circle.coe_exp, Complex.exp_mul_I]

def Pplus : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (1 + J)
def Pminus : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (1 - J)

/-- The contrast phase is generated from this same complement action. -/
def R : Matrix (Fin 2) (Fin 2) ℂ := Pplus + (rootPhase : ℂ) • Pminus

theorem R_formula : R = Pplus + Complex.I • Pminus := by rw [R, rootPhase_coe]

def a : ℂ := R 0 0
def b : ℂ := R 1 0

theorem a_eq : a = (1 + Complex.I) / 2 := by
  norm_num [a, R_formula, Pplus, Pminus, J, Matrix.one_apply, smul_eq_mul]
  ring

theorem b_eq : b = (1 - Complex.I) / 2 := by
  norm_num [b, R_formula, Pplus, Pminus, J, Matrix.one_apply, smul_eq_mul]
  ring

theorem R_matrix : R = !![a, b; b, a] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [a, b, R_formula, Pplus, Pminus, J]

theorem R_apply (x y : ℂ) :
    R *ᵥ ![x, y] = ![a * x + b * y, b * x + a * y] := by
  rw [R_matrix]
  ext index
  fin_cases index <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem R_square : R * R = J := by
  rw [R_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [J, Matrix.mul_apply, Fin.sum_univ_two, a_eq, b_eq,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

theorem R_unitary : R ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, R_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      a_eq, b_eq, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

def operator : Matrix.unitaryGroup (Fin 2) ℂ := ⟨R, R_unitary⟩

theorem normSq_a : Complex.normSq a = (1 / 2 : ℝ) := by
  norm_num [a_eq, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem normSq_b : Complex.normSq b = (1 / 2 : ℝ) := by
  norm_num [b_eq, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem cross_cancel : star a * b + star b * a = 0 := by
  norm_num [a_eq, b_eq, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im]

theorem energy_preserved (x y : ℂ) :
    Complex.normSq (a * x + b * y) + Complex.normSq (b * x + a * y) =
      Complex.normSq x + Complex.normSq y := by
  norm_num [a_eq, b_eq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  ring

/-- This phase is extracted from the same operator's contrast action. -/
def contrastPhase : ℂ := a - b

theorem contrastPhase_eq : contrastPhase = Complex.I := by
  rw [contrastPhase, a_eq, b_eq]
  ring

theorem contrast_action (x : ℂ) :
    R *ᵥ ![x, -x] = contrastPhase • ![x, -x] := by
  rw [R_apply]
  ext index
  fin_cases index <;> simp [contrastPhase] <;> ring

theorem primitive_action (x : ℂ) : J *ᵥ ![x, -x] = (-1 : ℂ) • ![x, -x] := by
  ext index
  fin_cases index <;> simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem contrastPhase_square : contrastPhase ^ 2 = -1 := by
  rw [contrastPhase_eq, Complex.I_sq]

theorem contrastPhase_effective : contrastPhase ^ 2 ≠ 1 := by
  rw [contrastPhase_square]
  norm_num

theorem phase_same_origin : contrastPhase = (rootPhase : ℂ) ∧
    contrastPhase ^ 2 = (primitive : ℂ) := by
  rw [contrastPhase_eq, rootPhase_coe, Complex.I_sq, primitive_eq]
  exact ⟨rfl, rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContactCollision
