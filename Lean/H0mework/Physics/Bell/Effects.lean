import H0mework.Physics.Bell.Operators

/-! Joint spectral projections are positive effects, including their complements. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

def axisProjector (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + (z : ℂ))/2, (x : ℂ)/2; (x : ℂ)/2, (1 - (z : ℂ))/2]

def spinProjector (x z : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(1 + (z : ℂ))/2, (x : ℂ)/2, 0, 0;
     (x : ℂ)/2, (1 - (z : ℂ))/2, 0, 0;
     0, 0, (1 + (z : ℂ))/2, (x : ℂ)/2;
     0, 0, (x : ℂ)/2, (1 - (z : ℂ))/2]

theorem axisProjector_hermitian (x z : ℝ) :
    (axisProjector x z).conjTranspose = axisProjector x z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [axisProjector, Matrix.conjTranspose_apply]

theorem spinProjector_hermitian (x z : ℝ) :
    (spinProjector x z).conjTranspose = spinProjector x z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinProjector, Matrix.conjTranspose_apply]

theorem axisProjector_square (x z : ℝ) (unit : x^2 + z^2 = 1) :
    axisProjector x z * axisProjector x z = axisProjector x z := by
  have h : (x : ℂ)^2 + (z : ℂ)^2 = 1 := by exact_mod_cast unit
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisProjector, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | (solve | ring) | linear_combination h / 4

theorem spinProjector_square (x z : ℝ) (unit : x^2 + z^2 = 1) :
    spinProjector x z * spinProjector x z = spinProjector x z := by
  have h : (x : ℂ)^2 + (z : ℂ)^2 = 1 := by exact_mod_cast unit
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinProjector, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | (solve | ring) | linear_combination h / 4

def projectorEffect (P : Observable) (hermitian : P.conjTranspose = P)
    (square : P * P = P) : Effect where
  matrix := P
  positive := by
    have positive := Matrix.posSemidef_self_mul_conjTranspose P
    rwa [hermitian, square] at positive
  complement_positive := by
    have factor : (1 - P) * (1 - P).conjTranspose = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hermitian,
        sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_one, square]
      abel
    rw [← factor]
    exact Matrix.posSemidef_self_mul_conjTranspose _

def jointEffect (ax az bx bz : ℝ) (aunit : ax^2 + az^2 = 1)
    (bunit : bx^2 + bz^2 = 1) : Effect :=
  projectorEffect (spinProjector ax az ⊗ₖ axisProjector bx bz)
    (by rw [Matrix.conjTranspose_kronecker, spinProjector_hermitian,
      axisProjector_hermitian])
    (by rw [← Matrix.mul_kronecker_mul, spinProjector_square ax az aunit,
      axisProjector_square bx bz bunit])


end
end SaturationMonoid.PhysicsCore.Stage10.Bell
