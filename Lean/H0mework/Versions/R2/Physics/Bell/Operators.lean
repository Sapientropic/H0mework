import H0mework.Versions.R2.Physics.QuantumState.StateSource
import H0mework.Versions.R2.Physics.QuantumState.AlgebraSourceAction
import H0mework.Physics.SpinPair.Dirac
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Commuting spin and color measurements on the complete occupied source carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell

open Matrix Stage9DEF State
open Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource
open scoped Kronecker ComplexOrder

noncomputable section

def axis (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(z : ℂ), (x : ℂ); (x : ℂ), -(z : ℂ)]

def spinAxis (x z : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(z : ℂ), (x : ℂ), 0, 0;
     (x : ℂ), -(z : ℂ), 0, 0;
     0, 0, (z : ℂ), (x : ℂ);
     0, 0, (x : ℂ), -(z : ℂ)]

def left (x z : ℝ) : Observable := spinAxis x z ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
def right (x z : ℝ) : Observable := (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ axis x z

theorem joint_mul (ax az bx bz : ℝ) :
    left ax az * right bx bz = spinAxis ax az ⊗ₖ axis bx bz := by
  rw [left, right, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem joint_commutes (ax az bx bz : ℝ) :
    left ax az * right bx bz = right bx bz * left ax az := by
  rw [joint_mul, right, left, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem joint_expectation (ax az bx bz : ℝ) :
    evaluation 0 (left ax az * right bx bz) = -(ax * bx + az * bz : ℝ) := by
  rw [joint_mul]
  simp [evaluation, vectorEvaluation, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Source.vector_zero, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two, spinAxis, axis]
  ring

theorem left_expectation (ax az : ℝ) : evaluation 0 (left ax az) = 0 := by
  simp [evaluation, vectorEvaluation, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Source.vector_zero, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two, left, spinAxis]
  ring

theorem right_expectation (bx bz : ℝ) : evaluation 0 (right bx bz) = 0 := by
  simp [evaluation, vectorEvaluation, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Source.vector_zero, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two, right, axis]
  ring


theorem right_from_mother (x z : ℝ) :
    right x z = (-2 * Complex.I) •
      ((x : ℂ) • Algebra.colorAction 0 + (z : ℂ) • Algebra.colorAction 2) := by
  ext row column
  rcases row with ⟨spin, color⟩
  rcases column with ⟨other, second⟩
  by_cases same : spin = other
  · subst other
    fin_cases color <;> fin_cases second <;>
      simp [right, axis, Algebra.colorAction, sourceColorPauli]
    all_goals ring_nf; simp
  · simp [right, Algebra.colorAction, same]

theorem spinAxis_from_clifford (x z : ℝ) :
    spinAxis x z = (-Complex.I) •
      ((x : ℂ) • spinRotation 0 + (z : ℂ) • spinRotation 2) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spinAxis, spinRotation, DiracCliffordRepresentation.diracGamma,
      DiracCliffordRepresentation.diracGammaOne,
      DiracCliffordRepresentation.diracGammaTwo,
      DiracCliffordRepresentation.diracGammaThree,
      ]
  all_goals ring_nf; simp


end
end SaturationMonoid.PhysicsCore.Stage10.Bell
