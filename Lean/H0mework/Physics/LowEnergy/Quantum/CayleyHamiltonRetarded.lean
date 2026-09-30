import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic

/-! The actual characteristic polynomial generates a two-sided resolvent.
Synthetic division supplies its finite Horner numerator; no inverse or
vanishing matrix polynomial is an input. The pole exclusion is explicit. -/
set_option autoImplicit false
namespace SourceCayleyHamiltonRetarded
open Polynomial
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "Mat" => Matrix ι ι ℂ

def numerator (A : Mat) (z : ℂ) : Mat :=
  aeval A (A.charpoly /ₘ (X - C z))

theorem left_numerator (A : Mat) (z : ℂ) :
    (algebraMap ℂ Mat z - A) * numerator A z = algebraMap ℂ Mat (A.charpoly.eval z) := by
  have h := congrArg (aeval A) (modByMonic_add_div A.charpoly (X - C z))
  simp only [modByMonic_X_sub_C_eq_C_eval, map_add, map_mul, map_sub,
    aeval_C, aeval_X, Matrix.aeval_self_charpoly] at h
  change (algebraMap ℂ Mat z - A) * aeval A (A.charpoly /ₘ (X - C z)) = _
  rw [← neg_sub A (algebraMap ℂ Mat z), neg_mul]
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem right_numerator (A : Mat) (z : ℂ) :
    numerator A z * (algebraMap ℂ Mat z - A) = algebraMap ℂ Mat (A.charpoly.eval z) := by
  have h := congrArg (aeval A) (mul_comm (X - C z) (A.charpoly /ₘ (X - C z)))
  simp only [map_mul, map_sub, aeval_X, aeval_C] at h
  change aeval A (A.charpoly /ₘ (X - C z)) * (algebraMap ℂ Mat z - A) = _
  calc
    _ = -(aeval A (A.charpoly /ₘ (X - C z)) * (A - algebraMap ℂ Mat z)) := by
      rw [← mul_neg, neg_sub]
    _ = -((A - algebraMap ℂ Mat z) * aeval A (A.charpoly /ₘ (X - C z))) := congrArg Neg.neg h.symm
    _ = (algebraMap ℂ Mat z - A) * numerator A z := by rw [← neg_mul, neg_sub]; rfl
    _ = _ := left_numerator A z

def resolvent (A : Mat) (z : ℂ) : Mat := (A.charpoly.eval z)⁻¹ • numerator A z

theorem both_inverse_products (A : Mat) (z : ℂ) (off_pole : A.charpoly.eval z ≠ 0) :
    (algebraMap ℂ Mat z - A) * resolvent A z = 1 ∧
      resolvent A z * (algebraMap ℂ Mat z - A) = 1 := by
  constructor
  · rw [resolvent, mul_smul_comm, left_numerator, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ off_pole, one_smul]
  · rw [resolvent, smul_mul_assoc, right_numerator, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ off_pole, one_smul]

#print axioms left_numerator
#print axioms right_numerator
#print axioms both_inverse_products
end
end SourceCayleyHamiltonRetarded
