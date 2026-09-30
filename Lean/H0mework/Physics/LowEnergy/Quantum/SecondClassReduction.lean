import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The scalar-normal / broken-Gauss constraint matrix and its generated Dirac inverse.
The original source instance supplies `D` and its inverse; the Gauss-Gauss block `K`
is retained.  In `source_full_gauss_section.py`, `D` is the original nine-dimensional
constraint Jacobian.  This algebra does not reinterpret the broken directions as
first-class gauge symmetries.
-/

namespace LowEnergy.SecondClassReduction

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def constraintMatrix (D K : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  fromBlocks 0 D (-Dᵀ) K

def diracInverse (I K : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  fromBlocks (Iᵀ * K * I) (-Iᵀ) I 0

theorem constraint_mul_inverse (D I K : Matrix ι ι R)
    (hDI : D * I = 1) (hID : I * D = 1) :
    constraintMatrix D K * diracInverse I K = 1 := by
  have hT : Dᵀ * Iᵀ = 1 := by rw [← transpose_mul, hID, transpose_one]
  simp only [constraintMatrix, diracInverse, fromBlocks_multiply, zero_mul, mul_zero,
    zero_add, add_zero, hDI, neg_mul, mul_neg, neg_neg, neg_zero]
  simp only [← mul_assoc, hT, one_mul, neg_add_cancel, fromBlocks_one]

theorem inverse_mul_constraint (D I K : Matrix ι ι R)
    (hDI : D * I = 1) (hID : I * D = 1) :
    diracInverse I K * constraintMatrix D K = 1 := by
  have hT : Iᵀ * Dᵀ = 1 := by rw [← transpose_mul, hDI, transpose_one]
  simp only [constraintMatrix, diracInverse, fromBlocks_multiply, zero_mul, mul_zero,
    zero_add, add_zero, hID, neg_mul, mul_neg, neg_neg, neg_zero, hT]
  rw [mul_assoc (Iᵀ * K), hID, mul_one, add_neg_cancel, fromBlocks_one]

omit [DecidableEq ι] in
/-- Remaining canonical variables commute with the scalar-normal coordinates.
Their brackets with the Gauss coordinates can be arbitrary. -/
theorem remaining_dirac_correction_zero (I K : Matrix ι ι R) (f g : ι → R) :
    (Sum.elim (fun _ : ι => 0) f) ⬝ᵥ
      (diracInverse I K *ᵥ Sum.elim (fun _ : ι => 0) g) = 0 := by
  simp [diracInverse, mulVec, dotProduct]

omit [DecidableEq ι] in
theorem remaining_dirac_bracket (I K : Matrix ι ι R) (f g : ι → R) (bracket : R) :
    bracket - (Sum.elim (fun _ : ι => 0) f) ⬝ᵥ
      (diracInverse I K *ᵥ Sum.elim (fun _ : ι => 0) g) = bracket := by
  rw [remaining_dirac_correction_zero, sub_zero]

/-- The determinant identity does not require an invertibility assumption. -/
theorem constraint_determinant (D K : Matrix ι ι R) :
    (constraintMatrix D K).det = D.det ^ 2 := by
  let J : Matrix (ι ⊕ ι) (ι ⊕ ι) R := fromBlocks 0 (-1) 1 0
  have hfactor : J =
      fromBlocks (1 : Matrix ι ι R) (-1) 0 1 *
      fromBlocks (1 : Matrix ι ι R) 0 1 1 *
      fromBlocks (1 : Matrix ι ι R) (-1) 0 1 := by
    simp [J, fromBlocks_multiply]
  have hJ : J.det = 1 := by
    simp only [hfactor, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂,
      det_one, one_mul]
  have hproduct : constraintMatrix D K * J = fromBlocks D 0 K Dᵀ := by
    simp [constraintMatrix, J, fromBlocks_multiply]
  have hdet := congrArg Matrix.det hproduct
  simpa [det_mul, hJ, det_fromBlocks_zero₁₂, det_transpose, pow_two] using hdet

section Measure

/-- The two constraint delta-functions and the second-class determinant cancel.
`gram` is the scalar-normal frame determinant, and `jacobian` is `det D`.
The physical reduced phase measure acquires no broken-orbit determinant. -/
theorem second_class_measure_cancellation (gram jacobian : ℝ)
    (hgram : gram ≠ 0) (hjacobian : jacobian ≠ 0) :
    (1 / |gram|) * (|gram| / |jacobian|) * |jacobian| = 1 := by
  have hg : |gram| ≠ 0 := abs_ne_zero.mpr hgram
  have hd : |jacobian| ≠ 0 := abs_ne_zero.mpr hjacobian
  field_simp

theorem constraint_measure_cancellation (D K : Matrix ι ι ℝ) (gram : ℝ)
    (hgram : gram ≠ 0) (hD : D.det ≠ 0) :
    (1 / |gram|) * (|gram| / |D.det|) * Real.sqrt ((constraintMatrix D K).det) = 1 := by
  rw [constraint_determinant, Real.sqrt_sq_eq_abs]
  exact second_class_measure_cancellation gram D.det hgram hD

end Measure

end LowEnergy.SecondClassReduction
