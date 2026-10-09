import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace BellRegisteredTensorAction

open Matrix
open scoped Kronecker

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
theorem source_tensor_left_right (la a ra : Matrix m m ℂ) (lb b rb : Matrix n n ℂ) :
    (la ⊗ₖ lb) * (a ⊗ₖ b) * (ra ⊗ₖ rb) = (la * a * ra) ⊗ₖ (lb * b * rb) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

omit [DecidableEq m] in
theorem same_side_recycle (l a r : Matrix m m ℂ) (b : Matrix n n ℂ) :
    (l ⊗ₖ (1 : Matrix n n ℂ)) * (a ⊗ₖ b) * (r ⊗ₖ (1 : Matrix n n ℂ)) =
      (l * a * r) ⊗ₖ b := by
  rw [source_tensor_left_right, Matrix.one_mul, Matrix.mul_one]

theorem opposite_side_recycle (l a : Matrix m m ℂ) (b r : Matrix n n ℂ) :
    (l ⊗ₖ (1 : Matrix n n ℂ)) * (a ⊗ₖ b) * ((1 : Matrix m m ℂ) ⊗ₖ r) =
      (l * a) ⊗ₖ (b * r) := by
  rw [source_tensor_left_right, Matrix.mul_one, Matrix.one_mul]

omit [Fintype m] [DecidableEq m] in
theorem complete_adjoint_pair (c : ℂ) (z : Matrix m m ℂ) :
    (c • z + star c • zᴴ).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, add_comm]

end BellRegisteredTensorAction
