import H0mework.Chemistry.LAlanineChargeIdentity.AlgebraIntegerStability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Algebra

open scoped BigOperators Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

def rationalMatrix (rows : Matrix n n Int) (scale : Nat) : Matrix n n ℚ :=
  Matrix.of fun i j => (rows i j : ℚ) / scale

omit [DecidableEq n] in
theorem rationalMatrix_mul_entry (N B : Matrix n n Int) (D S : Nat) (i j : n) :
    (rationalMatrix N D * rationalMatrix B S) i j =
      ((∑ k, N i k * B k j : Int) : ℚ) / ((D : ℚ) * S) := by
  simp only [Matrix.mul_apply, rationalMatrix, Matrix.of_apply, div_mul_div_comm,
    Int.cast_sum, Int.cast_mul, Finset.sum_div]

theorem integer_leftInverse_to_rational (N B : Matrix n n Int) (D S : Nat)
    (positiveD : 0 < D) (positiveS : 0 < S)
    (product : ∀ i j, ∑ k, N i k * B k j =
      (D : Int) * (S : Int) * if i = j then 1 else 0) :
    rationalMatrix N D * rationalMatrix B S = 1 := by
  have dne : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positiveD)
  have sne : (S : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positiveS)
  ext i j
  rw [rationalMatrix_mul_entry, product]
  by_cases same : i = j
  · subst j
    simp [dne, sne]
  · simp [same]

omit [DecidableEq n] in
theorem rationalMatrix_rowAbsSum (N : Matrix n n Int) (D : Nat) (i : n) :
    rowAbsSum (rationalMatrix N D) i = ((∑ j, |N i j| : Int) : ℚ) / D := by
  have dabs : |(D : ℚ)| = D := abs_of_nonneg (Nat.cast_nonneg D)
  simp only [rowAbsSum, rationalMatrix, Matrix.of_apply, abs_div, dabs,
    Int.cast_sum, Int.cast_abs, Finset.sum_div]

end LAlanine40K2025.ChargeIdentity.Algebra
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
