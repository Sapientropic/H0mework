import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Subordinate rational-field recovery; actual matrices and certificates are source output. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Algebra

open scoped BigOperators Matrix

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n]

def rowAbsSum (L : Matrix n m ℚ) (i : n) : ℚ := ∑ j, |L i j|

theorem leftInverse_recovers (L : Matrix n m ℚ) (B : Matrix m n ℚ)
    (leftInverse : L * B = 1) (z : n → ℚ) : L *ᵥ (B *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, leftInverse, Matrix.one_mulVec]

theorem fieldRead_injective (L : Matrix n m ℚ) (B : Matrix m n ℚ)
    (leftInverse : L * B = 1) : Function.Injective (fun z : n → ℚ => B *ᵥ z) := by
  intro z w same
  have lifted := congrArg (fun value => L *ᵥ value) same
  simpa only [leftInverse_recovers L B leftInverse] using lifted

omit [Fintype n] [DecidableEq n] in
theorem mulVec_abs_le (L : Matrix n m ℚ) (r : m → ℚ) (epsilon : ℚ)
    (bound : ∀ j, |r j| ≤ epsilon) (i : n) :
    |(L *ᵥ r) i| ≤ rowAbsSum L i * epsilon := by
  change |∑ j, L i j * r j| ≤ (∑ j, |L i j|) * epsilon
  calc
    _ ≤ ∑ j, |L i j * r j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |L i j| * |r j| := by simp only [abs_mul]
    _ ≤ ∑ j, |L i j| * epsilon :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (bound j) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem integer_eq_of_distance_lt_one (a b : Int)
    (near : |(a : ℚ) - (b : ℚ)| < 1) : a = b := by
  have small : |a - b| < (1 : Int) := by exact_mod_cast near
  have both := abs_lt.mp small
  omega

def residual (B : Matrix m n ℚ) (V : m → ℚ) (z : n → Int) : m → ℚ :=
  V + B *ᵥ (fun i => (z i : ℚ))

theorem residual_recovery (L : Matrix n m ℚ) (B : Matrix m n ℚ)
    (leftInverse : L * B = 1) (V : m → ℚ) (z : n → Int) :
    L *ᵥ residual B V z = L *ᵥ V + (fun i => (z i : ℚ)) := by
  rw [residual, Matrix.mulVec_add, leftInverse_recovers L B leftInverse]

theorem compatible_integer_unique (L : Matrix n m ℚ) (B : Matrix m n ℚ)
    (leftInverse : L * B = 1) (V : m → ℚ) (epsilon : ℚ)
    (margin : ∀ i, 2 * (rowAbsSum L i * epsilon) < 1)
    (z w : n → Int) (zBound : ∀ j, |residual B V z j| ≤ epsilon)
    (wBound : ∀ j, |residual B V w j| ≤ epsilon) : z = w := by
  funext i
  apply integer_eq_of_distance_lt_one
  have hdiff : (z i : ℚ) - (w i : ℚ) =
      (L *ᵥ residual B V z) i - (L *ᵥ residual B V w) i := by
    rw [residual_recovery L B leftInverse, residual_recovery L B leftInverse]
    simp only [Pi.add_apply]
    ring
  rw [hdiff]
  calc
    _ ≤ |(L *ᵥ residual B V z) i| + |(L *ᵥ residual B V w) i| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le ((L *ᵥ residual B V z) i) 0 ((L *ᵥ residual B V w) i))
    _ ≤ rowAbsSum L i * epsilon + rowAbsSum L i * epsilon :=
      add_le_add (mulVec_abs_le L _ epsilon zBound i) (mulVec_abs_le L _ epsilon wBound i)
    _ = 2 * (rowAbsSum L i * epsilon) := by ring
    _ < 1 := margin i

end LAlanine40K2025.ChargeIdentity.Algebra
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
