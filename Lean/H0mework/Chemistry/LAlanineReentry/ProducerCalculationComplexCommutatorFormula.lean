import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Arithmetic

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι]

theorem scaled_commutator_entry (H R J : Matrix ι ι Int) (a b : ℂ) (i j : ι) :
    (Matrix.of (fun i j => (H i j : ℂ) / a) *
      Matrix.of (fun i j => ((R i j : ℂ) + Complex.I * (J i j : ℂ)) / b) -
      Matrix.of (fun i j => ((R i j : ℂ) + Complex.I * (J i j : ℂ)) / b) *
      Matrix.of (fun i j => (H i j : ℂ) / a)) i j =
      (((∑ k, (H i k * R k j - R i k * H k j) : Int) : ℂ) +
        Complex.I * ((∑ k, (H i k * J k j - J i k * H k j) : Int) : ℂ)) / (a * b) := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_sub, Int.cast_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem complex_integer_norm_le (real imaginary : Int) :
    ‖(real : ℂ) + Complex.I * (imaginary : ℂ)‖ ≤ (real.natAbs : ℝ) + (imaginary.natAbs : ℝ) := by
  have triangle := norm_add_le (real : ℂ) (Complex.I * (imaginary : ℂ))
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Nat.cast_natAbs,
    Int.cast_abs] using triangle

theorem paired_nat_sum (r s : ι → ι → Nat) (denominator : ℝ) :
    (∑ i, ∑ j, ((r i j : ℝ) + (s i j : ℝ)) / denominator) =
      (((∑ i, ∑ j, r i j) + (∑ i, ∑ j, s i j) : Nat) : ℝ) / denominator := by
  simp only [Nat.cast_add, Nat.cast_sum, Finset.sum_div, Finset.sum_add_distrib, add_div]

end LAlanine40K2025.Reentry.Arithmetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
