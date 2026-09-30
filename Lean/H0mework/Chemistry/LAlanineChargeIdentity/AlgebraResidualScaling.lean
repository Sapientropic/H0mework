import H0mework.Chemistry.LAlanineChargeIdentity.AlgebraMatrixScaling

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Algebra

open scoped BigOperators

variable {n : Type} [Fintype n]

theorem scaled_residual_entry (V : Int) (B z : n → Int) :
    (V : ℚ) / 1000000000000 + ∑ j, ((B j : ℚ) / 1000000000000000) * (z j : ℚ) =
      ((1000 * V + ∑ j, B j * z j : Int) : ℚ) / 1000000000000000 := by
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, add_div, Finset.sum_div]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem scaled_residual_bound (r : Int) (bound : |r| ≤ 1000000) :
    |(r : ℚ) / 1000000000000000| ≤ 1 / 1000000000 := by
  have castBound : |(r : ℚ)| ≤ 1000000 := by exact_mod_cast bound
  rw [abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 1000000000000000)]
  exact (div_le_iff₀ (by norm_num)).mpr (by norm_num; exact castBound)

end LAlanine40K2025.ChargeIdentity.Algebra
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
