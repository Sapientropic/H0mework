import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNormData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem cross_squared_sum : (∑ i : Basis, ∑ j : Basis, ‖(Source.crossMatrix - 1) i j‖ ^ 2) =
    (crossSquareSum : ℝ) / 10 ^ 30 := by
  simp only [crossSquareSum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [crossDelta_entry]
  norm_num [norm_div, Complex.norm_intCast, div_pow, sq_abs]

theorem cross_frobenius_bound : ‖Source.crossMatrix - 1‖ ≤ (74 : ℝ) / 10 ^ 12 := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  rw [cross_squared_sum, crossSquareSum_exact]
  norm_num

theorem sourceCross_close : ‖Source.crossMatrix - 1‖ < 1 := cross_frobenius_bound.trans_lt (by norm_num)

theorem symmetric_cross_entry (i j : Basis) :
    (star (Source.crossMatrix - 1) + (Source.crossMatrix - 1)) i j =
      (symmetricCrossDelta i j : ℂ) / 1000000000000000 := by
  change star ((Source.crossMatrix - 1) j i) + (Source.crossMatrix - 1) i j = _
  rw [crossDelta_entry, crossDelta_entry]
  simp [symmetricCrossDelta, Int.cast_add, add_div, add_comm]

theorem symmetric_cross_squared_sum :
    (∑ i : Basis, ∑ j : Basis, ‖(star (Source.crossMatrix - 1) + (Source.crossMatrix - 1)) i j‖ ^ 2) =
      (symmetricCrossSquareSum : ℝ) / 10 ^ 30 := by
  simp only [symmetricCrossSquareSum, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [symmetric_cross_entry]
  norm_num [norm_div, Complex.norm_intCast, div_pow, sq_abs]

theorem symmetric_cross_bound :
    ‖star (Source.crossMatrix - 1) + (Source.crossMatrix - 1)‖ ≤ (329 : ℝ) / 10 ^ 15 := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  rw [symmetric_cross_squared_sum, symmetricCrossSquareSum_exact]
  norm_num

theorem cross_gram_bound : ‖star Source.crossMatrix * Source.crossMatrix - 1‖ < (330 : ℝ) / 10 ^ 15 := by
  have decomposition : star Source.crossMatrix * Source.crossMatrix - 1 =
      (star (Source.crossMatrix - 1) + (Source.crossMatrix - 1)) +
        star (Source.crossMatrix - 1) * (Source.crossMatrix - 1) := by
    simp only [star_sub, star_one]
    noncomm_ring
  rw [decomposition]
  have triangle := norm_add_le (star (Source.crossMatrix - 1) + (Source.crossMatrix - 1))
    (star (Source.crossMatrix - 1) * (Source.crossMatrix - 1))
  have product := norm_mul_le (star (Source.crossMatrix - 1)) (Source.crossMatrix - 1)
  rw [norm_star] at product
  have cross := cross_frobenius_bound
  have symmetric := symmetric_cross_bound
  nlinarith [norm_nonneg (Source.crossMatrix - 1)]

theorem geometric_unitary_close :
    ‖ElectronicFrame.Polar.matrix Source.crossMatrix - 1‖ < (75 : ℝ) / 10 ^ 12 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (ElectronicFrame.Polar.matrix Source.crossMatrix) Source.crossMatrix 1
  have residual := ElectronicFrame.Polar.projectionResidual_norm_le_gram Source.crossMatrix sourceCross_close
  change ‖Source.crossMatrix - ElectronicFrame.Polar.matrix Source.crossMatrix‖ ≤ _ at residual
  rw [norm_sub_rev] at residual
  linarith [cross_gram_bound, cross_frobenius_bound]

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
