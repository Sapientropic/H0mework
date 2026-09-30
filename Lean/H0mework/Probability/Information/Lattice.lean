import H0mework.Probability.Information.Variance

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreVariance.Lattice

noncomputable section

theorem index_sum (count : Nat) :
    (∑ index : Fin count, (index.val : ℝ)) = (count : ℝ) * ((count : ℝ) - 1) / 2 := by
  induction count with
  | zero => simp
  | succ count previous =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, previous, Nat.cast_add, Nat.cast_one]
      ring

theorem index_square_sum (count : Nat) :
    (∑ index : Fin count, (index.val : ℝ) ^ 2) =
      (count : ℝ) * ((count : ℝ) - 1) * (2 * (count : ℝ) - 1) / 6 := by
  induction count with
  | zero => simp
  | succ count previous =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, previous, Nat.cast_add, Nat.cast_one]
      ring

private theorem index_pair_inner (count : Nat) (value : ℝ) :
    (∑ index : Fin count, ((index.val : ℝ) - value) ^ 2) =
      (∑ index : Fin count, (index.val : ℝ) ^ 2) -
        2 * value * (∑ index : Fin count, (index.val : ℝ)) + (count : ℝ) * value ^ 2 := by
  have expanded (index : Fin count) : ((index.val : ℝ) - value) ^ 2 =
      (index.val : ℝ) ^ 2 - 2 * value * (index.val : ℝ) + value ^ 2 := by ring
  simp only [expanded, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem index_pair_square_sum (count : Nat) :
    (∑ left : Fin count, ∑ right : Fin count, ((right.val : ℝ) - (left.val : ℝ)) ^ 2) =
      (count : ℝ) ^ 2 * ((count : ℝ) ^ 2 - 1) / 6 := by
  simp only [index_pair_inner, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [index_sum, index_square_sum]
  ring

theorem lattice_pair_square_sum (count : Nat) (offset : ℝ) :
    (∑ left : Fin count, ∑ right : Fin count,
      ((2 * (right.val : ℝ) + offset) - (2 * (left.val : ℝ) + offset)) ^ 2) =
      (2 / 3 : ℝ) * (count : ℝ) ^ 2 * ((count : ℝ) ^ 2 - 1) := by
  have expanded (left right : Fin count) :
      ((2 * (right.val : ℝ) + offset) - (2 * (left.val : ℝ) + offset)) ^ 2 =
        4 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 := by ring
  simp only [expanded, ← Finset.mul_sum]
  rw [index_pair_square_sum]
  ring

end
end SourceUniformFibreVariance.Lattice
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
