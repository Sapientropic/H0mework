import H0mework.Probability.Recovery.Error
import H0mework.Probability.Runtime.History

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreVariance

open scoped Classical
noncomputable section

private theorem centered_expansion {A : Type*} (indices : Finset A) (task : A → ℝ) (center : ℝ) :
    (∑ index ∈ indices, (task index - center) ^ 2) =
      (∑ index ∈ indices, task index ^ 2) - 2 * center * (∑ index ∈ indices, task index) +
        indices.card * center ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem ordered_pair_expansion {A : Type*} (indices : Finset A) (task : A → ℝ) :
    (∑ left ∈ indices, ∑ right ∈ indices, (task right - task left) ^ 2) =
      2 * indices.card * (∑ index ∈ indices, task index ^ 2) -
        2 * (∑ index ∈ indices, task index) ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem mean_pairwise {A : Type*} (indices : Finset A) (task : A → ℝ) :
    (∑ index ∈ indices, (task index - (∑ other ∈ indices, task other) / indices.card) ^ 2) =
      (1 / (2 * (indices.card : ℝ))) *
        ∑ left ∈ indices, ∑ right ∈ indices, (task right - task left) ^ 2 := by
  by_cases empty : indices = ∅
  · simp [empty]
  · have nonzero : (indices.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    rw [centered_expansion, ordered_pair_expansion]
    field_simp
    ring

theorem real_norm_square (left right : ℝ) : ‖(left : ℂ) - (right : ℂ)‖ ^ 2 = (left - right) ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_self, mul_zero, add_zero]
  ring

end
end SourceUniformFibreVariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
