import H0mework.Probability.Source.MomentMoment

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceVectorMoment

noncomputable section
universe u v w
variable {ι : Type u} [Fintype ι] {E : Type v} [NormedAddCommGroup E]

theorem equal_weight_pair (p : PMF ι) (value guess : ι → E) (left right : ι)
    (distinct : left ≠ right) (same : guess left = guess right)
    (weight : (p left).toReal = (p right).toReal) :
    (p left).toReal * ‖value left - value right‖ ^ 2 / 2 ≤
      ∑ i, (p i).toReal * ‖value i - guess i‖ ^ 2 := by
  classical
  have selected : (p left).toReal * ‖value left - guess left‖ ^ 2 +
      (p right).toReal * ‖value right - guess right‖ ^ 2 ≤
        ∑ i, (p i).toReal * ‖value i - guess i‖ ^ 2 := by
    rw [← Finset.sum_pair distinct (f := fun i => (p i).toReal * ‖value i - guess i‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  rw [← weight, ← same] at selected
  have triangle : ‖value left - value right‖ ≤ ‖value left - guess left‖ + ‖value right - guess left‖ := by
    calc
      _ = ‖(value left - guess left) - (value right - guess left)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have squares : ‖value left - value right‖ ^ 2 ≤
      2 * (‖value left - guess left‖ ^ 2 + ‖value right - guess left‖ ^ 2) := by
    nlinarith [norm_nonneg (value left - value right), norm_nonneg (value left - guess left),
      norm_nonneg (value right - guess left), sq_nonneg (‖value left - guess left‖ - ‖value right - guess left‖)]
  have paid := mul_le_mul_of_nonneg_left squares (ENNReal.toReal_nonneg (a := p left))
  nlinarith

end
end SourceVectorMoment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
