import H0mework.Probability.Recovery.Error

/-! Two retained source atoms in one observation fibre impose their paid recovery cost. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

noncomputable section
universe u v
variable {Source : Type u} [Fintype Source] {Observed : Type v}

theorem equal_weight_pair_lower_bound (source : PMF Source) (observer : Source → Observed)
    (task : Source → ℂ) (decoder : Observed → ℂ) (left right : Source)
    (distinct : left ≠ right) (same : observer left = observer right)
    (weight : (source left).toReal = (source right).toReal) :
    (source left).toReal * ‖task left - task right‖ ^ 2 / 2 ≤ error source observer task decoder := by
  classical
  have selected : (source left).toReal * ‖task left - decoder (observer left)‖ ^ 2 +
      (source right).toReal * ‖task right - decoder (observer right)‖ ^ 2 ≤
        error source observer task decoder := by
    rw [← Finset.sum_pair distinct
      (f := fun point => (source point).toReal * ‖task point - decoder (observer point)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun point _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  rw [← weight, ← same] at selected
  have triangle : ‖task left - task right‖ ≤
      ‖task left - decoder (observer left)‖ + ‖task right - decoder (observer left)‖ := by
    calc
      _ = ‖(task left - decoder (observer left)) - (task right - decoder (observer left))‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  have squares : ‖task left - task right‖ ^ 2 ≤
      2 * (‖task left - decoder (observer left)‖ ^ 2 + ‖task right - decoder (observer left)‖ ^ 2) := by
    nlinarith [norm_nonneg (task left - task right),
      norm_nonneg (task left - decoder (observer left)), norm_nonneg (task right - decoder (observer left)),
      sq_nonneg (‖task left - decoder (observer left)‖ - ‖task right - decoder (observer left)‖)]
  have paid := mul_le_mul_of_nonneg_left squares (ENNReal.toReal_nonneg (a := source left))
  nlinarith

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
