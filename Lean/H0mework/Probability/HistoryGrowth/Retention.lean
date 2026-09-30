import H0mework.Probability.HistoryGrowth.Geometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryGrowth

open SourceWeightedRecovery SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability
open SourceUniformFibreVariance MeasureTheory
open scoped Classical
noncomputable section

variable {old fresh : Nat} (retained : old ≤ fresh)

private theorem new_ne_prior (index : Fin (fresh + 1)) (new : old + 1 ≤ index.val)
    (before : Fin (old + 1)) : index ≠ includeActor retained before := by
  intro same
  have values := congrArg (fun index : Fin (fresh + 1) => index.val) same
  change index.val = before.val at values
  have inside := before.isLt
  omega

theorem extend_at_new (value : Space (historyPMF old)) (index : Fin (fresh + 1))
    (new : old + 1 ≤ index.val) : extend retained value index = 0 := by
  change evalAt (historyPMF fresh) index (source_positive fresh index) (extend retained value) = _
  simp only [extend, sum_apply, ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  change (∑ before : Fin (old + 1), value before • cotest (historyPMF fresh) (includeActor retained before) index) = 0
  apply Finset.sum_eq_zero
  intro before _
  rw [cotest_value, if_neg (new_ne_prior retained index new before), smul_zero]

theorem remainder_at_prior (value : Space (historyPMF fresh)) (index : Fin (old + 1)) :
    remainder retained value (includeActor retained index) = 0 := by
  rw [remainder_eq]
  change evalAt (historyPMF fresh) (includeActor retained index) (source_positive fresh _)
    (value - extend retained (restrict retained value)) = 0
  rw [map_sub]
  change value (includeActor retained index) - extend retained (restrict retained value) (includeActor retained index) = 0
  rw [extend_at, restrict_at, sub_self]

theorem remainder_at_new (value : Space (historyPMF fresh)) (index : Fin (fresh + 1))
    (new : old + 1 ≤ index.val) : remainder retained value index = value index := by
  rw [remainder_eq]
  change evalAt (historyPMF fresh) index (source_positive fresh index)
    (value - extend retained (restrict retained value)) = value index
  rw [map_sub]
  change value index - extend retained (restrict retained value) index = value index
  rw [extend_at_new retained _ index new, sub_zero]

theorem restrict_new_cotest (index : Fin (fresh + 1)) (new : old + 1 ≤ index.val) :
    restrict retained (cotest (historyPMF fresh) index) = 0 := by
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro before
  rw [restrict_at, cotest_value]
  have distinct : includeActor retained before ≠ index := Ne.symm (new_ne_prior retained index new before)
  rw [if_neg distinct]
  exact (ae_at_support (historyPMF old) before (source_positive old before) (Lp.coeFn_zero ℂ 2 (historyPMF old).toMeasure)).symm

theorem remainder_new_cotest (index : Fin (fresh + 1)) (new : old + 1 ≤ index.val) :
    remainder retained (cotest (historyPMF fresh) index) = cotest (historyPMF fresh) index := by
  rw [remainder_eq, restrict_new_cotest retained index new, map_zero, sub_zero]

end
end SourceHistoryGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
