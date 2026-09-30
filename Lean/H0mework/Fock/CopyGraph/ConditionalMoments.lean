import H0mework.Probability.HistoryWord.Moments

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem residual_mean (bound : Nat) (observer : Fin (bound + 1) → Observed) (value : Space (historyPMF bound)) :
    (∫ actor, residual (historyPMF bound) observer value actor ∂(historyPMF bound).toMeasure) = 0 := by
  let constant : Space (observed (historyPMF bound) observer) :=
    Lp.const 2 (observed (historyPMF bound) observer).toMeasure (1 : ℂ)
  have constantAt (actor : Fin (bound + 1)) : pullback (historyPMF bound) observer constant actor = 1 := by
    rw [pullback_at _ _ _ actor (source_positive bound actor)]
    exact ae_at_support (observed (historyPMF bound) observer) (observer actor)
      (observed_supported _ _ actor (source_positive bound actor)) (Lp.coeFn_const 2 _ (1 : ℂ))
  have orthogonal := IsometricRetainedTransfer.residual_orthogonal (pullback (historyPMF bound) observer) value constant
  rw [inner_source_sum] at orthogonal
  simp_rw [constantAt] at orthogonal
  rw [PMF.integral_eq_sum]
  simpa only [RCLike.inner_apply, map_one, mul_one] using orthogonal

theorem residual_mass (bound : Nat) (observer : Fin (bound + 1) → Observed) (value : Space (historyPMF bound)) :
    SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound (residual (historyPMF bound) observer value)) = 0 := by
  have original := SourceHistoryWord.mass_original_mean bound (residual (historyPMF bound) observer value)
  change SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound (residual (historyPMF bound) observer value)) = _ at original
  rw [original, residual_mean, smul_zero]

end
end SourceConditionalGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
