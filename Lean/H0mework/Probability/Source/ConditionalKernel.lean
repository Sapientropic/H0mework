import H0mework.Probability.Source.ConditionalNextEntropy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
universe u v w x

theorem SourceConditionalHistory.conditional_eq_of_fibre {Source : Type u} {Left : Type v} {Right : Type w}
    (source : PMF Source) (left : Source → Left) (right : Source → Right)
    (leftValue : Left) (rightValue : Right)
    (leftSupported : leftValue ∈ (source.map left).support) (rightSupported : rightValue ∈ (source.map right).support)
    (same : ∀ point, left point = leftValue ↔ right point = rightValue) :
    SourceConditionalHistory.conditional source left leftValue leftSupported =
      SourceConditionalHistory.conditional source right rightValue rightSupported := by
  unfold SourceConditionalHistory.conditional
  congr 1
  exact Set.ext same

theorem SourceConditionalNext.conditionalEntropy_eq_of_kernel {Source : Type u} [Fintype Source]
    {Left : Type v} {Right : Type w} {Next : Type x} [Fintype Next]
    (source : PMF Source) (left : Source → Left) (right : Source → Right) (nextRead : Source → Next)
    (positive : ∀ point, point ∈ source.support)
    (same : ∀ a b, left a = left b ↔ right a = right b) :
    SourceConditionalNext.conditionalEntropy source left nextRead positive =
      SourceConditionalNext.conditionalEntropy source right nextRead positive := by
  unfold SourceConditionalNext.conditionalEntropy SourceConditionalNext.conditionalNext
  apply Finset.sum_congr rfl
  intro point _
  rw [SourceConditionalHistory.conditional_eq_of_fibre source left right (left point) (right point)
    (SourceWeightedRecovery.observed_supported source left point (positive point))
    (SourceWeightedRecovery.observed_supported source right point (positive point)) (fun other => same other point)]

end
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
