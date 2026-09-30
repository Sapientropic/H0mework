import H0mework.Probability.Source.ConditionalCoarsening

/-! The old complete mixture is pushed through the actual source action, without injectivity of the observed action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory.Coarsening

noncomputable section
universe u v w
variable {Source : Type u} {Next : Type v} {Observed : Type w}

theorem mixture_pushforward (source : PMF Source) (read : Source → Observed)
    (action : Source → Next) (nextRead : Next → Observed) (observedAction : Observed → Observed)
    (sourceSquare : ∀ point, nextRead (action point) = observedAction (read point))
    (value : Observed) (supported : value ∈ (observed (observed source read) observedAction).support) :
    ∃ nextSupported : value ∈ (observed (source.map action) nextRead).support,
      (mixture source read observedAction value supported).map action =
        conditional (source.map action) nextRead value nextSupported := by
  obtain ⟨coarseSupported, complete⟩ := mixture_is_conditional source read observedAction value supported
  obtain ⟨nextSupported, pushed⟩ := conditional_pushforward source (observedAction ∘ read)
    action nextRead id sourceSquare Function.injective_id value coarseSupported
  refine ⟨nextSupported, ?_⟩
  rw [complete]
  exact pushed

end
end SourceConditionalHistory.Coarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
