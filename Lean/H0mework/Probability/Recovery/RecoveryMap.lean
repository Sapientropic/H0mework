import H0mework.Probability.Recovery.Error

/-! A generated finite source map transports its exact error under the same weights. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

open MeasureTheory

noncomputable section

universe u v w

theorem error_map {Source : Type u} [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
    {Target : Type v} [Fintype Target] [MeasurableSpace Target] [MeasurableSingletonClass Target]
    {Observed : Type w} (source : PMF Source) (map : Source → Target) (observer : Target → Observed)
    (task : Target → ℂ) (decoder : Observed → ℂ) :
    error (source.map map) observer task decoder = error source (observer ∘ map) (task ∘ map) decoder := by
  let value : Target → ℝ := fun point => ‖task point - decoder (observer point)‖ ^ 2
  change (∑ point : Target, (source.map map point).toReal • value point) =
    ∑ point : Source, (source point).toReal • (value ∘ map) point
  rw [← PMF.integral_eq_sum (source.map map) value, ← PMF.integral_eq_sum source (value ∘ map),
    ← PMF.toMeasure_map map source (measurable_of_finite map)]
  exact integral_map (measurable_of_finite map).aemeasurable (measurable_of_finite value).aestronglyMeasurable

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
