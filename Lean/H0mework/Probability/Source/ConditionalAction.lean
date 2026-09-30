import H0mework.Probability.Source.Conditional

/-! Actual action and an injective observation update transport the complete existing conditional law. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory

open scoped Classical
noncomputable section
universe u v w z
variable {Source : Type u} {Next : Type v} {Observed : Type w} {NextObserved : Type z}

theorem conditional_pushforward (source : PMF Source) (read : Source → Observed)
    (action : Source → Next) (nextRead : Next → NextObserved) (observedAction : Observed → NextObserved)
    (sourceSquare : ∀ point, nextRead (action point) = observedAction (read point))
    (injective : Function.Injective observedAction) (value : Observed)
    (supported : value ∈ (observed source read).support) :
    ∃ nextSupported : observedAction value ∈ (observed (source.map action) nextRead).support,
      (conditional source read value supported).map action =
        conditional (source.map action) nextRead (observedAction value) nextSupported := by
  have square : observed (source.map action) nextRead = (observed source read).map observedAction := by
    simp only [observed, PMF.map_comp]
    congr 1
    exact funext sourceSquare
  have normalizer : observed (source.map action) nextRead (observedAction value) = observed source read value := by
    rw [square, PMF.map_apply, tsum_eq_single value]
    · exact if_pos rfl
    · intro other different
      exact if_neg (fun same => different (injective same).symm)
  have nextSupported : observedAction value ∈ (observed (source.map action) nextRead).support := by
    change observed (source.map action) nextRead (observedAction value) ≠ 0
    rw [normalizer]
    exact supported
  refine ⟨nextSupported, ?_⟩
  apply PMF.ext
  intro target
  rw [PMF.map_apply, conditional_apply, normalizer]
  by_cases visible : nextRead target = observedAction value
  · rw [if_pos visible, PMF.map_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro point
    rw [conditional_apply]
    by_cases reaches : target = action point
    · have same : read point = value :=
        injective ((sourceSquare point).symm.trans (by simpa only [← reaches] using visible))
      rw [if_pos reaches, if_pos same, if_pos reaches]
    · rw [if_neg reaches, if_neg reaches, zero_mul]
  · rw [if_neg visible]
    apply ENNReal.tsum_eq_zero.mpr
    intro point
    rw [conditional_apply]
    by_cases reaches : target = action point
    · have unseen : read point ≠ value := by
        intro same
        apply visible
        rw [reaches, sourceSquare, same]
      rw [if_pos reaches, if_neg unseen]
    · exact if_neg reaches

end
end SourceConditionalHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
