import H0mework.Probability.Recovery.Decoder

/-! The source-generated transfer is exactly the complete conditional task mean on every reachable output. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

open MeasureTheory
open scoped InnerProductSpace Classical

noncomputable section

universe u v

variable {Source : Type u} [Fintype Source] {Observed : Type v}
variable (source : PMF Source) (observer : Source → Observed)

def conditionalMean (task : Source → ℂ) (atom : Observed) (supported : atom ∈ (observed source observer).support) : ℂ :=
  ∑ point : Source, (SourceConditionalHistory.conditional source observer atom supported point).toReal • task point

theorem conditionalMean_weighted (task : Source → ℂ) (atom : Observed)
    (supported : atom ∈ (observed source observer).support) :
    (observed source observer atom).toReal • conditionalMean source observer task atom supported =
      ∑ point : Source, (source point).toReal • (if observer point = atom then task point else 0) := by
  rw [conditionalMean, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro point _
  have weights := SourceConditionalHistory.weighted_conditional source observer atom supported point
  rw [smul_smul, ← ENNReal.toReal_mul, weights]
  by_cases same : observer point = atom <;> simp [same]

variable [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def optimalDecoder (task : Source → ℂ) : Observed → ℂ := transfer source observer (taskValue source task)

theorem weighted_optimal (task : Source → ℂ) (atom : Observed) :
    (observed source observer atom).toReal • optimalDecoder source observer task atom =
      ∑ point : Source, (source point).toReal • (if observer point = atom then task point else 0) := by
  calc
    _ = ⟪atomTest source observer atom, transfer source observer (taskValue source task)⟫_ℂ := by
      rw [atomTest, L2.inner_indicatorConstLp_one, integral_singleton]
      change _ = ((observed source observer).toMeasure {atom}).toReal • _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      rfl
    _ = ⟪pullback source observer (atomTest source observer atom), taskValue source task⟫_ℂ :=
      (pullback source observer).toContinuousLinearMap.adjoint_inner_right _ _
    _ = _ := by
      rw [inner_source_sum]
      apply Finset.sum_congr rfl
      intro point _
      by_cases zero : source point = 0
      · simp only [zero, ENNReal.toReal_zero, zero_smul]
      · rw [pullback_at source observer _ point zero, taskValue_at source task point zero,
          atomTest_at source observer _ (observer point) (observed_supported source observer point zero)]
        by_cases same : observer point = atom <;> simp [same]

theorem optimal_is_conditional (task : Source → ℂ) (atom : Observed)
    (supported : atom ∈ (observed source observer).support) :
    optimalDecoder source observer task atom = conditionalMean source observer task atom supported := by
  have nonzero : (observed source observer atom).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨supported, (observed source observer).apply_ne_top atom⟩
  exact (smul_right_injective (M := ℂ) nonzero)
    ((weighted_optimal source observer task atom).trans (conditionalMean_weighted source observer task atom supported).symm)

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
