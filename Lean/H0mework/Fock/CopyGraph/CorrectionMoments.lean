import H0mework.Fock.CopyGraph.CorrectionSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def one (bound : Nat) (query : Fin (bound + 1) → Observed) : Space (observed (historyPMF bound) query) :=
  Lp.const 2 (observed (historyPMF bound) query).toMeasure (1 : ℂ)

def clockMean (bound : Nat) (query : Fin (bound + 1) → Observed) : Space (observed (historyPMF bound) query) :=
  transfer (historyPMF bound) query (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound))

theorem one_at (bound : Nat) (query : Fin (bound + 1) → Observed) (actor : Fin (bound + 1)) :
    pullback (historyPMF bound) query (one bound query) actor = 1 := by
  rw [pullback_at _ _ _ actor (source_positive bound actor)]
  exact ae_at_support (observed (historyPMF bound) query) (query actor)
    (observed_supported _ _ actor (source_positive bound actor)) (Lp.coeFn_const 2 _ (1 : ℂ))

omit [MeasurableSingletonClass Observed] in
theorem one_norm (bound : Nat) (query : Fin (bound + 1) → Observed) : ‖one bound query‖ = 1 := by
  unfold one
  rw [Lp.norm_const' 2 _ (1 : ℂ) (by norm_num : (2 : ENNReal) ≠ 0) (by simp : (2 : ENNReal) ≠ ⊤)]
  simp

theorem mass_pullback (bound : Nat) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) :
    SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound (pullback (historyPMF bound) query value)) =
      Real.sqrt (bound + 1 : ℝ) • inner ℂ (one bound query) value := by
  have original := SourceHistoryWord.mass_original_mean bound (pullback (historyPMF bound) query value)
  change SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound (pullback (historyPMF bound) query value)) = _ at original
  rw [original, ← (pullback (historyPMF bound) query).inner_map_map, inner_source_sum, PMF.integral_eq_sum]
  simp only [one_at, RCLike.inner_apply, map_one, mul_one]

omit [MeasurableSingletonClass Observed] in
theorem clock_pullback (bound : Nat) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) :
    SourceClockComplex.clock (SourceHistoryWord.word bound (pullback (historyPMF bound) query value)) =
      Real.sqrt (bound + 1 : ℝ) • inner ℂ (clockMean bound query) value := by
  rw [SourceConditionalGraph.clock_inner]
  exact congrArg (fun scalar : ℂ => Real.sqrt (bound + 1 : ℝ) • scalar)
    ((pullback (historyPMF bound) query).toContinuousLinearMap.adjoint_inner_left value
      (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound))).symm

theorem clock_mean_conditional (bound : Nat) (query : Fin (bound + 1) → Observed) (atom : Observed)
    (supported : atom ∈ (observed (historyPMF bound) query).support) :
    clockMean bound query atom = ∑ actor : Fin (bound + 1),
      (SourceConditionalHistory.conditional (historyPMF bound) query atom supported actor).toReal •
        SourceGeneratedJointClock.signal bound actor :=
  SourceConditionalGraph.clock_conditional bound query atom supported

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
