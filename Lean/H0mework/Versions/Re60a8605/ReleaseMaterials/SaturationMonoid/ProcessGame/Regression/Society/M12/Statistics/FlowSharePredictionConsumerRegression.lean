/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Kernel.ZeroMassBoundaryRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Consumer.ObserverConditionedPrediction

/-!
# M12 flow-share prediction consumer

The normalized source folds are consumed as derived prediction classes.  The
coarse and fine observers use the same source measure, event and visible label
but produce opposite classes.  No probability value or class is installed as
source data.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12FlowSharePredictionConsumerRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space Observer
open Probability Measure Kernel Consumer
open M12GeneratedFlowObserverFixture
open M12GeneratedFlowMeasureFixture
open M12ObserverGeometryRegression
open M12ZeroMassBoundaryRegression

def coarsePrediction : SourceGeneratedObserverConditionedPredictionAt
    coarseMonthlyFold (.conditioned : Visible) :=
  SourceGeneratedObserverConditionedPredictionAt.generate
    coarseMonthlyFold .conditioned

def finePrediction : SourceGeneratedObserverConditionedPredictionAt
    fineMonthlyFold (.conditioned : Visible) :=
  SourceGeneratedObserverConditionedPredictionAt.generate
    fineMonthlyFold .conditioned

def uniformPrediction : SourceGeneratedObserverConditionedPredictionAt
    coarseUniformFold (.conditioned : Visible) :=
  SourceGeneratedObserverConditionedPredictionAt.generate
    coarseUniformFold .conditioned

def zeroPrediction : SourceGeneratedObserverConditionedPredictionAt
    coarseZeroFold (.conditioned : Visible) :=
  SourceGeneratedObserverConditionedPredictionAt.generate
    coarseZeroFold .conditioned

@[simp] theorem coarse_probability_exact :
    coarsePrediction.probability = some ((8754 : ℚ≥0) / 20581) :=
  coarse_readVisible_exact

@[simp] theorem fine_probability_exact :
    finePrediction.probability = some ((8754 : ℚ≥0) / 11511) :=
  fine_readVisible_exact

@[simp] theorem uniform_probability_exact :
    uniformPrediction.probability = some ((1 : ℚ≥0) / 3) :=
  uniform_coarse_readVisible_exact

@[simp] theorem zero_probability_none : zeroPrediction.probability = none :=
  nonempty_allZero_fibre_is_none.1

theorem coarse_prediction_belowHalf :
    coarsePrediction.classification =
      some ObserverConditionedPredictionClass.belowHalf := by
  apply coarsePrediction.classification_eq_some_belowHalf_iff.mpr
  exact ⟨(8754 : ℚ≥0) / 20581, coarse_probability_exact,
    by simpa [ObserverConditionedPredictionClass.half] using
      coarse_probability_below_half⟩

theorem fine_prediction_aboveHalf :
    finePrediction.classification =
      some ObserverConditionedPredictionClass.aboveHalf := by
  apply finePrediction.classification_eq_some_aboveHalf_iff.mpr
  exact ⟨(8754 : ℚ≥0) / 11511, fine_probability_exact,
    by simpa [ObserverConditionedPredictionClass.half] using
      fine_probability_above_half⟩

theorem uniform_prediction_belowHalf :
    uniformPrediction.classification =
      some ObserverConditionedPredictionClass.belowHalf := by
  apply uniformPrediction.classification_eq_some_belowHalf_iff.mpr
  refine ⟨(1 : ℚ≥0) / 3, uniform_probability_exact, ?_⟩
  unfold ObserverConditionedPredictionClass.half
  change (1 : ℚ) / 3 < (1 : ℚ) / 2
  norm_num

theorem zero_prediction_unclassified :
    zeroPrediction.classification = none :=
  zeroPrediction.classification_eq_none_iff.mpr zero_probability_none

/-- Strong social-statistics consumer: observer kernel geometry alone flips
the prediction class. -/
theorem observer_geometry_flips_prediction_class :
    ObserverConditionedPredictionClass.ReadoutDiffers
      coarsePrediction.classification finePrediction.classification := by
  unfold ObserverConditionedPredictionClass.ReadoutDiffers
  rw [coarse_prediction_belowHalf, fine_prediction_aboveHalf]
  decide

/-- The visible probability computation remains exact and factorized. -/
def coarseProbabilityFactorization :
    ReadoutFactorization coarseObserver coarsePrediction.probabilityReadout :=
  coarsePrediction.exactReadoutFactorization

/-- Its prediction consumer still cannot recover exact source authority. -/
theorem coarse_prediction_not_authority_complete :
    ¬ Nonempty (AuthorityCompleteReadoutAt coarseObserver
      coarsePrediction.probabilityReadout) :=
  coarsePrediction.noAuthorityCompleteConsumer coarseKernelPair

theorem fine_prediction_not_authority_complete :
    ¬ Nonempty (AuthorityCompleteReadoutAt fineObserver
      finePrediction.probabilityReadout) :=
  finePrediction.noAuthorityCompleteConsumer fineKernelPair

structure FlowSharePredictionConsumerCertificate where
  coarse : SourceGeneratedObserverConditionedPredictionAt
    coarseMonthlyFold (.conditioned : Visible)
  fine : SourceGeneratedObserverConditionedPredictionAt
    fineMonthlyFold (.conditioned : Visible)
  coarseBelow : coarse.classification =
    some ObserverConditionedPredictionClass.belowHalf
  fineAbove : fine.classification =
    some ObserverConditionedPredictionClass.aboveHalf
  classificationDiffers :
    ObserverConditionedPredictionClass.ReadoutDiffers
      coarse.classification fine.classification
  coarseFactorization :
    ReadoutFactorization coarseObserver coarse.probabilityReadout
  coarseNoAuthority : ¬ Nonempty
    (AuthorityCompleteReadoutAt coarseObserver coarse.probabilityReadout)
  fineNoAuthority : ¬ Nonempty
    (AuthorityCompleteReadoutAt fineObserver fine.probabilityReadout)

def flowSharePredictionDirectConsumer :
    FlowSharePredictionConsumerCertificate where
  coarse := coarsePrediction
  fine := finePrediction
  coarseBelow := coarse_prediction_belowHalf
  fineAbove := fine_prediction_aboveHalf
  classificationDiffers := observer_geometry_flips_prediction_class
  coarseFactorization := coarseProbabilityFactorization
  coarseNoAuthority := coarse_prediction_not_authority_complete
  fineNoAuthority := fine_prediction_not_authority_complete

end
end M12FlowSharePredictionConsumerRegression
end Society
end ProcessGame
end SaturationMonoid
