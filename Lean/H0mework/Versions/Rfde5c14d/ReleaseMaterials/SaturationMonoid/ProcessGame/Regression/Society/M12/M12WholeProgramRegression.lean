/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Authority.SourceInstalledProbabilityRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Go.GoNormalFormProbabilityRegression

/-!
# M12 whole-program sink

The sink retains source-owned measure/fold/prediction seals, all normalization
boundary controls, the observer-geometry class flip, independent measure
sensitivity, the Go authority no-go, and both M11 boundary and M12 probability
faces at one literal root visit and generated next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12WholeProgramRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space Observer
open Probability Measure Kernel Consumer Authority

structure M12WholeProgramCertificate (horizon : Nat) where
  monthlyMeasure : SourceGeneratedFiniteMeasureAt
    M12GeneratedFlowMeasureFixture.monthlyMeasureCompiler
  uniformMeasure : SourceGeneratedFiniteMeasureAt
    M12GeneratedFlowMeasureFixture.uniformMeasureCompiler
  zeroMeasure : SourceGeneratedFiniteMeasureAt
    M12GeneratedFlowMeasureFixture.zeroMeasureCompiler
  flowPrediction :
    M12FlowSharePredictionConsumerRegression.FlowSharePredictionConsumerCertificate
  observerGeometryFlip :
    ObserverConditionedPredictionClass.ReadoutDiffers
      M12FlowSharePredictionConsumerRegression.coarsePrediction.classification
      M12FlowSharePredictionConsumerRegression.finePrediction.classification
  measureSensitivity :
    M12ObserverGeometryRegression.coarseMonthlyFold.readVisible
        .conditioned ≠
      M12ObserverGeometryRegression.coarseUniformFold.readVisible
        .conditioned
  nonemptyZeroMassUndefined :
    M12ZeroMassBoundaryRegression.coarseZeroFold.readVisible .conditioned =
        none ∧
      M12ZeroMassBoundaryRegression.coarseZeroFold.fibre .conditioned ≠ []
  positiveEmptyEventDefinedZero :
    M12ZeroMassBoundaryRegression.emptyEventMonthlyFold.readVisible
      .conditioned = some 0
  goProbability :
    M12GoNormalFormProbabilityRegression.GoNormalFormProbabilityCertificate
      horizon
  boundaryFace : SourceInstalledBoundaryMaintenanceAt
    M12SourceInstalledProbabilityRegression.jointBoundaryRenewal
  probabilityFace : SourceInstalledProbabilityAt
    M12SourceInstalledProbabilityRegression.jointProbabilityRenewal
  probabilityConsumer : SourceInstalledProbabilityConsumerAt probabilityFace
  bothFactorize :
    M12SourceInstalledProbabilityRegression.jointBoundaryRenewal.RootAnswerAndNextFactorizes ∧
      M12SourceInstalledProbabilityRegression.jointProbabilityRenewal.RootAnswerAndNextFactorizes
  sameWholeLedger :
    M12SourceInstalledProbabilityRegression.boundaryConsumer.wholeLedgerWriteBack =
      M12SourceInstalledProbabilityRegression.probabilityConsumer.wholeLedgerWriteBack
  uniqueGeneratedNext :
    M12SourceInstalledProbabilityRegression.boundaryConsumer.generatedNext =
        M12SourceInstalledProbabilityRegression.jointRoot.generatedNextCurrentAt
          M12SourceInstalledProbabilityRegression.jointVisit ∧
      M12SourceInstalledProbabilityRegression.probabilityConsumer.generatedNext =
        M12SourceInstalledProbabilityRegression.jointRoot.generatedNextCurrentAt
          M12SourceInstalledProbabilityRegression.jointVisit ∧
      M12SourceInstalledProbabilityRegression.boundaryConsumer.generatedNext =
        M12SourceInstalledProbabilityRegression.probabilityConsumer.generatedNext
  derivedProbability : probabilityFace.normalizedProbability =
    some ((1 : ℚ≥0) / 3)
  derivedPrediction : probabilityFace.predictionClassification =
    some ObserverConditionedPredictionClass.belowHalf
  noAuthorityComplete : ¬ Nonempty (AuthorityCompleteReadoutAt
    M12GeneratedFlowObserverFixture.coarseObserver
    probabilityFace.probabilityReadout)

def m12WholeProgramConsumer (horizon : Nat) :
    M12WholeProgramCertificate horizon where
  monthlyMeasure := M12GeneratedFlowMeasureFixture.monthlyMeasure
  uniformMeasure := M12GeneratedFlowMeasureFixture.uniformMeasure
  zeroMeasure := M12GeneratedFlowMeasureFixture.zeroMeasure
  flowPrediction :=
    M12FlowSharePredictionConsumerRegression.flowSharePredictionDirectConsumer
  observerGeometryFlip :=
    M12FlowSharePredictionConsumerRegression.observer_geometry_flips_prediction_class
  measureSensitivity :=
    M12ObserverGeometryRegression.measure_compiler_cannot_be_deleted
  nonemptyZeroMassUndefined :=
    M12ZeroMassBoundaryRegression.nonempty_allZero_fibre_is_none
  positiveEmptyEventDefinedZero :=
    M12ZeroMassBoundaryRegression.positive_fibre_empty_event_is_some_zero
  goProbability :=
    M12GoNormalFormProbabilityRegression.goNormalFormProbabilityDirectConsumer
      horizon
  boundaryFace := M12SourceInstalledProbabilityRegression.jointBoundaryMaintenance
  probabilityFace := M12SourceInstalledProbabilityRegression.jointProbability
  probabilityConsumer :=
    M12SourceInstalledProbabilityRegression.probabilityConsumer
  bothFactorize :=
    M12SourceInstalledProbabilityRegression.both_faces_factorize_same_joint_root
  sameWholeLedger :=
    M12SourceInstalledProbabilityRegression.wholeLedgerWriteBack_eq
  uniqueGeneratedNext :=
    M12SourceInstalledProbabilityRegression.unique_generatedNext
  derivedProbability :=
    M12SourceInstalledProbabilityRegression.derived_probability_exact
  derivedPrediction :=
    M12SourceInstalledProbabilityRegression.derived_prediction_belowHalf
  noAuthorityComplete :=
    M12SourceInstalledProbabilityRegression.derived_probability_not_authority_complete

end
end M12WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
