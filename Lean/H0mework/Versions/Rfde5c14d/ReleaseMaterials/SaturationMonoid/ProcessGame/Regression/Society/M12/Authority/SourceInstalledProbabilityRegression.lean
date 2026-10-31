/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.BoundaryMaintenanceRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M12.Statistics.FlowSharePredictionConsumerRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Authority.SourceInstalledProbability

/-!
# M12 joint source-installed probability regression

The M11 boundary-maintenance renewal is inherited into one literal joint
authority source before a second probability renewal component is installed.
Both faces then run at the same temporal visit, consume the same singleton
root row and whole-ledger occurrence, and read the same root-generated next.

The probability payload contains only the proof-indexed M12 restriction.  Its
numeric probability and prediction class remain derived readouts.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12SourceInstalledProbabilityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space Observer
open Probability Measure Kernel Consumer Authority

abbrev LocalGame := M11BoundaryMaintenanceRegression.LocalGame
abbrev LocalSeed := M11BoundaryMaintenanceRegression.LocalSeed
abbrev LocalSeedAt := M11BoundaryMaintenanceRegression.LocalSeedAt
abbrev localFocalSeed := M11BoundaryMaintenanceRegression.localFocalSeed

abbrev authorityFold :=
  M12ObserverGeometryRegression.coarseUniformFold
abbrev authorityPrediction :=
  M12FlowSharePredictionConsumerRegression.uniformPrediction
abbrev Visible := M12GeneratedFlowObserverFixture.Visible

/-! ## Probability component before joint emission -/

/-- Literal fixed probability restriction indexed by the generated fold,
visible and prediction consumer. -/
def probabilityRestriction : ProbabilityRestrictionAt
    authorityFold (.conditioned : Visible) authorityPrediction
      localFocalSeed where
  seed_eq_focal := rfl

abbrev ProbabilityConsumerAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  ProbabilityRestrictionAt authorityFold (.conditioned : Visible)
    authorityPrediction seed

abbrev ProbabilityDispositionAt
    (_seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  PUnit

/-- Second renewal law compiled over the already boundary-enabled M11 source. -/
def probabilityLaw : SourceNativeRenewalProjectionLaw
    (M11BoundaryMaintenanceRegression.authoritySource
      |>.restructuringSource.toLedgerSource)
    LocalGame LocalSeed LocalSeedAt
    ProbabilityConsumerAt ProbabilityDispositionAt where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  compile := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support
    cases event
    exact RootRestrictedRenewalPayloadAt.generate
      localFocalSeed probabilityRestriction PUnit.unit
      M10OccurrenceCapacityRootSourceFixture.entry
      M10OccurrenceCapacityRootSourceFixture.sourceRow
      M10OccurrenceCapacityRootSourceFixture.successor
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive _seedEq
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport
    cases rightSupport
    cases leftEvent
    cases rightEvent
    rfl

/-- Both renewal coordinates are present before the literal joint emitter. -/
def jointAuthoritySource : SourceNativeAuthoritySource
    M10OccurrenceCapacityRootSourceFixture.N
    M10OccurrenceCapacityRootSourceFixture.V :=
  withRenewalProjection
    M11BoundaryMaintenanceRegression.authoritySource probabilityLaw

/-- One regression root reusing the M11 ledger source and emitter. -/
def jointRoot : SourceNativeLivingRootClosure
    M10OccurrenceCapacityRootSourceFixture.N
    M10OccurrenceCapacityRootSourceFixture.V where
  source :=
    { base := jointAuthoritySource
      terminalHandoff := jointAuthoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := M10OccurrenceCapacityRootSourceFixture.emitted
  compiler_commutes := fun _ => rfl

def jointVisit : SourceNativeTemporalVisitAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite jointRoot.toAuthoritativeRoot.toRoot.initialVisit

/-! ## Both projection coordinates in the joint inventory -/

/-- Existing M11 boundary component transported through the second renewal
uplift. -/
def boundaryInstallationInJoint : SourceNativeProjectionLaw.InstallationAt
    M11BoundaryMaintenanceRegression.renewalLaw.toProjectionLaw
    jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  M11BoundaryMaintenanceRegression.installation.trans
    (inheritedByRenewal
      M11BoundaryMaintenanceRegression.authoritySource probabilityLaw)

/-- New probability component of the joint projection inventory. -/
def probabilityInstallationInJoint :
    SourceNativeProjectionLaw.InstallationAt probabilityLaw.toProjectionLaw
      jointRoot.toAuthoritativeRoot.source.projectionLaw :=
  renewalComponent
    M11BoundaryMaintenanceRegression.authoritySource probabilityLaw

def jointBoundaryRecognition : SourceNativeBoundaryMaintenanceRecognitionAt
    jointRoot M11BoundaryMaintenanceRegression.maintenanceSocialSpace
      M11BoundaryMaintenanceRegression.DebitP
      M11BoundaryMaintenanceRegression.DebitProcess
      M11BoundaryMaintenanceRegression.MaintenanceDispositionAt where
  law := M11BoundaryMaintenanceRegression.renewalLaw
  installation := boundaryInstallationInJoint

def jointProbabilityRecognition : SourceNativeProbabilityRecognitionAt
    jointRoot authorityFold (.conditioned : Visible) authorityPrediction
      ProbabilityDispositionAt where
  law := probabilityLaw
  installation := probabilityInstallationInJoint

/-- Both installed faces are generated at the exact same joint visit. -/
def jointBoundaryRenewal : SourceInstalledRenewalAt
    jointBoundaryRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def jointProbabilityRenewal : SourceInstalledRenewalAt
    jointProbabilityRecognition jointVisit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def jointBoundaryMaintenance :
    SourceInstalledBoundaryMaintenanceAt jointBoundaryRenewal :=
  sourceInstalledBoundaryMaintenance jointBoundaryRenewal

def jointProbability :
    SourceInstalledProbabilityAt jointProbabilityRenewal :=
  sourceInstalledProbability jointProbabilityRenewal

def boundaryConsumer :
    BoundaryMaintenanceConsumerAt jointBoundaryMaintenance :=
  jointBoundaryMaintenance.independentConsumer

/-- The independent probability consumer stores only indexed seals and root
readouts; numeric probability and prediction class are absent from its fields. -/
def probabilityConsumer :
    SourceInstalledProbabilityConsumerAt jointProbability :=
  jointProbability.independentConsumer

/-! ## Same occurrence, whole ledger and generated next -/

theorem joint_emitter_is_M11_emitter :
    HEq jointRoot.emitted M11BoundaryMaintenanceRegression.root.emitted :=
  HEq.rfl

theorem both_payloads_use_literal_same_row :
    jointBoundaryRenewal.payload.sourceEntry =
        jointProbabilityRenewal.payload.sourceEntry ∧
      HEq jointBoundaryRenewal.payload.selectedRow
        jointProbabilityRenewal.payload.selectedRow ∧
      HEq jointBoundaryRenewal.payload.successor
        jointProbabilityRenewal.payload.successor :=
  ⟨rfl, HEq.rfl, HEq.rfl⟩

theorem both_faces_factorize_same_joint_root :
    jointBoundaryRenewal.RootAnswerAndNextFactorizes ∧
      jointProbabilityRenewal.RootAnswerAndNextFactorizes :=
  ⟨boundaryConsumer.rootFactorization,
    probabilityConsumer.rootFactorization⟩

/-- Both consumers read the exact same whole-ledger write-back value. -/
theorem wholeLedgerWriteBack_eq :
    boundaryConsumer.wholeLedgerWriteBack =
      probabilityConsumer.wholeLedgerWriteBack :=
  rfl

/-- Neither local face emits a next; both values are definitionally the one
joint-root generated next. -/
theorem unique_generatedNext :
    boundaryConsumer.generatedNext =
        jointRoot.generatedNextCurrentAt jointVisit ∧
      probabilityConsumer.generatedNext =
        jointRoot.generatedNextCurrentAt jointVisit ∧
      boundaryConsumer.generatedNext = probabilityConsumer.generatedNext :=
  ⟨boundaryConsumer.generatedNext_eq,
    probabilityConsumer.generatedNext_eq, rfl⟩

theorem probability_consumer_exact_indices :
    probabilityConsumer.normalizedFold = authorityFold ∧
      probabilityConsumer.conditionedVisible = (.conditioned : Visible) ∧
      HEq probabilityConsumer.predictionConsumer authorityPrediction :=
  ⟨rfl, rfl, HEq.rfl⟩

/- The independent authority consumer intentionally exposes no cached
numeric probability or prediction-classification field. -/
/-- error: Invalid field `normalizedProbability` -/
#guard_msgs (substring := true) in
#check probabilityConsumer.normalizedProbability

/-- error: Invalid field `predictionClassification` -/
#guard_msgs (substring := true) in
#check probabilityConsumer.predictionClassification

/-! ## Derived probability readouts -/

theorem derived_probability_exact :
    jointProbability.normalizedProbability =
      some ((1 : ℚ≥0) / 3) := by
  change authorityPrediction.probability = some ((1 : ℚ≥0) / 3)
  exact M12FlowSharePredictionConsumerRegression.uniform_probability_exact

theorem derived_prediction_belowHalf :
    jointProbability.predictionClassification =
      some ObserverConditionedPredictionClass.belowHalf := by
  change authorityPrediction.classification =
    some ObserverConditionedPredictionClass.belowHalf
  exact M12FlowSharePredictionConsumerRegression.uniform_prediction_belowHalf

theorem derived_probability_not_authority_complete :
    ¬ Nonempty (AuthorityCompleteReadoutAt
      M12GeneratedFlowObserverFixture.coarseObserver
      jointProbability.probabilityReadout) :=
  jointProbability.noAuthorityCompleteProbability
    M12GeneratedFlowObserverFixture.coarseKernelPair

/-! ## Negative controls -/

/-- Bare numeric or prediction-class readouts do not elaborate as the
pre-emitter restriction carrier. -/
theorem bare_readouts_are_not_probability_restrictions : True := by
  fail_if_success
    exact (authorityPrediction.probability : ProbabilityRestrictionAt
      authorityFold (.conditioned : Visible) authorityPrediction
        localFocalSeed)
  fail_if_success
    exact (authorityPrediction.classification : ProbabilityRestrictionAt
      authorityFold (.conditioned : Visible) authorityPrediction
        localFocalSeed)
  trivial

/-- A real nonfocal exact source seed cannot be repaired by any bare readout. -/
def nonFocalSeed : SourceSeed
    M10OccurrenceCapacityProcessFixture.occurrenceOf
    LocalSeed LocalSeedAt LocalGame.source :=
  ⟨true,
    ⟨Capacity.stateAt LocalGame
        M10OccurrenceCapacityProcessFixture.middlePosition,
      Capacity.stateAt_mem LocalGame
        M10OccurrenceCapacityProcessFixture.middlePosition,
      rfl⟩⟩

theorem nonFocalSeed_ne_focal : nonFocalSeed ≠ localFocalSeed := by
  intro equality
  have seedEquality : true = false := congrArg Subtype.val equality
  cases seedEquality

theorem nonfocal_restriction_is_empty :
    IsEmpty (ProbabilityRestrictionAt authorityFold
      (.conditioned : Visible) authorityPrediction nonFocalSeed) :=
  ⟨fun restriction =>
    nonFocalSeed_ne_focal restriction.seed_eq_focal⟩

/-- A face installed at the joint root cannot be recast as an installation at
the already-emitted M11 sibling visit. -/
theorem postEmitter_sibling_visit_rejected : True := by
  fail_if_success
    exact (jointProbabilityRenewal : SourceInstalledRenewalAt
      jointProbabilityRecognition M11BoundaryMaintenanceRegression.visit)
  trivial

end
end M12SourceInstalledProbabilityRegression
end Society
end ProcessGame
end SaturationMonoid
