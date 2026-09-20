import H0mework.Physics.Coframe.EinsteinCartanSpatialSkewCoframeActualResponseOperator
import H0mework.Physics.CurrentAction.LorentzDualResponse

/-!
# S9-C3h200i: source/action-generated pre-contorsion spatial profile

The proof-free P506/L0 source first generates its nonzero matter seed and the
current-state direct complete-P286 actual.  Before any Einstein--Cartan
contorsion is installed, the full Lorentz action on that same actual generates
eighteen spatial algebraic coordinates.  The actual 18-to-18 simple-`B`
principal proved in the dependency-light companion module then uniquely
generates a spatial skew-coframe jet and a smooth nondegenerate local actual:

```text
exact P506/L0 source
→ source-generated matter Cauchy state
→ pre-contorsion linear-Plebanski + direct complete-P286 actual
→ eighteen spatial Lorentz action coordinates
→ unique spatial skew-coframe jet
→ actual affine coframe profile
→ B := II⁺(coframe).
```

The omitted temporal six coordinates are not supplied to the constructor;
the spatial principal predicts them.  Consequently temporal Lorentz Gauss
remains a downstream independent acceptance gate.

This checkpoint is a local spatial-profile actual producer.  The spatial jet
is not a coframe time velocity, the retained P286 fields do not transport an
old P286 equation receipt across the new coframe, and this module does not
claim a next-current write, constraint tangency, an integral curve, or a
continuous flow.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineConnectionSectorSourceBalance
open StageNineCurrentCanonicalFullActionLorentzDualResponse
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEinsteinCartanSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpatialSkewCoframeActualResponseOperator
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineConjugateMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

abbrev PreContorsionP286Actual : StageNineHolonomicConfiguration :=
  currentCanonicalGravityPreservingP286Actual positiveSmoothUnifiedSource
    positiveSourceTargetMatterCauchyState 0

theorem preContorsionP286Actual_coframe_one (point : BasePoint) :
    PreContorsionP286Actual.coframe point = 1 := by
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveSourceTargetMatterCauchyState 0)).coframe point = 1
  rw [currentP286CompleteActionResponseOperator_coframe]
  unfold currentCanonicalFullActionBaseActual
    currentFullSynchronizedCompleteP286BaseActual
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe]
  simp [positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

@[simp] theorem preContorsionP286Actual_gravityConnection_origin :
    PreContorsionP286Actual.gravityConnection 0 = 0 := by
  change
    (currentP286CompleteActionResponseOperator positiveSmoothUnifiedSource
      (currentCanonicalFullActionBaseActual positiveSmoothUnifiedSource
        positiveSourceTargetMatterCauchyState 0)).gravityConnection 0 = 0
  rw [currentP286CompleteActionResponseOperator_gravityConnection]
  change
    (sourceActionGeneratedLinearPlebanskiJointLocalActualLift
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      ).gravityConnection 0 = 0
  rw [sourceActionGeneratedLinearPlebanskiJointLocalActualLift_initialConnection]
  simp [positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

@[simp] theorem preContorsionP286Actual_matter_origin :
    PreContorsionP286Actual.matter 0 = diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedMatterLocalActualLift positiveSmoothUnifiedSource
      positiveSourceTargetMatterCauchyState 0).matter 0 =
      diracSpinTwoMatterProbe
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  exact positiveSourceTargetMatterCauchyState_matter

@[simp] theorem preContorsionP286Actual_conjugateMatter_origin :
    PreContorsionP286Actual.conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  change
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      ).conjugateMatter 0 = diracSpinZeroMatterCoordinate
  rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
  exact positiveSourceTargetMatterCauchyState_conjugate

theorem preContorsionP286Actual_smooth : PreContorsionP286Actual.Smooth := by
  apply currentP286CompleteActionResponseOperator_smooth
  exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_smooth
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

theorem preContorsionP286Actual_gravityBFAlgebraic_zero
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient PreContorsionP286Actual direction 0 =
      0 := by
  have curvatureDirectionZero :
      lorentzConnectionAlgebraicCurvatureDirection
          PreContorsionP286Actual direction 0 = 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [preContorsionP286Actual_gravityConnection_origin]
    simp
  unfold lorentzGravityBFAlgebraicCoefficient
  rw [curvatureDirectionZero]
  simp [gravityBFCurvatureIncrementDensity, gravityCoframePairing,
    coframeTwoFormMetricPairing]

/-- The actual algebraic Lorentz action target on the eighteen spatial
connection directions of the pre-contorsion P286 actual. -/
def preContorsionSpatialLorentzActionTarget :
    LorentzSpatialBivectorDirection :=
  fun spatial internalPair =>
    lorentzConnectionAlgebraicSpinCurrentCoefficient
      positiveSmoothUnifiedSource PreContorsionP286Actual
      (lorentzBivectorOneFormCoordinateDirection spatial.succ internalPair) 0

private theorem spatialDirection_zero_one :
    lorentzBivectorOneFormCoordinateDirection (0 : Fin 3).succ 1 =
      canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1) := by
  funext formDirection internalPair
  refine Fin.cases ?_ (fun spatial => ?_) formDirection
  · change 0 =
      canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)
        canonicalLorentzianTimeDirection internalPair
    rw [canonicalLorentzSpatialBivectorOneForm_time]
    rfl
  · rw [canonicalLorentzSpatialBivectorOneForm_spatial]
    fin_cases spatial <;> fin_cases internalPair <;>
      simp [lorentzBivectorOneFormCoordinateDirection, spinDirection]

theorem preContorsionSpatialLorentzActionTarget_zero_one :
    preContorsionSpatialLorentzActionTarget 0 1 = 1 / 2 := by
  have matterHalf :
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          PreContorsionP286Actual
          (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
        1 / 2 :=
    spinProbeResponse_eq_half_of_origin PreContorsionP286Actual
      (preContorsionP286Actual_coframe_one 0)
      preContorsionP286Actual_matter_origin
      preContorsionP286Actual_conjugateMatter_origin
  unfold preContorsionSpatialLorentzActionTarget
  rw [spatialDirection_zero_one,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    preContorsionP286Actual_gravityBFAlgebraic_zero, matterHalf]
  ring

def generatedSpatialSkewCoframeJet : LorentzSpatialBivectorDirection :=
  einsteinCartanSpatialSkewCoframeCoordinates
    preContorsionSpatialLorentzActionTarget

theorem generatedSpatialSkewCoframeJet_reaches_actionTarget :
    spatialSkewCoframeActualBFDivergenceCoordinates
        generatedSpatialSkewCoframeJet =
      preContorsionSpatialLorentzActionTarget := by
  exact einsteinCartanSpatialSkewCoframeCoordinates_rightInverse _

theorem generatedSpatialSkewCoframeJet_unique
    (candidate : LorentzSpatialBivectorDirection)
    (reaches :
      spatialSkewCoframeActualBFDivergenceCoordinates candidate =
        preContorsionSpatialLorentzActionTarget) :
    candidate = generatedSpatialSkewCoframeJet := by
  apply spatialSkewCoframeActualBFDivergenceCoordinates_bijective.injective
  rw [reaches, generatedSpatialSkewCoframeJet_reaches_actionTarget]

theorem generatedSpatialSkewCoframeJet_nonzero :
    generatedSpatialSkewCoframeJet ≠ 0 := by
  intro jetZero
  have responseZero := congrArg
    (fun response : LorentzSpatialBivectorDirection => response 0 1)
    generatedSpatialSkewCoframeJet_reaches_actionTarget
  rw [jetZero] at responseZero
  simp [spatialSkewCoframeActualBFDivergenceCoordinates,
    spatialSkewCoframeJetLift,
    skewCoframeActualBFDivergenceCoordinates_apply,
    skewCoframeDivergenceResponseCoordinates,
    preContorsionSpatialLorentzActionTarget_zero_one] at responseZero

def preContorsionSpatialProfileActual : StageNineHolonomicConfiguration :=
  spatialSkewCoframeActualOn PreContorsionP286Actual
    generatedSpatialSkewCoframeJet

@[simp] theorem preContorsionSpatialProfileActual_coframe_origin :
    preContorsionSpatialProfileActual.coframe 0 = 1 := by
  exact spatialSkewCoframeActualOn_coframe_origin _ _

theorem preContorsionSpatialProfileActual_retains_gravityConnection :
    preContorsionSpatialProfileActual.gravityConnection =
      PreContorsionP286Actual.gravityConnection := by
  exact
    (spatialSkewCoframeActualOn_retains_fields PreContorsionP286Actual
      generatedSpatialSkewCoframeJet).1

theorem preContorsionSpatialProfileActual_retains_p286Fields :
    preContorsionSpatialProfileActual.gaugeConnection =
        PreContorsionP286Actual.gaugeConnection ∧
      preContorsionSpatialProfileActual.gaugeAuxiliary =
        PreContorsionP286Actual.gaugeAuxiliary := by
  have retained :=
    spatialSkewCoframeActualOn_retains_fields PreContorsionP286Actual
      generatedSpatialSkewCoframeJet
  exact ⟨retained.2.2.1, retained.2.2.2.1⟩

theorem preContorsionSpatialProfileActual_retains_matterFields :
    preContorsionSpatialProfileActual.matter =
        PreContorsionP286Actual.matter ∧
      preContorsionSpatialProfileActual.conjugateMatter =
        PreContorsionP286Actual.conjugateMatter := by
  have retained :=
    spatialSkewCoframeActualOn_retains_fields PreContorsionP286Actual
      generatedSpatialSkewCoframeJet
  exact ⟨retained.2.2.2.2.2.1, retained.2.2.2.2.2.2⟩

theorem preContorsionSpatialProfileActual_gravityAuxiliary_generated :
    preContorsionSpatialProfileActual.gravityAuxiliary =
      fun point => physicalIIPlusBivector
        (preContorsionSpatialProfileActual.coframe point) := by
  exact spatialSkewCoframeActualOn_gravityAuxiliary_generated _ _

theorem preContorsionSpatialProfileActual_smooth :
    preContorsionSpatialProfileActual.Smooth := by
  exact spatialSkewCoframeActualOn_smooth _
    preContorsionP286Actual_smooth _

theorem preContorsionSpatialProfileActual_nondegenerate :
    preContorsionSpatialProfileActual.Nondegenerate := by
  exact spatialSkewCoframeActualOn_nondegenerate _ _

theorem preContorsionSpatialProfileActual_origin_nondegenerate :
    Matrix.det (preContorsionSpatialProfileActual.coframe 0) ≠ 0 := by
  rw [preContorsionSpatialProfileActual_coframe_origin]
  simp

def preContorsionSpatialProfileActualBFDivergenceCoordinates :
    LorentzSpatialBivectorDirection :=
  spatialSkewCoframeActualOnBFDivergenceCoordinates
    PreContorsionP286Actual generatedSpatialSkewCoframeJet

theorem preContorsionSpatialProfileActualBFDivergenceCoordinates_eq_operator :
    preContorsionSpatialProfileActualBFDivergenceCoordinates =
      spatialSkewCoframeActualBFDivergenceCoordinates
        generatedSpatialSkewCoframeJet := by
  exact
    spatialSkewCoframeActualOnBFDivergenceCoordinates_eq_actualOperator _ _

theorem preContorsionSpatialProfileActual_reaches_actionTarget :
    preContorsionSpatialProfileActualBFDivergenceCoordinates =
      preContorsionSpatialLorentzActionTarget := by
  rw [preContorsionSpatialProfileActualBFDivergenceCoordinates_eq_operator]
  exact generatedSpatialSkewCoframeJet_reaches_actionTarget

/-- The six temporal BF-divergence coordinates remain predictions of the
already generated spatial target; they were not used to choose the jet. -/
theorem preContorsionSpatialProfileActual_temporalPrediction :
    spatialSkewCoframeActualOnFullBFDivergenceCoordinates
        PreContorsionP286Actual generatedSpatialSkewCoframeJet
        canonicalLorentzianTimeDirection =
      spatialSkewCoframeTemporalBFDivergencePrediction
        preContorsionSpatialLorentzActionTarget := by
  unfold generatedSpatialSkewCoframeJet
  exact spatialSkewCoframeActualOn_temporal_prediction _ _

/-! ## Spatial Lorentz action acceptance -/

@[simp] theorem preContorsionSpatialProfileActual_gravityConnection_origin :
    preContorsionSpatialProfileActual.gravityConnection 0 = 0 := by
  rw [preContorsionSpatialProfileActual_retains_gravityConnection,
    preContorsionP286Actual_gravityConnection_origin]

theorem preContorsionSpatialProfileActual_gravityBFAlgebraic_zero
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient
        preContorsionSpatialProfileActual direction 0 = 0 := by
  have curvatureDirectionZero :
      lorentzConnectionAlgebraicCurvatureDirection
          preContorsionSpatialProfileActual direction 0 = 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [preContorsionSpatialProfileActual_gravityConnection_origin]
    simp
  unfold lorentzGravityBFAlgebraicCoefficient
  rw [curvatureDirectionZero]
  simp [gravityBFCurvatureIncrementDensity, gravityCoframePairing,
    coframeTwoFormMetricPairing]

theorem preContorsionSpatialProfileActual_matterSpin_eq_base
    (direction : LorentzBivectorOneForm) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        preContorsionSpatialProfileActual direction 0 =
      lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        PreContorsionP286Actual direction 0 := by
  have spinCoordinatesEq :
      actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          preContorsionSpatialProfileActual 0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          PreContorsionP286Actual 0 := by
    exact actualMatterSpinActionCoordinates_eq_of_origin_fields
      positiveSmoothUnifiedSource preContorsionSpatialProfileActual
      PreContorsionP286Actual
      (preContorsionSpatialProfileActual_coframe_origin.trans
        (preContorsionP286Actual_coframe_one 0).symm)
      (congrFun preContorsionSpatialProfileActual_retains_matterFields.1 0)
      (congrFun preContorsionSpatialProfileActual_retains_matterFields.2 0)
  have spinDualEq :
      einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          preContorsionSpatialProfileActual 0 =
        einsteinCartanMatterSpinActionDual positiveSmoothUnifiedSource
          PreContorsionP286Actual 0 := by
    apply einsteinCartanLorentzDual_eq_of_coordinate_eq
    intro formDirection internalPair
    exact congrFun (congrFun spinCoordinatesEq formDirection) internalPair
  exact DFunLike.congr_fun spinDualEq direction

theorem preContorsionSpatialProfileActual_algebraicAction_eq_base
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource preContorsionSpatialProfileActual
        direction 0 =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource PreContorsionP286Actual direction 0 := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    preContorsionSpatialProfileActual_gravityBFAlgebraic_zero,
    preContorsionP286Actual_gravityBFAlgebraic_zero,
    preContorsionSpatialProfileActual_matterSpin_eq_base]

/-- The generated profile closes all eighteen spatial Lorentz rows.  This is
producer-soundness for the spatial action equation; temporal Gauss remains
outside the constructor and is not claimed here. -/
theorem preContorsionSpatialProfileActual_spatialLorentzEuler_origin
    (spatial : Fin 3) (internalPair : Fin 6) :
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        preContorsionSpatialProfileActual
        (lorentzBivectorOneFormCoordinateDirection spatial.succ internalPair)
        0 = 0 := by
  rw [lorentzConnectionEulerLagrangeCoefficient,
    preContorsionSpatialProfileActual_algebraicAction_eq_base]
  change
    preContorsionSpatialLorentzActionTarget spatial internalPair -
        preContorsionSpatialProfileActualBFDivergenceCoordinates spatial
          internalPair =
      0
  have reached := congrFun
    (congrFun preContorsionSpatialProfileActual_reaches_actionTarget spatial)
    internalPair
  rw [reached]
  ring

/-! ## Exact producer law -/

/-- C3h200i records the source/action provenance, unique spatial principal,
and actual local profile without storing a temporal Gauss receipt. -/
structure PositiveP506MatterPreContorsionSpatialProfileActualLiftLaw
    (actual : StageNineHolonomicConfiguration) : Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  endpointEleven :
    positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
        canonicalSource_generatedLineage_height_pos = 11
  baseActual :
    PreContorsionP286Actual =
      currentCanonicalGravityPreservingP286Actual
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
  basePreContorsion : PreContorsionP286Actual.gravityConnection 0 = 0
  actionTargetGenerated : ∀ spatial internalPair,
    preContorsionSpatialLorentzActionTarget spatial internalPair =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource PreContorsionP286Actual
        (lorentzBivectorOneFormCoordinateDirection spatial.succ internalPair) 0
  principalBijective :
    Function.Bijective spatialSkewCoframeActualBFDivergenceCoordinates
  generatedJetResponse :
    spatialSkewCoframeActualBFDivergenceCoordinates
        generatedSpatialSkewCoframeJet =
      preContorsionSpatialLorentzActionTarget
  uniqueGeneratedJet : ∀ candidate,
    spatialSkewCoframeActualBFDivergenceCoordinates candidate =
        preContorsionSpatialLorentzActionTarget →
      candidate = generatedSpatialSkewCoframeJet
  nonzeroActionCoordinate :
    preContorsionSpatialLorentzActionTarget 0 1 = 1 / 2
  nonzeroGeneratedJet : generatedSpatialSkewCoframeJet ≠ 0
  actualPath : actual = preContorsionSpatialProfileActual
  retainedPrimitiveFields :
    SpatialSkewCoframeActualOnRetainedFields PreContorsionP286Actual actual
  coframeOrigin : actual.coframe 0 = 1
  gravityAuxiliaryGenerated :
    actual.gravityAuxiliary =
      fun point => physicalIIPlusBivector (actual.coframe point)
  smooth : actual.Smooth
  nondegenerate : actual.Nondegenerate
  spatialActionResponse :
    preContorsionSpatialProfileActualBFDivergenceCoordinates =
      preContorsionSpatialLorentzActionTarget
  spatialLorentzEuler : ∀ (spatial : Fin 3) (internalPair : Fin 6),
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        actual
        (lorentzBivectorOneFormCoordinateDirection spatial.succ internalPair)
        0 = 0
  temporalOutputPrediction :
    spatialSkewCoframeActualOnFullBFDivergenceCoordinates
        PreContorsionP286Actual generatedSpatialSkewCoframeJet
        canonicalLorentzianTimeDirection =
      spatialSkewCoframeTemporalBFDivergencePrediction
        preContorsionSpatialLorentzActionTarget

theorem positiveP506MatterPreContorsionSpatialProfileActualLift_realizes_C3h200i :
    PositiveP506MatterPreContorsionSpatialProfileActualLiftLaw
      preContorsionSpatialProfileActual := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      endpointEleven := positiveSmoothUnifiedSource_generates_endpoint_eleven
      baseActual := rfl
      basePreContorsion :=
        preContorsionP286Actual_gravityConnection_origin
      actionTargetGenerated := by intro spatial internalPair; rfl
      principalBijective :=
        spatialSkewCoframeActualBFDivergenceCoordinates_bijective
      generatedJetResponse :=
        generatedSpatialSkewCoframeJet_reaches_actionTarget
      uniqueGeneratedJet := generatedSpatialSkewCoframeJet_unique
      nonzeroActionCoordinate :=
        preContorsionSpatialLorentzActionTarget_zero_one
      nonzeroGeneratedJet := generatedSpatialSkewCoframeJet_nonzero
      actualPath := rfl
      retainedPrimitiveFields :=
        spatialSkewCoframeActualOn_retains_fields _ _
      coframeOrigin := preContorsionSpatialProfileActual_coframe_origin
      gravityAuxiliaryGenerated :=
        preContorsionSpatialProfileActual_gravityAuxiliary_generated
      smooth := preContorsionSpatialProfileActual_smooth
      nondegenerate := preContorsionSpatialProfileActual_nondegenerate
      spatialActionResponse :=
        preContorsionSpatialProfileActual_reaches_actionTarget
      spatialLorentzEuler :=
        preContorsionSpatialProfileActual_spatialLorentzEuler_origin
      temporalOutputPrediction :=
        preContorsionSpatialProfileActual_temporalPrediction }


end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterPreContorsionSpatialProfileActualLift
