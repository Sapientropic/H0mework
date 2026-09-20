import H0mework.Physics.Lorentz.CartanLorentzBFMomentumResponse
import H0mework.Physics.Matter.GeneratedMatter
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance

/-!
# S9-C3h107: source-generated matter spin action update

The Stage-8 proof-free source already generates an actual finite-link matter
jet.  This module rebases its source dual to the canonical time-link target
through the same actual mother-link representation, uses the target matter
and transported dual as a parameter-free Cauchy seed, and then lets the
existing matter, dual, Lorentz, and BF actions generate the local response.

The order is strictly forward:

```text
primitive P506/L0 source
→ actual Stage-8 matter link
→ identity-link target rebase in the existing representation
→ primitive Cauchy seed
→ action-generated matter/dual local actual lift
→ full Lorentz canonical update
→ spin-current and momentum readout.
```

For the fixed representation coordinate with spatial form index `1` and
internal bivector `(0,2)`, the generated matter spin response and the
Lorentz BF-momentum update are both `1/2`.  The coefficient is calculated
from the existing gamma matrices and source amplitude; it is not a source
slot, ansatz coefficient, target endpoint, residual inverse, or supplied
certificate.  Residual laws remain downstream acceptance.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceGeneratedMatterSpinActionUpdate

open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open StageNineCanonicalCauchyState
open StageNineBlockwiseConstitutive
open StageNineCartanLorentzBFMomentumResponse
open StageNineConnectionSectorSourceBalance
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineScalarActionCanonicalMomentumUpdate
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink

noncomputable section

set_option autoImplicit false

def targetRebasedConjugateMatter
    (link : SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  jet.sourceConjugateField.comp (diracExteriorLinkAction link)

theorem targetRebasedConjugateMatter_pairing
    (link : SU7MotherFundamentalLink)
    (jet : DiracExteriorMatterLinkJet)
    (matter : DiracExteriorMatterCarrier) :
    targetRebasedConjugateMatter link jet matter =
      jet.sourceConjugateField (diracExteriorLinkAction link matter) :=
  rfl

def canonicalTargetRebasedConjugateMatter
    (source : SmoothUnifiedSource) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  targetRebasedConjugateMatter
    ((motherLinkFamilyOfConnection zeroMotherGaugeConnection) 0)
    (sourceGeneratedMatterJet source.stageEight)

theorem canonicalTargetRebasedConjugateMatter_eq_source
    (source : SmoothUnifiedSource) :
    canonicalTargetRebasedConjugateMatter source =
      (sourceGeneratedMatterJet source.stageEight).sourceConjugateField := by
  rw [canonicalTargetRebasedConjugateMatter,
    zeroMotherLinkFamily_eq_identity]
  simp [identityFundamentalLinkFamily, targetRebasedConjugateMatter,
    diracExteriorLinkAction_one]

def sourceTargetMatterCauchyState
    (source : SmoothUnifiedSource) : StageNineCauchyState :=
  { positivePhaseProbeCauchyState with
    matter := fun _ =>
      (sourceGeneratedMatterJet source.stageEight).targetField
        0
    conjugateMatter := fun _ =>
      canonicalTargetRebasedConjugateMatter source }

theorem sourceTargetMatterCauchyState_pairing
    (source : SmoothUnifiedSource)
    (space : StageNineSpatialPoint) :
    (sourceTargetMatterCauchyState source).conjugateMatter space
        ((sourceTargetMatterCauchyState source).matter space) =
      (sourceGeneratedMatterJet source.stageEight).sourceConjugateField
        (diracExteriorLinkAction
          ((motherLinkFamilyOfConnection zeroMotherGaugeConnection) 0)
          ((sourceGeneratedMatterJet source.stageEight).targetField 0)) := by
  rfl

def positiveSourceTargetMatterCauchyState : StageNineCauchyState :=
  sourceTargetMatterCauchyState positiveSmoothUnifiedSource

def positiveSourceTargetMatterActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedJointLocalActualLift
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

def positiveSourceTargetMatterGravityGaugeActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedGravityGaugeLocalActualLift
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState space

@[simp] theorem positiveSourceTargetMatterCauchyState_matter :
    positiveSourceTargetMatterCauchyState.matter 0 =
      diracSpinTwoMatterProbe := by
  simp [positiveSourceTargetMatterCauchyState,
    sourceTargetMatterCauchyState, sourceGeneratedMatterJet,
    sourceMatterAmplitude, positiveSmoothUnifiedSource,
    canonicalSource_physicalPhaseAmplitude,
    ]

@[simp] theorem positiveSourceTargetMatterCauchyState_conjugate :
    positiveSourceTargetMatterCauchyState.conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  simp [positiveSourceTargetMatterCauchyState,
    sourceTargetMatterCauchyState, sourceGeneratedMatterJet,
    sourceMatterAmplitude, positiveSmoothUnifiedSource,
    canonicalSource_physicalPhaseAmplitude,
    canonicalTargetRebasedConjugateMatter_eq_source]

def spinDirection
    (spatial : Fin 3) (pair : Fin 6) :
    LorentzSpatialBivectorDirection :=
  fun candidateSpatial candidatePair =>
    if candidateSpatial = spatial ∧ candidatePair = pair then 1 else 0

set_option linter.unusedSimpArgs false in
theorem spinProbeResponse_eq_half_of_origin
    (configuration : StageNineHolonomicConfiguration)
    (coframeOrigin : configuration.coframe 0 = 1)
    (matterOrigin : configuration.matter 0 = diracSpinTwoMatterProbe)
    (conjugateOrigin :
      configuration.conjugateMatter 0 = diracSpinZeroMatterCoordinate) :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        configuration
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      1 / 2 := by
  have directionOne :
      canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1) 1 =
        spinDirection 0 1 0 := by
    rfl
  have directionTwo :
      canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1) 2 =
        spinDirection 0 1 1 := by
    rfl
  have directionThree :
      canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1) 3 =
        spinDirection 0 1 2 := by
    rfl
  have directionZero :
      canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1) 0 = 0 := by
    rfl
  simp [lorentzMatterSpinSourceCoefficient,
    coframeOrigin, matterOrigin, conjugateOrigin,
    positiveSmoothUnifiedSource, spinDirection,
    matterGaugeConnectionFirstVariationDensity,
    matterGaugeConnectionVariationVector,
    matterGaugeKineticSum,
    holonomicMatterLorentzConnectionVariation,
    diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    generatedVolumeDensity, toContinuumPointField,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm,
    Fin.sum_univ_four, Fin.sum_univ_six,
    pairFirst, pairSecond, lorentzBivectorFirst,
    lorentzBivectorSecond, minkowskiInternalSign,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    inverseCoframeDiracGamma,
    inverseCoframeDiracGamma_identity,
    diracMatrixMatterAction,
    diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate_probe,
    directionZero, directionOne, directionTwo, directionThree,
    Matrix.mul_apply]

theorem positiveSourceTargetMatterActual_matterSpin_eq_half :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        positiveSourceTargetMatterActual
        (canonicalLorentzSpatialBivectorOneForm
          (spinDirection 0 1)) 0 =
      1 / 2 := by
  apply spinProbeResponse_eq_half_of_origin
  · rfl
  · change
      (sourceActionGeneratedMatterLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        0).matter 0 = diracSpinTwoMatterProbe
    rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
    exact positiveSourceTargetMatterCauchyState_matter
  · change
      (sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        0).conjugateMatter 0 = diracSpinZeroMatterCoordinate
    rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
    exact positiveSourceTargetMatterCauchyState_conjugate

theorem positiveSourceTargetMatterGravityGaugeActual_space_independent
    (space : StageNineSpatialPoint) :
    positiveSourceTargetMatterGravityGaugeActual space =
      positiveSourceTargetMatterGravityGaugeActual 0 := by
  unfold positiveSourceTargetMatterGravityGaugeActual
  rw [positiveSourceTargetMatterCauchyState,
    sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm]
  ext <;>
    simp [positiveProbeCauchyStateNormalForm,
      sourceActionGeneratedGravityGaugeLocalActualLift,
      sourceGeneratedP286ActionLocalActualLift,
      actionGeneratedGravityCurvature,
      actionGeneratedGravityAuxiliary,
      sourceGeneratedP286ActionLocalConnection,
      sourceGeneratedP286ActionLocalConnectionCoordinate,
      sourceGeneratedP286ActionLocalIncrement,
      sourceGeneratedP286ActionLocalConnectionJet,
      actionGeneratedP286ExteriorDerivativeCoordinate,
      actionGeneratedP286Curvature,
      cauchyP286SpatialConnectionDerivativeCoordinate]

theorem positiveSourceTargetMatter_lorentzSpatialBFMomentumDivergence_zero
    (direction : LorentzSpatialBivectorDirection) :
    sourceActionGeneratedLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
        direction = 0 := by
  unfold sourceActionGeneratedLorentzSpatialBFMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  have momentumFieldConstant :
      (sourceActionGeneratedLorentzBFMomentumEvaluation
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        derivativeDirection.succ · direction) =
      fun _ =>
        sourceActionGeneratedLorentzBFMomentumEvaluation
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
          derivativeDirection.succ 0 direction := by
    funext space
    unfold sourceActionGeneratedLorentzBFMomentumEvaluation
    rw [show
      sourceActionGeneratedGravityGaugeLocalActualLift
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
          space =
        positiveSourceTargetMatterGravityGaugeActual space by rfl]
    rw [positiveSourceTargetMatterGravityGaugeActual_space_independent]
    rfl
  rw [momentumFieldConstant]
  simp

theorem positiveSourceTargetMatterGravityGaugeActual_matterSpin_eq_half :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        (positiveSourceTargetMatterGravityGaugeActual 0)
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      1 / 2 := by
  apply spinProbeResponse_eq_half_of_origin
  · rfl
  · change positiveSourceTargetMatterCauchyState.matter 0 =
      diracSpinTwoMatterProbe
    exact positiveSourceTargetMatterCauchyState_matter
  · exact positiveSourceTargetMatterCauchyState_conjugate

theorem matterSpin_zero_of_matter_origin_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (matterOrigin : configuration.matter 0 = 0) :
    lorentzMatterSpinSourceCoefficient source configuration direction 0 =
      0 := by
  unfold lorentzMatterSpinSourceCoefficient
    holonomicMatterLorentzConnectionVariation
  rw [matterOrigin]
  simp [matterGaugeConnectionFirstVariationDensity,
    matterGaugeConnectionVariationVector, matterGaugeKineticSum]

theorem positiveGravityGaugeLocalActualLift_algebraicSpin_eq_zero :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource positiveGravityGaugeLocalActualLift
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      0 := by
  have velocityZero :=
    congrFun positiveLorentzSpatialBFMomentumVelocity_zero
      (spinDirection 0 1)
  change
    lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource positiveGravityGaugeLocalActualLift
          (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 -
        sourceActionGeneratedLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
          (spinDirection 0 1) =
      0 at velocityZero
  rw [positiveLorentzSpatialBFMomentumDivergence_zero] at velocityZero
  linarith

theorem positiveGravityGaugeLocalActualLift_matterSpin_eq_zero :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        positiveGravityGaugeLocalActualLift
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      0 := by
  apply matterSpin_zero_of_matter_origin_zero
  exact positiveGravityGaugeLocalActualLift_matter_origin

theorem positiveGravityGaugeLocalActualLift_gravityBFAlgebraic_eq_zero :
    lorentzGravityBFAlgebraicCoefficient
        positiveGravityGaugeLocalActualLift
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      0 := by
  have sectors :=
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors
      positiveSmoothUnifiedSource positiveGravityGaugeLocalActualLift
      (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0
  rw [positiveGravityGaugeLocalActualLift_algebraicSpin_eq_zero,
    positiveGravityGaugeLocalActualLift_matterSpin_eq_zero] at sectors
  linarith

theorem positiveSourceTargetMatter_gravityBFAlgebraic_eq_positive :
    lorentzGravityBFAlgebraicCoefficient
        (positiveSourceTargetMatterGravityGaugeActual 0)
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      lorentzGravityBFAlgebraicCoefficient
        positiveGravityGaugeLocalActualLift
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 := by
  let newConfiguration := positiveSourceTargetMatterGravityGaugeActual 0
  let oldConfiguration := positiveGravityGaugeLocalActualLift
  have coframeEqual :
      newConfiguration.coframe 0 = oldConfiguration.coframe 0 := by
    rfl
  have auxiliaryEqual :
      newConfiguration.gravityAuxiliary 0 =
        oldConfiguration.gravityAuxiliary 0 := by
    rfl
  have connectionEqual :
      newConfiguration.gravityConnection 0 =
        oldConfiguration.gravityConnection 0 := by
    rfl
  have curvatureEqual :
      lorentzConnectionAlgebraicCurvatureDirection newConfiguration
          (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
        lorentzConnectionAlgebraicCurvatureDirection oldConfiguration
          (canonicalLorentzSpatialBivectorOneForm
            (spinDirection 0 1)) 0 := by
    funext internalPair spacetimePair
    unfold lorentzConnectionAlgebraicCurvatureDirection
      lorentzConnectionAlgebraicCurvatureVariation
    rw [connectionEqual]
  have volumeEqual :
      generatedVolumeDensity (toContinuumPointField newConfiguration 0) =
        generatedVolumeDensity (toContinuumPointField oldConfiguration 0) := by
    unfold generatedVolumeDensity
    change |Matrix.det (newConfiguration.coframe 0)| =
      |Matrix.det (oldConfiguration.coframe 0)|
    rw [coframeEqual]
  unfold lorentzGravityBFAlgebraicCoefficient
  rw [show
    generatedVolumeDensity
        (toContinuumPointField
          (positiveSourceTargetMatterGravityGaugeActual 0) 0) =
      generatedVolumeDensity
        (toContinuumPointField newConfiguration 0) by rfl]
  rw [show
    generatedVolumeDensity
        (toContinuumPointField positiveGravityGaugeLocalActualLift 0) =
      generatedVolumeDensity
        (toContinuumPointField oldConfiguration 0) by rfl]
  rw [show
    (positiveSourceTargetMatterGravityGaugeActual 0).coframe 0 =
        newConfiguration.coframe 0 by rfl]
  rw [show
    (positiveSourceTargetMatterGravityGaugeActual 0).gravityAuxiliary 0 =
        newConfiguration.gravityAuxiliary 0 by rfl]
  rw [show
    positiveGravityGaugeLocalActualLift.coframe 0 =
        oldConfiguration.coframe 0 by rfl]
  rw [show
    positiveGravityGaugeLocalActualLift.gravityAuxiliary 0 =
        oldConfiguration.gravityAuxiliary 0 by rfl]
  rw [volumeEqual, coframeEqual, auxiliaryEqual, curvatureEqual]

theorem positiveSourceTargetMatter_gravityBFAlgebraic_eq_zero :
    lorentzGravityBFAlgebraicCoefficient
        (positiveSourceTargetMatterGravityGaugeActual 0)
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      0 := by
  rw [positiveSourceTargetMatter_gravityBFAlgebraic_eq_positive,
    positiveGravityGaugeLocalActualLift_gravityBFAlgebraic_eq_zero]

theorem positiveSourceTargetMatter_algebraicSpin_eq_half :
    lorentzConnectionAlgebraicSpinCurrentCoefficient
        positiveSmoothUnifiedSource
        (positiveSourceTargetMatterGravityGaugeActual 0)
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      1 / 2 := by
  rw [lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    positiveSourceTargetMatter_gravityBFAlgebraic_eq_zero,
    positiveSourceTargetMatterGravityGaugeActual_matterSpin_eq_half]
  ring

theorem positiveSourceTargetMatter_lorentzSpatialBFMomentumVelocity_eq_half :
    sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
        (spinDirection 0 1) =
      1 / 2 := by
  change
    lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          (positiveSourceTargetMatterGravityGaugeActual 0)
          (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 -
        sourceActionGeneratedLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
          (spinDirection 0 1) =
      1 / 2
  rw [positiveSourceTargetMatter_algebraicSpin_eq_half,
    positiveSourceTargetMatter_lorentzSpatialBFMomentumDivergence_zero]
  ring

theorem positiveSourceTargetMatter_lorentzUnitUpdate_increment_eq_half :
    (sourceActionGeneratedLorentzCanonicalPhaseUpdate
          positiveSmoothUnifiedSource 1
          positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
          0 (spinDirection 0 1) -
        (sourceActionGeneratedLorentzCanonicalPhaseState
          positiveSmoothUnifiedSource
          positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
          0 (spinDirection 0 1) =
      1 / 2 := by
  simpa [sourceActionGeneratedLorentzCanonicalPhaseUpdate,
    sourceActionGeneratedLorentzCanonicalPhaseVelocity] using
    positiveSourceTargetMatter_lorentzSpatialBFMomentumVelocity_eq_half

theorem positiveSourceTargetMatter_lorentzUnitUpdate_fullActionLaw :
    (∀ space,
      holonomicGravityCurvature
          (sourceActionGeneratedGravityGaugeLocalActualLift
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
            space) 0 =
        actionGeneratedGravityCurvature positiveSourceTargetMatterCauchyState
          space) ∧
      LorentzActionGeneratedSpatialVelocityLaw
        positiveSourceTargetMatterCauchyState
        (sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState) ∧
      ∀ space direction,
        (sourceActionGeneratedLorentzCanonicalPhaseUpdate
              positiveSmoothUnifiedSource 1
              positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
              space direction -
            (sourceActionGeneratedLorentzCanonicalPhaseState
              positiveSmoothUnifiedSource
              positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
              space direction =
          let actual :=
            sourceActionGeneratedGravityGaugeLocalActualLift
              positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
              space
          let fullDirection :=
            canonicalLorentzSpatialBivectorOneForm direction
          lorentzConnectionAlgebraicSpinCurrentCoefficient
              positiveSmoothUnifiedSource actual fullDirection 0 -
            sourceActionGeneratedLorentzSpatialBFMomentumDivergence
              positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
              space direction := by
  exact
    sourceActionGeneratedLorentzCanonicalPhaseUnitUpdate_satisfies_spatialActionLaws
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState

theorem positiveSourceTargetMatterActual_smooth :
    positiveSourceTargetMatterActual.Smooth := by
  exact sourceActionGeneratedJointLocalActualLift_smooth
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

theorem positiveSourceTargetMatterActual_nondegenerate :
    positiveSourceTargetMatterActual.Nondegenerate := by
  apply sourceActionGeneratedJointLocalActualLift_nondegenerate
  simp [positiveSourceTargetMatterCauchyState,
    sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

theorem positiveSourceTargetMatterActual_matterActionJet
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            (positiveSourceTargetMatterActual.matter point))
        0 direction =
      actionGeneratedMatterLocalJetCoordinate
        positiveSourceTargetMatterCauchyState 0 direction := by
  change
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((sourceActionGeneratedMatterLocalActualLift
              positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
              0).matter point))
        0 direction =
      _
  exact sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      direction

theorem positiveSourceTargetMatterActual_conjugateActionJet
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          positiveSourceTargetMatterActual.conjugateMatter point matter)
        0 direction =
      actionGeneratedConjugateMatterLocalJet
        positiveSourceTargetMatterCauchyState 0 direction matter := by
  change
    fieldDirectionalDerivative
        (fun point =>
          (sourceActionGeneratedMatterDualLocalActualLift
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
            0).conjugateMatter point matter)
        0 direction =
      _
  exact
    sourceActionGeneratedMatterDualLocalActualLift_conjugateDerivative_origin
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
        matter direction

/-- C3h107 records the output of the forward source/action construction.

The law owns the actual path, both action-generated matter jets, and the
complete Lorentz canonical update.  The fixed nonzero coordinate is only a
faithful readout of that universally quantified update; it is not stored in
the source or used to choose the generated configuration. -/
structure PositiveSourceGeneratedMatterSpinActionUpdateLaw
    (actual : StageNineHolonomicConfiguration) : Prop where
  actualPath :
    actual =
      sourceActionGeneratedJointLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
  sourceTargetPairing :
    ∀ space,
      (sourceTargetMatterCauchyState
          positiveSmoothUnifiedSource).conjugateMatter space
          ((sourceTargetMatterCauchyState
            positiveSmoothUnifiedSource).matter space) =
        (sourceGeneratedMatterJet
            positiveSmoothUnifiedSource.stageEight).sourceConjugateField
          (diracExteriorLinkAction
            ((motherLinkFamilyOfConnection zeroMotherGaugeConnection) 0)
            ((sourceGeneratedMatterJet
              positiveSmoothUnifiedSource.stageEight).targetField 0))
  smooth :
    actual.Smooth
  nondegenerate :
    actual.Nondegenerate
  matterActionJet :
    ∀ direction,
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (actual.matter point))
          0 direction =
        actionGeneratedMatterLocalJetCoordinate
          positiveSourceTargetMatterCauchyState 0 direction
  conjugateActionJet :
    ∀ matter direction,
      fieldDirectionalDerivative
          (fun point => actual.conjugateMatter point matter)
          0 direction =
        actionGeneratedConjugateMatterLocalJet
          positiveSourceTargetMatterCauchyState 0 direction matter
  generatedGravityCurvature :
    ∀ space,
      holonomicGravityCurvature
          (sourceActionGeneratedGravityGaugeLocalActualLift
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
            space) 0 =
        actionGeneratedGravityCurvature positiveSourceTargetMatterCauchyState
          space
  generatedLorentzConnectionVelocity :
    LorentzActionGeneratedSpatialVelocityLaw
      positiveSourceTargetMatterCauchyState
      (sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState)
  fullLorentzMomentumUpdate :
    ∀ space direction,
      (sourceActionGeneratedLorentzCanonicalPhaseUpdate
            positiveSmoothUnifiedSource 1
            positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
            space direction -
          (sourceActionGeneratedLorentzCanonicalPhaseState
            positiveSmoothUnifiedSource
            positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
            space direction =
        let gravityGaugeActual :=
          sourceActionGeneratedGravityGaugeLocalActualLift
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
            space
        let fullDirection :=
          canonicalLorentzSpatialBivectorOneForm direction
        lorentzConnectionAlgebraicSpinCurrentCoefficient
            positiveSmoothUnifiedSource gravityGaugeActual fullDirection 0 -
          sourceActionGeneratedLorentzSpatialBFMomentumDivergence
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
            space direction
  nonzeroMatterSpinUpdate :
    (sourceActionGeneratedLorentzCanonicalPhaseUpdate
          positiveSmoothUnifiedSource 1
          positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
          0 (spinDirection 0 1) -
        (sourceActionGeneratedLorentzCanonicalPhaseState
          positiveSmoothUnifiedSource
          positiveSourceTargetMatterCauchyState).spatialBFMomentumEvaluation
          0 (spinDirection 0 1) =
      1 / 2

theorem positiveSourceGeneratedMatterSpinActionUpdate_realizes_C3h107 :
    PositiveSourceGeneratedMatterSpinActionUpdateLaw
      positiveSourceTargetMatterActual := by
  have fullActionLaw :=
    positiveSourceTargetMatter_lorentzUnitUpdate_fullActionLaw
  refine
    { actualPath := rfl,
      sourceTargetPairing := ?_,
      smooth := positiveSourceTargetMatterActual_smooth,
      nondegenerate := positiveSourceTargetMatterActual_nondegenerate,
      matterActionJet := positiveSourceTargetMatterActual_matterActionJet,
      conjugateActionJet :=
        positiveSourceTargetMatterActual_conjugateActionJet,
      generatedGravityCurvature := fullActionLaw.1,
      generatedLorentzConnectionVelocity := fullActionLaw.2.1,
      fullLorentzMomentumUpdate := fullActionLaw.2.2,
      nonzeroMatterSpinUpdate :=
        positiveSourceTargetMatter_lorentzUnitUpdate_increment_eq_half }
  intro space
  exact
    sourceTargetMatterCauchyState_pairing positiveSmoothUnifiedSource space

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceGeneratedMatterSpinActionUpdate
