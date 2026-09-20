import H0mework.Physics.Exterior.JointActionCanonicalPhasePathLaw

/-!
# S9-C3h101: path-first joint local actual lift

C3h100 generated a reduced canonical path directly from one proof-free source,
one primitive Cauchy state, and the existing sector actions.  This module
constructs an actual local holonomic field before any residual is read.

The Lorentz connection is Cauchy-faithful:

* its temporal--spatial jet is the C3h95 action-generated connection velocity;
* its spatial--temporal jet is the actual spatial Cauchy derivative;
* only the purely spatial exterior derivative uses the fixed antisymmetric
  half split.

The resulting germ recovers all six action-generated gravity-curvature
components and its temporal derivative is literally the C3h95 tangent.  It is
then installed into the existing P286, scalar, matter, and conjugate-matter
actual lift.

For the existing positive proof-free source, the three canonical momentum
velocities are independently computed from the action to be zero.  Hence the
same actual nine-field germ realizes all twelve C3h100 initial coordinates and
all twelve C3h100 first-jet coordinates.  No residual, target endpoint,
preimage, quotient representative, supplied solution certificate, or branch
choice participates in either constructor.

This is a local first-jet producer at the canonical positive source.  It is
not a nonlinear integral flow, a neighborhood on-shell development, or the
final interaction-sensitive simultaneous Stage-9 producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineJointActionLocalActualLift

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open PointwiseDiracSpinConnectionLift
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineJointActionCanonicalPhaseUpdate
open StageNineJointActionCanonicalPhasePathLaw
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionPointwiseEquation
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineScalarActionCanonicalMomentumUpdate
open StageNineScalarPointwiseEquation
open StageNineBlockwiseConstitutive
open StageNineDynamicBreakingVacuum
open StageNineGravityGaugeActionLocalActualLift
open StageNineGravityAuxiliaryVariation
open StageNineGlobalIntegratedAction
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarVariation
open StageNineSourceGeneratedHolonomicPhaseEvolution
open StageNineHolonomicField
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def positiveProbeCauchyStateNormalForm : StageNineCauchyState where
  coframe := fun _ => 1
  gravityConnection := fun _ => 0
  gravityAuxiliary := fun _ => 0
  gravitySimplicityMultiplier := fun _ => 0
  gaugeConnection := fun _ => 0
  gaugeAuxiliary := fun _ => 0
  scalar := fun _ =>
    sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  scalarVelocity := fun _ => 0
  matter := fun _ => 0
  conjugateMatter := fun _ => 0

theorem positivePhaseProbeCauchyState_eq_normalForm :
    positivePhaseProbeCauchyState = positiveProbeCauchyStateNormalForm := by
  apply StageNineCauchyState.ext <;>
    funext <;>
    simp [positiveProbeCauchyStateNormalForm,
      positivePhaseProbeCauchyState,
      canonicalCauchyRestriction,
      positivePhaseProbeConfiguration,
      fieldDirectionalDerivative]

theorem positiveMatterRawTimeVelocity_zero :
    actionGeneratedMatterRawTimeVelocity
        positivePhaseProbeCauchyState 0 = 0 := by
  simp [actionGeneratedMatterRawTimeVelocity,
    actionGeneratedMatterTimeCovariantDerivative,
    identityCoframeMatterTimePrincipal,
    actionGeneratedMatterKnownVector,
    cauchyMatterSpatialCovariantDerivative,
    cauchyMatterSpatialDerivativeCoordinate,
    cauchyMatterConnectionAction,
    positivePhaseProbeCauchyState,
    canonicalCauchyRestriction,
    positivePhaseProbeConfiguration]

def positiveJointLocalActualLift : StageNineHolonomicConfiguration :=
  sourceActionGeneratedMatterDualScalarLocalActualLift
    positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

def positiveGravityGaugeLocalActualLift : StageNineHolonomicConfiguration :=
  sourceActionGeneratedGravityGaugeLocalActualLift
    positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

@[simp] theorem positiveGravityGaugeLocalActualLift_gaugeConnection_origin :
    positiveGravityGaugeLocalActualLift.gaugeConnection 0 = 0 := by
  unfold positiveGravityGaugeLocalActualLift
    sourceActionGeneratedGravityGaugeLocalActualLift
  funext direction
  change sourceGeneratedP286ActionLocalConnection
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 0
        direction = 0
  rw [sourceGeneratedP286ActionLocalConnection_origin]
  rfl

@[simp] theorem positiveGravityGaugeLocalActualLift_gravityConnection_origin :
    positiveGravityGaugeLocalActualLift.gravityConnection 0 = 0 := by
  unfold positiveGravityGaugeLocalActualLift
  rw [
    sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin]
  rfl

@[simp] theorem positiveGravityGaugeLocalActualLift_gaugeAuxiliary_origin :
    positiveGravityGaugeLocalActualLift.gaugeAuxiliary 0 = 0 := by
  rfl

@[simp] theorem positiveGravityGaugeLocalActualLift_scalar_origin :
    positiveGravityGaugeLocalActualLift.scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  simp [positiveGravityGaugeLocalActualLift,
    sourceActionGeneratedGravityGaugeLocalActualLift,
    sourceGeneratedP286ActionLocalActualLift,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

@[simp] theorem positiveGravityGaugeLocalActualLift_matter_origin :
    positiveGravityGaugeLocalActualLift.matter 0 = 0 := by
  rfl

@[simp] theorem positiveGravityGaugeLocalActualLift_conjugate_origin :
    positiveGravityGaugeLocalActualLift.conjugateMatter 0 = 0 := by
  rfl

@[simp] theorem
    positiveGravityGaugeLocalActualLift_scalarCovariantDerivative_origin :
    holonomicScalarCovariantDerivative positiveGravityGaugeLocalActualLift 0 =
      0 := by
  funext direction
  simp [holonomicScalarCovariantDerivative,
    positiveGravityGaugeLocalActualLift,
    sourceActionGeneratedGravityGaugeLocalActualLift,
    sourceGeneratedP286ActionLocalActualLift,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm,
    fieldDirectionalDerivative]

@[simp] theorem positiveJointLocalActualLift_gaugeConnection_origin :
    positiveJointLocalActualLift.gaugeConnection 0 = 0 := by
  change positiveGravityGaugeLocalActualLift.gaugeConnection 0 = 0
  exact positiveGravityGaugeLocalActualLift_gaugeConnection_origin

@[simp] theorem positiveJointLocalActualLift_scalar_origin :
    positiveJointLocalActualLift.scalar 0 =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  exact
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

@[simp] theorem positiveJointLocalActualLift_matter_origin :
    positiveJointLocalActualLift.matter 0 = 0 := by
  change
    (sourceActionGeneratedMatterLocalActualLift positiveSmoothUnifiedSource
      positivePhaseProbeCauchyState 0).matter 0 = 0
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  rfl

@[simp] theorem positiveJointLocalActualLift_conjugate_origin :
    positiveJointLocalActualLift.conjugateMatter 0 = 0 := by
  change
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState
      0).conjugateMatter 0 = 0
  rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
  rfl

@[simp] theorem positiveJointLocalActualLift_scalarCovariantDerivative_origin :
    holonomicScalarCovariantDerivative positiveJointLocalActualLift 0 = 0 := by
  funext direction
  have scalarDerivativeZero :
      fieldDirectionalDerivative positiveJointLocalActualLift.scalar
          0 direction = 0 := by
    calc
      _ = actionGeneratedScalarLocalJetCoordinate
            positivePhaseProbeCauchyState 0 direction := by
        simpa [positiveJointLocalActualLift] using
          sourceActionGeneratedMatterDualScalarLocalActualLift_scalarDerivative_origin
            positiveSmoothUnifiedSource positivePhaseProbeCauchyState
              0 direction
      _ = 0 := by
        fin_cases direction <;>
          simp [actionGeneratedScalarLocalJetCoordinate,
            cauchyScalarSpatialDerivativeCoordinate,
            positivePhaseProbeCauchyState_eq_normalForm,
            positiveProbeCauchyStateNormalForm]
  unfold holonomicScalarCovariantDerivative
  rw [scalarDerivativeZero]
  simp

theorem positiveConjugateMatterTimeDerivative_zero :
    actionGeneratedConjugateMatterTimeDerivative
        positivePhaseProbeCauchyState 0 = 0 := by
  apply LinearMap.ext
  intro matter
  simp [actionGeneratedConjugateMatterTimeDerivative,
    actionGeneratedConjugateMatterKnownDual,
    actionGeneratedConjugateMatterSpatialTransport,
    actionGeneratedMatterAlgebraicOperator,
    cauchyMatterVariationConnectionOperator,
    cauchyConjugateMatterSpatialDerivative,
    cauchyConjugateMatterSpatialDerivativeCoordinate,
    positivePhaseProbeCauchyState,
    canonicalCauchyRestriction,
    positivePhaseProbeConfiguration]

theorem positiveGravityGaugeLocalActualLift_space_independent
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedGravityGaugeLocalActualLift
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState space =
      sourceActionGeneratedGravityGaugeLocalActualLift
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 := by
  rw [positivePhaseProbeCauchyState_eq_normalForm]
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

theorem positiveMatterDualScalarLocalActualLift_space_independent
    (space : StageNineSpatialPoint) :
    sourceActionGeneratedMatterDualScalarLocalActualLift
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState space =
      sourceActionGeneratedMatterDualScalarLocalActualLift
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 := by
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  ext <;>
    simp [positiveProbeCauchyStateNormalForm,
      sourceActionGeneratedMatterDualScalarLocalActualLift,
      sourceActionGeneratedMatterDualLocalActualLift,
      sourceActionGeneratedMatterLocalActualLift,
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
      cauchyP286SpatialConnectionDerivativeCoordinate,
      actionGeneratedMatterLocalField,
      actionGeneratedMatterLocalCoordinate,
      actionGeneratedMatterLocalIncrement,
      actionGeneratedMatterLocalJetCoordinate,
      actionGeneratedMatterRawTimeVelocity,
      actionGeneratedMatterTimeCovariantDerivative,
      actionGeneratedMatterKnownVector,
      cauchyMatterSpatialCovariantDerivative,
      cauchyMatterSpatialDerivativeCoordinate,
      cauchyMatterConnectionAction,
      identityCoframeMatterTimePrincipal,
      actionGeneratedConjugateMatterLocalField,
      actionGeneratedConjugateMatterLocalJet,
      actionGeneratedConjugateMatterTimeDerivative,
      actionGeneratedConjugateMatterKnownDual,
      actionGeneratedConjugateMatterSpatialTransport,
      cauchyConjugateMatterSpatialDerivative,
      cauchyConjugateMatterSpatialDerivativeCoordinate,
      actionGeneratedScalarLocalField,
      actionGeneratedScalarLocalIncrement,
      actionGeneratedScalarLocalJetCoordinate,
      cauchyScalarSpatialDerivativeCoordinate]

theorem positiveP286SpatialBFMomentumDivergence_zero
    (direction : P286SpatialGaugeDirection) :
    sourceActionGeneratedP286SpatialBFMomentumDivergence
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction = 0 := by
  unfold sourceActionGeneratedP286SpatialBFMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  have momentumFieldConstant :
      (sourceActionGeneratedP286BFMomentumEvaluation
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState
        derivativeDirection.succ · direction) =
      fun _ =>
        sourceActionGeneratedP286BFMomentumEvaluation
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          derivativeDirection.succ 0 direction := by
    funext space
    unfold sourceActionGeneratedP286BFMomentumEvaluation
    rw [positiveGravityGaugeLocalActualLift_space_independent space]
  rw [momentumFieldConstant]
  simp

theorem positiveLorentzSpatialBFMomentumDivergence_zero
    (direction : LorentzSpatialBivectorDirection) :
    sourceActionGeneratedLorentzSpatialBFMomentumDivergence
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction = 0 := by
  unfold sourceActionGeneratedLorentzSpatialBFMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  have momentumFieldConstant :
      (sourceActionGeneratedLorentzBFMomentumEvaluation
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState
        derivativeDirection.succ · direction) =
      fun _ =>
        sourceActionGeneratedLorentzBFMomentumEvaluation
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          derivativeDirection.succ 0 direction := by
    funext space
    unfold sourceActionGeneratedLorentzBFMomentumEvaluation
    rw [positiveGravityGaugeLocalActualLift_space_independent space]
  rw [momentumFieldConstant]
  simp

theorem positiveScalarSpatialMomentumDivergence_zero
    (direction : ScalarCoordinateCarrier) :
    sourceActionGeneratedScalarSpatialMomentumDivergence
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction = 0 := by
  unfold sourceActionGeneratedScalarSpatialMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  have momentumFieldConstant :
      (sourceActionGeneratedScalarDifferentialMomentumEvaluation
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState
        derivativeDirection.succ · direction) =
      fun _ =>
        sourceActionGeneratedScalarDifferentialMomentumEvaluation
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          derivativeDirection.succ 0 direction := by
    funext space
    unfold sourceActionGeneratedScalarDifferentialMomentumEvaluation
    rw [positiveMatterDualScalarLocalActualLift_space_independent space]
  rw [momentumFieldConstant]
  simp

theorem positiveP286SpatialBFMomentumVelocity_zero :
    sourceActionGeneratedP286SpatialBFMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 = 0 := by
  funext direction
  rw [show
    sourceActionGeneratedP286SpatialBFMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction =
      p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          (sourceActionGeneratedGravityGaugeLocalActualLift
            positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0)
          (canonicalP286SpatialGaugeOneForm direction) 0 -
        sourceActionGeneratedP286SpatialBFMomentumDivergence
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
          direction by rfl]
  rw [positiveP286SpatialBFMomentumDivergence_zero direction, sub_zero]
  change p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource positiveGravityGaugeLocalActualLift
      (canonicalP286SpatialGaugeOneForm direction) 0 = 0
  simp [p286GaugeConnectionAlgebraicCurrentCoefficient,
    p286GaugeConnectionFirstVariationDensity,
    toContinuumPointField,
    p286GaugeConnectionAlgebraicCurvatureDirection,
    p286GaugeConnectionAlgebraicCurvatureVariation,
    holonomicP286GaugeConnectionCoordinate,
    holonomicScalarGaugeConnectionVariation,
    scalarGaugeConnectionKineticFirstVariationDensity,
    matterGaugeConnectionFirstVariationDensity,
    p286GaugeBFCurvatureIncrementDensity,
    scalarFrameRelativeCovariantDerivative,
    StageNineP286GaugeAuxiliaryVariation.p286AuxiliaryCoordinate,
    generatedGaugeTwoFormMetricPairing,
    liftGaugeTwoFormOperator,
    scalarCoordinatePairingRe]

theorem positiveLorentzSpatialBFMomentumVelocity_zero :
    sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 = 0 := by
  funext direction
  rw [show
    sourceActionGeneratedLorentzSpatialBFMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction =
      lorentzConnectionAlgebraicSpinCurrentCoefficient
          positiveSmoothUnifiedSource
          (sourceActionGeneratedGravityGaugeLocalActualLift
            positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0)
          (canonicalLorentzSpatialBivectorOneForm direction) 0 -
        sourceActionGeneratedLorentzSpatialBFMomentumDivergence
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
          direction by rfl]
  rw [positiveLorentzSpatialBFMomentumDivergence_zero direction, sub_zero]
  change lorentzConnectionAlgebraicSpinCurrentCoefficient
      positiveSmoothUnifiedSource positiveGravityGaugeLocalActualLift
      (canonicalLorentzSpatialBivectorOneForm direction) 0 = 0
  have algebraicCurvatureZero :
      lorentzConnectionAlgebraicCurvatureDirection
          positiveGravityGaugeLocalActualLift
          (canonicalLorentzSpatialBivectorOneForm direction) 0 = 0 := by
    funext internalPair spacetimePair
    simp [lorentzConnectionAlgebraicCurvatureDirection,
      lorentzConnectionAlgebraicCurvatureVariation]
  simp [lorentzConnectionAlgebraicSpinCurrentCoefficient,
    lorentzConnectionFirstVariationDensity,
    toContinuumPointField,
    algebraicCurvatureZero,
    gravityBFCurvatureIncrementDensity,
    matterGaugeConnectionFirstVariationDensity,
    gravityCoframePairing,
    coframeTwoFormMetricPairing,
    coframeTwoFormLinear,
    gravitySpacetimeHodge]

theorem positiveScalarTemporalMomentumVelocity_zero :
    sourceActionGeneratedScalarTemporalMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 = 0 := by
  funext direction
  rw [show
    sourceActionGeneratedScalarTemporalMomentumVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        direction =
      scalarAlgebraicDirectionalCoefficient
          positiveSmoothUnifiedSource positiveJointLocalActualLift
          direction 0 -
        sourceActionGeneratedScalarSpatialMomentumDivergence
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
          direction by rfl]
  rw [positiveScalarSpatialMomentumDivergence_zero direction, sub_zero]
  change scalarAlgebraicDirectionalCoefficient
      positiveSmoothUnifiedSource positiveJointLocalActualLift direction 0 = 0
  unfold scalarAlgebraicDirectionalCoefficient
  apply mul_eq_zero_of_right
  simp [toContinuumPointField,
    holonomicScalarVariationAlgebraicDirection,
    scalarGaugeConnectionKineticFirstVariationDensity,
    scalarPotentialFirstVariation,
    scalarYukawaFirstVariationDensity,
    scalarYukawaVariationVector,
    scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe,
    frameRelativeScalarGradient,
    scalarCoordinateRealPairing]

/-! ## Path-first Lorentz actual germ -/

def actionGeneratedLorentzExteriorDerivativeCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) : ℝ :=
  actionGeneratedGravityCurvature state space internalPair spacetimePair -
    cauchyLoweredLorentzConnectionBracketCoordinate state space
      (pairFirst spacetimePair) (pairSecond spacetimePair) internalPair

def actionGeneratedLorentzLocalConnectionJet
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  ![
    ![
      0,
      actionGeneratedLorentzSpatialConnectionVelocity state space 0
        internalPair,
      actionGeneratedLorentzSpatialConnectionVelocity state space 1
        internalPair,
      actionGeneratedLorentzSpatialConnectionVelocity state space 2
        internalPair
    ],
    ![
      cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate state space
        0 canonicalLorentzianTimeDirection internalPair,
      0,
      (1 / 2 : ℝ) *
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
          internalPair 5,
      -((1 / 2 : ℝ) *
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
          internalPair 4)
    ],
    ![
      cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate state space
        1 canonicalLorentzianTimeDirection internalPair,
      -((1 / 2 : ℝ) *
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
          internalPair 5),
      0,
      (1 / 2 : ℝ) *
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
          internalPair 3
    ],
    ![
      cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate state space
        2 canonicalLorentzianTimeDirection internalPair,
      (1 / 2 : ℝ) *
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
          internalPair 4,
      -((1 / 2 : ℝ) *
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
          internalPair 3),
      0
    ]
  ] derivativeDirection formDirection

def actionGeneratedLorentzLocalIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) : BasePoint →L[ℝ] ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    (localBaseCoordinate derivativeDirection).smulRight
      (actionGeneratedLorentzLocalConnectionJet state space
        derivativeDirection formDirection internalPair)

def actionGeneratedLorentzLocalBivectorIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    actionGeneratedLorentzLocalIncrement state space formDirection
      internalPair point

def actionGeneratedLorentzLocalConnectionCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  loweredLorentzConnectionCoefficient
      (state.gravityConnection space) formDirection internalPair +
    actionGeneratedLorentzLocalIncrement state space formDirection
      internalPair point

def actionGeneratedLorentzLocalConnection
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) : LorentzConnectionField :=
  fun point =>
    state.gravityConnection space +
      lorentzSkewConnectionOfBivectorOneForm
        (actionGeneratedLorentzLocalBivectorIncrement state space point)

theorem actionGeneratedLorentzLocalConnection_loweredCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    loweredLorentzConnectionCoefficient
        (actionGeneratedLorentzLocalConnection state space point)
        formDirection internalPair =
      actionGeneratedLorentzLocalConnectionCoordinate state space point
        formDirection internalPair := by
  rw [show
    actionGeneratedLorentzLocalConnection state space point =
      state.gravityConnection space +
        lorentzSkewConnectionOfBivectorOneForm
          (actionGeneratedLorentzLocalBivectorIncrement state space point) by
    rfl]
  rw [loweredLorentzConnectionCoefficient_add,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  rfl

@[simp] theorem actionGeneratedLorentzLocalConnection_origin
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedLorentzLocalConnection state space 0 =
      state.gravityConnection space := by
  have incrementZero :
      actionGeneratedLorentzLocalBivectorIncrement state space 0 = 0 := by
    funext formDirection internalPair
    simp [actionGeneratedLorentzLocalBivectorIncrement,
      actionGeneratedLorentzLocalIncrement]
  unfold actionGeneratedLorentzLocalConnection
  rw [incrementZero]
  funext formDirection internalOut internalIn
  simp

theorem actionGeneratedLorentzLocalConnectionCoordinate_derivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          actionGeneratedLorentzLocalConnectionCoordinate state space point
            formDirection internalPair)
        0 derivativeDirection =
      actionGeneratedLorentzLocalIncrement state space formDirection
        internalPair (coordinateDirection derivativeDirection) := by
  unfold fieldDirectionalDerivative
    actionGeneratedLorentzLocalConnectionCoordinate
  rw [fderiv_const_add]
  rw [(actionGeneratedLorentzLocalIncrement state space formDirection
    internalPair).hasFDerivAt.fderiv]

theorem actionGeneratedLorentzLocalConnection_loweredDerivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            (actionGeneratedLorentzLocalConnection state space point)
            formDirection internalPair)
        0 derivativeDirection =
      actionGeneratedLorentzLocalConnectionJet state space
        derivativeDirection formDirection internalPair := by
  rw [show
    (fun point =>
      loweredLorentzConnectionCoefficient
        (actionGeneratedLorentzLocalConnection state space point)
        formDirection internalPair) =
      fun point =>
        actionGeneratedLorentzLocalConnectionCoordinate state space point
          formDirection internalPair by
    funext point
    exact actionGeneratedLorentzLocalConnection_loweredCoordinate
      state space point formDirection internalPair]
  rw [actionGeneratedLorentzLocalConnectionCoordinate_derivative]
  fin_cases derivativeDirection <;>
    simp [actionGeneratedLorentzLocalIncrement, localBaseCoordinate,
      coordinateDirection, Fin.sum_univ_four]

theorem actionGeneratedLorentzLocalConnection_smooth
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    ∀ formDirection internalOut internalIn,
      ContDiff ℝ ∞ (fun point =>
        actionGeneratedLorentzLocalConnection state space point
          formDirection internalOut internalIn) := by
  intro formDirection internalOut internalIn
  unfold actionGeneratedLorentzLocalConnection
    lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
    actionGeneratedLorentzLocalBivectorIncrement
  apply contDiff_const.add
  apply contDiff_const.mul
  apply ContDiff.sum
  intro internalPair _
  exact
    (actionGeneratedLorentzLocalIncrement state space formDirection
      internalPair).contDiff.mul contDiff_const

theorem loweredLorentzConnectionCoefficient_directionalDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6)
    (differentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          configuration.gravityConnection candidate formDirection
            (pairFirst internalPair) (pairSecond internalPair))
        point) :
    fieldDirectionalDerivative
        (fun candidate =>
          loweredLorentzConnectionCoefficient
            (configuration.gravityConnection candidate)
            formDirection internalPair)
        point derivativeDirection =
      minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative configuration point derivativeDirection
          formDirection (pairFirst internalPair) (pairSecond internalPair) := by
  fin_cases internalPair <;>
    unfold fieldDirectionalDerivative gravityConnectionDerivative
      loweredLorentzConnectionCoefficient <;>
    simp only [lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond] at differentiable ⊢ <;>
    rw [fderiv_const_mul differentiable] <;>
    simp [minkowskiInternalSign]

theorem actionGeneratedLorentzLocalConnectionJet_antisymmetrized
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (internalPair spacetimePair : Fin 6) :
    actionGeneratedLorentzLocalConnectionJet state space
          (pairFirst spacetimePair) (pairSecond spacetimePair) internalPair -
        actionGeneratedLorentzLocalConnectionJet state space
          (pairSecond spacetimePair) (pairFirst spacetimePair) internalPair =
      actionGeneratedLorentzExteriorDerivativeCoordinate state space
        internalPair spacetimePair := by
  fin_cases spacetimePair <;>
    simp [actionGeneratedLorentzLocalConnectionJet,
      actionGeneratedLorentzExteriorDerivativeCoordinate,
      actionGeneratedLorentzSpatialConnectionVelocity,
      temporalSpatialPair, canonicalLorentzianTimeDirection,
      pairFirst, pairSecond] <;>
    ring_nf

def sourceActionGeneratedJointLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  { sourceActionGeneratedMatterDualScalarLocalActualLift source state
      space with
    gravityConnection :=
      actionGeneratedLorentzLocalConnection state space }

theorem sourceActionGeneratedJointLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointLocalActualLift source state space).Smooth := by
  have baseSmooth :=
    sourceActionGeneratedMatterDualScalarLocalActualLift_smooth
      source state space
  rcases baseSmooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      actionGeneratedLorentzLocalConnection_smooth state space,
      gravityAuxiliarySmooth, multiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem sourceActionGeneratedJointLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedJointLocalActualLift source state
      space).Nondegenerate := by
  exact sourceActionGeneratedMatterDualScalarLocalActualLift_nondegenerate
    source state space nondegenerate

theorem sourceActionGeneratedJointLocalActualLift_initialGravityConnection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointLocalActualLift source state space).gravityConnection
        0 =
      state.gravityConnection space := by
  exact actionGeneratedLorentzLocalConnection_origin state space

@[simp] theorem sourceActionGeneratedJointLocalActualLift_initialScalar
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointLocalActualLift source state space).scalar 0 =
      state.scalar space := by
  exact
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
      source state space

@[simp] theorem sourceActionGeneratedJointLocalActualLift_initialMatter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointLocalActualLift source state space).matter 0 =
      state.matter space := by
  exact sourceActionGeneratedMatterLocalActualLift_matter_origin
    source state space

@[simp] theorem sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedJointLocalActualLift source state
      space).conjugateMatter 0 =
      state.conjugateMatter space := by
  exact sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin
    source state space

theorem
    sourceActionGeneratedJointLocalActualLift_matterCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedJointLocalActualLift source state space)
        0 direction =
      holonomicMatterCovariantDerivative
        (sourceActionGeneratedMatterLocalActualLift source state space)
        0 direction := by
  have matterField :
      (sourceActionGeneratedJointLocalActualLift source state space).matter =
        (sourceActionGeneratedMatterLocalActualLift source state
          space).matter :=
    rfl
  have gravityConnectionOrigin :
      (sourceActionGeneratedJointLocalActualLift source state
          space).gravityConnection 0 =
        (sourceActionGeneratedMatterLocalActualLift source state
          space).gravityConnection 0 := by
    rw [sourceActionGeneratedJointLocalActualLift_initialGravityConnection]
    exact
      (sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
        source state space).symm
  have gaugeConnectionOrigin :
      (sourceActionGeneratedJointLocalActualLift source state
          space).gaugeConnection 0 =
        (sourceActionGeneratedMatterLocalActualLift source state
          space).gaugeConnection 0 :=
    rfl
  unfold holonomicMatterCovariantDerivative
  rw [matterField, gravityConnectionOrigin, gaugeConnectionOrigin]

theorem sourceActionGeneratedJointLocalActualLift_lorentzLoweredDerivative
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedJointLocalActualLift source state space).gravityConnection
              point)
            formDirection internalPair)
        0 derivativeDirection =
      actionGeneratedLorentzLocalConnectionJet state space
        derivativeDirection formDirection internalPair := by
  exact actionGeneratedLorentzLocalConnection_loweredDerivative
    state space derivativeDirection formDirection internalPair

theorem sourceActionGeneratedJointLocalActualLift_gravityCurvature_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (sourceActionGeneratedJointLocalActualLift source state space) 0 =
      actionGeneratedGravityCurvature state space := by
  funext internalPair spacetimePair
  let actual :=
    sourceActionGeneratedJointLocalActualLift source state space
  have actualSmooth : actual.Smooth :=
    sourceActionGeneratedJointLocalActualLift_smooth source state space
  have connectionOrigin :
      actual.gravityConnection 0 = state.gravityConnection space :=
    sourceActionGeneratedJointLocalActualLift_initialGravityConnection
      source state space
  have firstDifferentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          actual.gravityConnection candidate (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair))
        0 :=
    (actualSmooth.2.1 (pairSecond spacetimePair)
      (pairFirst internalPair) (pairSecond internalPair)
      |>.differentiable (by simp)).differentiableAt
  have secondDifferentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          actual.gravityConnection candidate (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair))
        0 :=
    (actualSmooth.2.1 (pairFirst spacetimePair)
      (pairFirst internalPair) (pairSecond internalPair)
      |>.differentiable (by simp)).differentiableAt
  have firstDerivative :
      minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative actual 0
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) =
        actionGeneratedLorentzLocalConnectionJet state space
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          internalPair := by
    calc
      _ = fieldDirectionalDerivative
            (fun candidate =>
              loweredLorentzConnectionCoefficient
                (actual.gravityConnection candidate)
                (pairSecond spacetimePair) internalPair)
            0 (pairFirst spacetimePair) := by
          symm
          exact
            loweredLorentzConnectionCoefficient_directionalDerivative
              actual 0 (pairFirst spacetimePair)
                (pairSecond spacetimePair) internalPair
                firstDifferentiable
      _ = _ :=
        sourceActionGeneratedJointLocalActualLift_lorentzLoweredDerivative
          source state space (pairFirst spacetimePair)
            (pairSecond spacetimePair) internalPair
  have secondDerivative :
      minkowskiInternalSign (pairFirst internalPair) *
          gravityConnectionDerivative actual 0
            (pairSecond spacetimePair) (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) =
        actionGeneratedLorentzLocalConnectionJet state space
          (pairSecond spacetimePair) (pairFirst spacetimePair)
          internalPair := by
    calc
      _ = fieldDirectionalDerivative
            (fun candidate =>
              loweredLorentzConnectionCoefficient
                (actual.gravityConnection candidate)
                (pairFirst spacetimePair) internalPair)
            0 (pairSecond spacetimePair) := by
          symm
          exact
            loweredLorentzConnectionCoefficient_directionalDerivative
              actual 0 (pairSecond spacetimePair)
                (pairFirst spacetimePair) internalPair
                secondDifferentiable
      _ = _ :=
        sourceActionGeneratedJointLocalActualLift_lorentzLoweredDerivative
          source state space (pairSecond spacetimePair)
            (pairFirst spacetimePair) internalPair
  have antisymmetrized :=
    actionGeneratedLorentzLocalConnectionJet_antisymmetrized
      state space internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  change
    minkowskiInternalSign (pairFirst internalPair) *
        (gravityConnectionDerivative actual 0
              (pairFirst spacetimePair) (pairSecond spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair) -
          gravityConnectionDerivative actual 0
              (pairSecond spacetimePair) (pairFirst spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair) +
          ∑ middle : LorentzianIndex,
            (actual.gravityConnection 0 (pairFirst spacetimePair)
                  (pairFirst internalPair) middle *
                actual.gravityConnection 0 (pairSecond spacetimePair)
                  middle (pairSecond internalPair) -
              actual.gravityConnection 0 (pairSecond spacetimePair)
                  (pairFirst internalPair) middle *
                actual.gravityConnection 0 (pairFirst spacetimePair)
                  middle (pairSecond internalPair))) =
      actionGeneratedGravityCurvature state space internalPair spacetimePair
  rw [connectionOrigin]
  have bracketCoordinate :
    minkowskiInternalSign (pairFirst internalPair) *
          ∑ middle : LorentzianIndex,
            (state.gravityConnection space (pairFirst spacetimePair)
                  (pairFirst internalPair) middle *
                state.gravityConnection space (pairSecond spacetimePair)
                  middle (pairSecond internalPair) -
              state.gravityConnection space (pairSecond spacetimePair)
                  (pairFirst internalPair) middle *
                state.gravityConnection space (pairFirst spacetimePair)
                  middle (pairSecond internalPair)) =
        cauchyLoweredLorentzConnectionBracketCoordinate state space
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          internalPair := by
    rfl
  calc
    _ =
        (minkowskiInternalSign (pairFirst internalPair) *
            gravityConnectionDerivative actual 0
              (pairFirst spacetimePair) (pairSecond spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair)) -
          (minkowskiInternalSign (pairFirst internalPair) *
            gravityConnectionDerivative actual 0
              (pairSecond spacetimePair) (pairFirst spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair)) +
          cauchyLoweredLorentzConnectionBracketCoordinate state space
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            internalPair := by
      rw [← bracketCoordinate]
      ring
    _ =
        actionGeneratedLorentzLocalConnectionJet state space
              (pairFirst spacetimePair) (pairSecond spacetimePair)
              internalPair -
            actionGeneratedLorentzLocalConnectionJet state space
              (pairSecond spacetimePair) (pairFirst spacetimePair)
              internalPair +
          cauchyLoweredLorentzConnectionBracketCoordinate state space
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            internalPair := by rw [firstDerivative, secondDerivative]
    _ =
        actionGeneratedLorentzExteriorDerivativeCoordinate state space
            internalPair spacetimePair +
          cauchyLoweredLorentzConnectionBracketCoordinate state space
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            internalPair := by rw [antisymmetrized]
    _ = _ := by
      unfold actionGeneratedLorentzExteriorDerivativeCoordinate
      ring

theorem sourceActionGeneratedJointLocalActualLift_lorentzSpatialTimeDerivative
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            ((sourceActionGeneratedJointLocalActualLift source state space).gravityConnection
              point)
            direction.succ internalPair)
        0 canonicalLorentzianTimeDirection =
      actionGeneratedLorentzSpatialConnectionVelocity state space direction
        internalPair := by
  change
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            (actionGeneratedLorentzLocalConnection state space point)
            direction.succ internalPair)
        0 canonicalLorentzianTimeDirection =
      _
  rw [actionGeneratedLorentzLocalConnection_loweredDerivative]
  fin_cases direction <;>
    simp [actionGeneratedLorentzLocalConnectionJet,
      canonicalLorentzianTimeDirection]

/-! ## Positive full-field specialization -/

def positivePathFirstJointLocalActualLift :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedJointLocalActualLift
    positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

@[simp] theorem positivePathFirstJointLocalActualLift_coframe :
    positivePathFirstJointLocalActualLift.coframe = fun _ => 1 := by
  funext point
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

@[simp] theorem positivePathFirstJointLocalActualLift_gravityAuxiliary :
    positivePathFirstJointLocalActualLift.gravityAuxiliary =
      fun _ => physicalIIPlusBivector 1 := by
  funext point
  change actionGeneratedGravityAuxiliary positivePhaseProbeCauchyState 0 =
    physicalIIPlusBivector 1
  simp [actionGeneratedGravityAuxiliary,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

@[simp] theorem positivePathFirstJointLocalActualLift_multiplier :
    positivePathFirstJointLocalActualLift.gravitySimplicityMultiplier = 0 := by
  funext point internalPair spacetimePair
  change positivePhaseProbeCauchyState.gravitySimplicityMultiplier 0
    internalPair spacetimePair = 0
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

@[simp] theorem positivePathFirstJointLocalActualLift_gaugeAuxiliary :
    positivePathFirstJointLocalActualLift.gaugeAuxiliary = 0 := by
  funext point pair
  change positivePhaseProbeCauchyState.gaugeAuxiliary 0 pair = 0
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

theorem positiveP286SpatialConnectionVelocity_zero :
    sourceGeneratedP286SpatialConnectionVelocity
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState = 0 := by
  apply sourceGeneratedP286SpatialConnectionVelocity_eq_zero_of_gaugeData_zero
  · rfl
  · rfl

theorem positiveP286ActionLocalConnectionJet_zero
    (derivativeDirection formDirection : LorentzianIndex) :
    sourceGeneratedP286ActionLocalConnectionJet
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        derivativeDirection formDirection = 0 := by
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [sourceGeneratedP286ActionLocalConnectionJet,
      actionGeneratedP286ExteriorDerivativeCoordinate,
      actionGeneratedP286Curvature,
      cauchyP286SpatialConnectionDerivativeCoordinate,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]

theorem positiveP286ActionLocalIncrement_zero
    (formDirection : LorentzianIndex) :
    sourceGeneratedP286ActionLocalIncrement
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        formDirection = 0 := by
  apply ContinuousLinearMap.ext
  intro point
  simp [sourceGeneratedP286ActionLocalIncrement,
    positiveP286ActionLocalConnectionJet_zero]

@[simp] theorem positivePathFirstJointLocalActualLift_gaugeConnection :
    positivePathFirstJointLocalActualLift.gaugeConnection = 0 := by
  funext point formDirection
  change sourceGeneratedP286ActionLocalConnection
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
      point formDirection = 0
  apply p286CoordinateEquiv.injective
  simp only [sourceGeneratedP286ActionLocalConnection,
    p286CoordinateEquiv.apply_symm_apply]
  unfold sourceGeneratedP286ActionLocalConnectionCoordinate
  rw [positiveP286ActionLocalIncrement_zero]
  simp [
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

@[simp] theorem positivePathFirstJointLocalActualLift_gravityConnection_origin :
    positivePathFirstJointLocalActualLift.gravityConnection 0 = 0 := by
  change
    actionGeneratedLorentzLocalConnection positivePhaseProbeCauchyState 0
      0 = 0
  rw [actionGeneratedLorentzLocalConnection_origin]
  rfl

@[simp] theorem positivePathFirstJointLocalActualLift_matter_origin :
    positivePathFirstJointLocalActualLift.matter 0 = 0 := by
  change
    (sourceActionGeneratedMatterLocalActualLift positiveSmoothUnifiedSource
      positivePhaseProbeCauchyState 0).matter 0 = 0
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  rfl

@[simp] theorem positivePathFirstJointLocalActualLift_conjugate_origin :
    positivePathFirstJointLocalActualLift.conjugateMatter 0 = 0 := by
  change
    (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState
      0).conjugateMatter 0 = 0
  rw [sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
  rfl

@[simp] theorem positivePathFirstJointLocalActualLift_scalar :
    positivePathFirstJointLocalActualLift.scalar =
      fun _ => sourceGeneratedVacuumCoordinates
        positiveSmoothUnifiedSource := by
  funext point
  rw [show
    positivePathFirstJointLocalActualLift.scalar point =
      actionGeneratedScalarLocalField positivePhaseProbeCauchyState 0 point by
    rfl]
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement,
    actionGeneratedScalarLocalJetCoordinate,
    cauchyScalarSpatialDerivativeCoordinate,
    positiveProbeCauchyStateNormalForm,
    Fin.sum_univ_four]

@[simp] theorem
    positivePathFirstJointLocalActualLift_scalarCovariantDerivative :
    holonomicScalarCovariantDerivative
        positivePathFirstJointLocalActualLift = 0 := by
  funext point direction
  simp [holonomicScalarCovariantDerivative,
    fieldDirectionalDerivative]

theorem positivePathFirstJointLocalActualLift_p286BFMomentum_zero
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positivePathFirstJointLocalActualLift direction = 0 := by
  funext point
  have auxiliaryZero :
      holonomicP286GaugeAuxiliaryCoordinate
          positivePathFirstJointLocalActualLift point = 0 := by
    funext pair
    simp [holonomicP286GaugeAuxiliaryCoordinate]
  rw [show
    p286GaugeConnectionBFDifferentialMomentum
        positivePathFirstJointLocalActualLift direction point =
      generatedVolumeDensity
          (toContinuumPointField positivePathFirstJointLocalActualLift point) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          (positivePathFirstJointLocalActualLift.coframe point)
          (holonomicP286GaugeAuxiliaryCoordinate
            positivePathFirstJointLocalActualLift point)
          direction by rfl]
  rw [auxiliaryZero]
  simp [p286GaugeAuxiliaryHodgePairingPolynomial]

theorem positivePathFirstJointLocalActualLift_lorentzBFMomentum_const
    (direction : PhysicalBivector) :
    lorentzConnectionBFDifferentialMomentum
        positivePathFirstJointLocalActualLift direction =
      fun _ =>
        gravityAuxiliaryHodgePairingPolynomial 1
          (physicalIIPlusBivector 1) direction := by
  funext point
  simp [lorentzConnectionBFDifferentialMomentum,
    generatedVolumeDensity, toContinuumPointField]

theorem positivePathFirstJointLocalActualLift_scalarMomentum_zero
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        positivePathFirstJointLocalActualLift direction
        derivativeDirection = 0 := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
  simp [toContinuumPointField,
    scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

theorem positiveP286BFMomentumEvaluation_zero
    (derivativeDirection : LorentzianIndex)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    sourceActionGeneratedP286BFMomentumEvaluation
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState
        derivativeDirection space direction = 0 := by
  change
    p286GaugeConnectionBFDifferentialMomentum
        (sourceActionGeneratedGravityGaugeLocalActualLift
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState space)
        (p286GaugeExteriorDerivativeDirection derivativeDirection
          (canonicalP286SpatialGaugeOneForm direction))
        0 = 0
  have auxiliaryZero :
      holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedGravityGaugeLocalActualLift
            positiveSmoothUnifiedSource positivePhaseProbeCauchyState
            space)
          0 = 0 := by
    funext pair
    simp [holonomicP286GaugeAuxiliaryCoordinate,
      sourceActionGeneratedGravityGaugeLocalActualLift,
      sourceGeneratedP286ActionLocalActualLift,
      positivePhaseProbeCauchyState,
      canonicalCauchyRestriction,
      positivePhaseProbeConfiguration]
  unfold p286GaugeConnectionBFDifferentialMomentum
  rw [auxiliaryZero]
  simp [p286GaugeAuxiliaryHodgePairingPolynomial]

theorem positiveLorentzBFMomentumEvaluation_const
    (derivativeDirection : LorentzianIndex)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    sourceActionGeneratedLorentzBFMomentumEvaluation
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState
        derivativeDirection space direction =
      gravityAuxiliaryHodgePairingPolynomial 1
        (physicalIIPlusBivector 1)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          (canonicalLorentzSpatialBivectorOneForm direction)) := by
  change
    lorentzConnectionBFDifferentialMomentum
        (sourceActionGeneratedGravityGaugeLocalActualLift
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState space)
        (lorentzConnectionExteriorDerivativeDirection derivativeDirection
          (canonicalLorentzSpatialBivectorOneForm direction))
        0 =
      _
  unfold lorentzConnectionBFDifferentialMomentum
    generatedVolumeDensity
  simp [toContinuumPointField,
    sourceActionGeneratedGravityGaugeLocalActualLift,
    sourceGeneratedP286ActionLocalActualLift,
    actionGeneratedGravityAuxiliary,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

theorem positiveScalarDifferentialMomentumEvaluation_zero
    (derivativeDirection : LorentzianIndex)
    (direction : ScalarCoordinateCarrier) :
    sourceActionGeneratedScalarDifferentialMomentumEvaluation
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState
        derivativeDirection 0 direction = 0 := by
  change
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        positiveJointLocalActualLift direction derivativeDirection 0 = 0
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
  simp [toContinuumPointField,
    scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

theorem positivePathFirstJointLocalActualLift_p286TemporalBFDerivative_zero
    (direction : P286SpatialGaugeDirection) :
    p286GaugeConnectionTemporalBFMomentumDerivative
        positivePathFirstJointLocalActualLift
        (canonicalP286SpatialGaugeOneForm direction) 0 = 0 := by
  unfold p286GaugeConnectionTemporalBFMomentumDerivative
  rw [positivePathFirstJointLocalActualLift_p286BFMomentum_zero]
  simp [fieldDirectionalDerivative]

theorem positivePathFirstJointLocalActualLift_lorentzTemporalBFDerivative_zero
    (direction : LorentzSpatialBivectorDirection) :
    lorentzConnectionTemporalBFMomentumDerivative
        positivePathFirstJointLocalActualLift
        (canonicalLorentzSpatialBivectorOneForm direction) 0 = 0 := by
  unfold lorentzConnectionTemporalBFMomentumDerivative
  rw [positivePathFirstJointLocalActualLift_lorentzBFMomentum_const]
  simp [fieldDirectionalDerivative]

theorem
    positivePathFirstJointLocalActualLift_scalarTemporalMomentumDerivative_zero
    (direction : ScalarCoordinateCarrier) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          positivePathFirstJointLocalActualLift direction
          canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection = 0 := by
  rw [positivePathFirstJointLocalActualLift_scalarMomentum_zero]
  simp [fieldDirectionalDerivative]

theorem positivePathFirstJointLocalActualLift_coframeTimeDerivative_zero
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          positivePathFirstJointLocalActualLift.coframe point
            internal coordinate)
        0 canonicalLorentzianTimeDirection = 0 := by
  simp [fieldDirectionalDerivative]

theorem positivePathFirstJointLocalActualLift_multiplierTimeDerivative_zero
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          positivePathFirstJointLocalActualLift.gravitySimplicityMultiplier
            point internalPair spacetimePair)
        0 canonicalLorentzianTimeDirection = 0 := by
  simp [fieldDirectionalDerivative]

theorem
    positivePathFirstJointLocalActualLift_temporalGravityTimeDerivative_zero
    (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            (positivePathFirstJointLocalActualLift.gravityConnection point)
            canonicalLorentzianTimeDirection internalPair)
        0 canonicalLorentzianTimeDirection = 0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          loweredLorentzConnectionCoefficient
            (actionGeneratedLorentzLocalConnection
              positivePhaseProbeCauchyState 0 point)
            canonicalLorentzianTimeDirection internalPair)
        0 canonicalLorentzianTimeDirection = 0
  rw [actionGeneratedLorentzLocalConnection_loweredDerivative]
  simp [actionGeneratedLorentzLocalConnectionJet,
    canonicalLorentzianTimeDirection]

theorem
    positivePathFirstJointLocalActualLift_temporalGaugeTimeDerivative_zero :
    p286GaugeConnectionCoordinateDerivative
        positivePathFirstJointLocalActualLift 0
        canonicalLorentzianTimeDirection
        canonicalLorentzianTimeDirection = 0 := by
  simp [p286GaugeConnectionCoordinateDerivative,
    holonomicP286GaugeConnectionCoordinate,
    fieldDirectionalDerivative]

theorem positivePathFirstJointLocalActualLift_p286SpatialTimeDerivative
    (direction : Fin 3) :
    p286GaugeConnectionCoordinateDerivative
        positivePathFirstJointLocalActualLift 0
        canonicalLorentzianTimeDirection direction.succ =
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          0 direction) := by
  have velocityZero :
      sourceGeneratedP286SpatialConnectionVelocity
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          0 direction = 0 :=
    congrFun
      (congrFun positiveP286SpatialConnectionVelocity_zero 0) direction
  rw [velocityZero]
  simp [p286GaugeConnectionCoordinateDerivative,
    holonomicP286GaugeConnectionCoordinate,
    fieldDirectionalDerivative]

theorem positivePathFirstJointLocalActualLift_scalarTimeDerivative :
    fieldDirectionalDerivative positivePathFirstJointLocalActualLift.scalar
        0 canonicalLorentzianTimeDirection =
      positivePhaseProbeCauchyState.scalarVelocity 0 := by
  change
    fieldDirectionalDerivative
        (sourceActionGeneratedMatterDualScalarLocalActualLift
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0).scalar
        0 canonicalLorentzianTimeDirection =
      _
  exact
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalarTimeVelocity_origin
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0

theorem positivePathFirstJointLocalActualLift_matterTimeDerivative :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            (positivePathFirstJointLocalActualLift.matter point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (actionGeneratedMatterRawTimeVelocity
          positivePhaseProbeCauchyState 0) := by
  change
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((sourceActionGeneratedMatterLocalActualLift
              positiveSmoothUnifiedSource positivePhaseProbeCauchyState
              0).matter point))
        0 canonicalLorentzianTimeDirection =
      _
  simpa [actionGeneratedMatterLocalJetCoordinate,
    canonicalLorentzianTimeDirection] using
    sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
        canonicalLorentzianTimeDirection

theorem positivePathFirstJointLocalActualLift_conjugateTimeDerivative
    (matter : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          positivePathFirstJointLocalActualLift.conjugateMatter point matter)
        0 canonicalLorentzianTimeDirection =
      actionGeneratedConjugateMatterTimeDerivative
        positivePhaseProbeCauchyState 0 matter := by
  change
    fieldDirectionalDerivative
        (fun point =>
          (sourceActionGeneratedMatterDualLocalActualLift
            positiveSmoothUnifiedSource positivePhaseProbeCauchyState
            0).conjugateMatter point matter)
        0 canonicalLorentzianTimeDirection =
      _
  simpa [actionGeneratedConjugateMatterLocalJet,
    canonicalLorentzianTimeDirection] using
    sourceActionGeneratedMatterDualLocalActualLift_conjugateDerivative_origin
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 matter
        canonicalLorentzianTimeDirection

/-! ## Complete C3h100 actual-lift interface -/

structure StageNineJointCanonicalActualInitialLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (actual : StageNineHolonomicConfiguration) : Prop where
  coframe :
    ∀ internal coordinate,
      actual.coframe 0 internal coordinate =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).frozenCoframeSnapshot
          space internal coordinate
  simplicityMultiplier :
    ∀ internalPair spacetimePair,
      actual.gravitySimplicityMultiplier 0 internalPair spacetimePair =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).gravitySimplicityMultiplier
          space internalPair spacetimePair
  temporalGravityConnection :
    ∀ internalPair,
      loweredLorentzConnectionCoefficient
          (actual.gravityConnection 0)
          canonicalLorentzianTimeDirection internalPair =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).temporalGravityConnection
          space internalPair
  temporalGaugeConnection :
    p286CoordinateEquiv
        (actual.gaugeConnection 0 canonicalLorentzianTimeDirection) =
      p286CoordinateEquiv
        ((sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).temporalGaugeConnection
          space)
  p286SpatialConnection :
    ∀ direction,
      holonomicP286GaugeConnectionCoordinate
          actual 0 direction.succ =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).gravityGauge.p286.spatialConnection
          space direction
  p286SpatialBFMomentum :
    ∀ direction,
      p286GaugeConnectionBFDifferentialMomentum
          actual
          (p286GaugeExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalP286SpatialGaugeOneForm direction))
          0 =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).gravityGauge.p286.spatialBFMomentumEvaluation
          space direction
  lorentzSpatialConnection :
    ∀ direction internalPair,
      loweredLorentzConnectionCoefficient
          (actual.gravityConnection 0)
          direction.succ internalPair =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).gravityGauge.lorentz.spatialConnection
          space direction
            internalPair
  lorentzSpatialBFMomentum :
    ∀ direction,
      lorentzConnectionBFDifferentialMomentum
          actual
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction))
          0 =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).gravityGauge.lorentz.spatialBFMomentumEvaluation
          space direction
  scalarCoordinate :
    actual.scalar 0 =
      (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).scalar.scalarCoordinate
        space
  scalarTemporalMomentum :
    ∀ direction,
      scalarDifferentialMomentum source
          actual direction canonicalLorentzianTimeDirection 0 =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).scalar.temporalMomentumEvaluation
          space direction
  matter :
    actual.matter 0 =
      (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).matter
        space
  conjugateMatterEvaluation :
    ∀ matter,
      actual.conjugateMatter 0 matter =
        (sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state).conjugateMatter
          space matter

theorem positivePathFirstJointLocalActualLift_initialLaw :
    StageNineJointCanonicalActualInitialLaw positiveSmoothUnifiedSource
      positivePhaseProbeCauchyState 0
        positivePathFirstJointLocalActualLift := by
  refine
    { coframe := ?_,
      simplicityMultiplier := ?_,
      temporalGravityConnection := ?_,
      temporalGaugeConnection := ?_,
      p286SpatialConnection := ?_,
      p286SpatialBFMomentum := ?_,
      lorentzSpatialConnection := ?_,
      lorentzSpatialBFMomentum := ?_,
      scalarCoordinate := ?_,
      scalarTemporalMomentum := ?_,
      matter := ?_,
      conjugateMatterEvaluation := ?_ }
  · intro internal coordinate
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro internalPair spacetimePair
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro internalPair
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero,
      positivePathFirstJointLocalActualLift_gravityConnection_origin]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro direction
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [holonomicP286GaugeConnectionCoordinate,
      sourceActionGeneratedJointCanonicalPhaseState,
      sourceActionGeneratedGravityGaugeCanonicalPhaseState,
      sourceActionGeneratedP286CanonicalPhaseState,
      sourceActionGeneratedP286SpatialConnectionCoordinate,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro direction
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    rw [positivePathFirstJointLocalActualLift_p286BFMomentum_zero]
    change
      0 =
        sourceActionGeneratedP286BFMomentumEvaluation
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          canonicalLorentzianTimeDirection 0 direction
    rw [positiveP286BFMomentumEvaluation_zero]
  · intro direction internalPair
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero,
      positivePathFirstJointLocalActualLift_gravityConnection_origin]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      sourceActionGeneratedGravityGaugeCanonicalPhaseState,
      sourceActionGeneratedLorentzCanonicalPhaseState,
      sourceActionGeneratedLorentzSpatialConnectionCoordinate,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro direction
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    rw [show
      lorentzConnectionBFDifferentialMomentum
          positivePathFirstJointLocalActualLift
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction))
          0 =
        gravityAuxiliaryHodgePairingPolynomial 1
          (physicalIIPlusBivector 1)
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction)) by
      exact congrFun
        (positivePathFirstJointLocalActualLift_lorentzBFMomentum_const
          (lorentzConnectionExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalLorentzSpatialBivectorOneForm direction)))
        0]
    change
      _ =
        sourceActionGeneratedLorentzBFMomentumEvaluation
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          canonicalLorentzianTimeDirection 0 direction
    rw [positiveLorentzBFMomentumEvaluation_const]
  · rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      sourceActionGeneratedScalarCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro direction
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    rw [positivePathFirstJointLocalActualLift_scalarMomentum_zero]
    change
      0 =
        sourceActionGeneratedScalarDifferentialMomentumEvaluation
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState
          canonicalLorentzianTimeDirection 0 direction
    rw [positiveScalarDifferentialMomentumEvaluation_zero]
  · rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  · intro matter
    rw [sourceActionGeneratedJointCanonicalPhasePath_zero]
    simp [sourceActionGeneratedJointCanonicalPhaseState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]

structure StageNineJointCanonicalActualFirstJetLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (actual : StageNineHolonomicConfiguration) : Prop where
  coframe :
    ∀ internal coordinate,
      fieldDirectionalDerivative
          (fun point => actual.coframe point internal coordinate)
          0 canonicalLorentzianTimeDirection =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).frozenCoframeSnapshot space internal coordinate)
          0
  simplicityMultiplier :
    ∀ internalPair spacetimePair,
      fieldDirectionalDerivative
          (fun point =>
            actual.gravitySimplicityMultiplier point internalPair
              spacetimePair)
          0 canonicalLorentzianTimeDirection =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).gravitySimplicityMultiplier space internalPair
                spacetimePair)
          0
  temporalGravityConnection :
    ∀ internalPair,
      fieldDirectionalDerivative
          (fun point =>
            loweredLorentzConnectionCoefficient
              (actual.gravityConnection point)
              canonicalLorentzianTimeDirection internalPair)
          0 canonicalLorentzianTimeDirection =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).temporalGravityConnection space internalPair)
          0
  temporalGaugeConnection :
    p286GaugeConnectionCoordinateDerivative actual 0
        canonicalLorentzianTimeDirection canonicalLorentzianTimeDirection =
      deriv
        (fun time =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).temporalGaugeConnection space))
        0
  p286SpatialConnection :
    ∀ direction,
      p286GaugeConnectionCoordinateDerivative actual 0
          canonicalLorentzianTimeDirection direction.succ =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).gravityGauge.p286.spatialConnection space direction)
          0
  p286SpatialBFMomentum :
    ∀ direction,
      p286GaugeConnectionTemporalBFMomentumDerivative actual
          (canonicalP286SpatialGaugeOneForm direction) 0 =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).gravityGauge.p286.spatialBFMomentumEvaluation
                space direction)
          0
  lorentzSpatialConnection :
    ∀ direction internalPair,
      fieldDirectionalDerivative
          (fun point =>
            loweredLorentzConnectionCoefficient
              (actual.gravityConnection point) direction.succ internalPair)
          0 canonicalLorentzianTimeDirection =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).gravityGauge.lorentz.spatialConnection space direction
                internalPair)
          0
  lorentzSpatialBFMomentum :
    ∀ direction,
      lorentzConnectionTemporalBFMomentumDerivative actual
          (canonicalLorentzSpatialBivectorOneForm direction) 0 =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).gravityGauge.lorentz.spatialBFMomentumEvaluation
                space direction)
          0
  scalarCoordinate :
    fieldDirectionalDerivative actual.scalar 0
        canonicalLorentzianTimeDirection =
      deriv
        (fun time =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate source time
            state).scalar.scalarCoordinate space)
        0
  scalarTemporalMomentum :
    ∀ direction,
      fieldDirectionalDerivative
          (scalarDifferentialMomentum source actual direction
            canonicalLorentzianTimeDirection)
          0 canonicalLorentzianTimeDirection =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).scalar.temporalMomentumEvaluation space direction)
          0
  matter :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (actual.matter point))
        0 canonicalLorentzianTimeDirection =
      deriv
        (fun time =>
          matterCoordinateEquiv
            ((sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).matter space))
        0
  conjugateMatterEvaluation :
    ∀ matter,
      fieldDirectionalDerivative
          (fun point => actual.conjugateMatter point matter)
          0 canonicalLorentzianTimeDirection =
        deriv
          (fun time =>
            (sourceActionGeneratedJointCanonicalPhaseUpdate source time
              state).conjugateMatter space matter)
          0

theorem positivePathFirstJointLocalActualLift_firstJetLaw :
    StageNineJointCanonicalActualFirstJetLaw positiveSmoothUnifiedSource
      positivePhaseProbeCauchyState 0
        positivePathFirstJointLocalActualLift := by
  have pathLaw :=
    sourceActionGeneratedJointCanonicalPhasePath_hasGeneratedDerivative
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
  refine
    { coframe := ?_,
      simplicityMultiplier := ?_,
      temporalGravityConnection := ?_,
      temporalGaugeConnection := ?_,
      p286SpatialConnection := ?_,
      p286SpatialBFMomentum := ?_,
      lorentzSpatialConnection := ?_,
      lorentzSpatialBFMomentum := ?_,
      scalarCoordinate := ?_,
      scalarTemporalMomentum := ?_,
      matter := ?_,
      conjugateMatterEvaluation := ?_ }
  · intro internal coordinate
    rw [pathLaw.frozenCoframe 0 internal coordinate |>.deriv]
    exact
      positivePathFirstJointLocalActualLift_coframeTimeDerivative_zero
        internal coordinate
  · intro internalPair spacetimePair
    rw [pathLaw.simplicityMultiplier 0 internalPair spacetimePair |>.deriv]
    exact
      positivePathFirstJointLocalActualLift_multiplierTimeDerivative_zero
        internalPair spacetimePair
  · intro internalPair
    rw [pathLaw.temporalGravityConnection 0 internalPair |>.deriv]
    exact
      positivePathFirstJointLocalActualLift_temporalGravityTimeDerivative_zero
        internalPair
  · rw [pathLaw.temporalGaugeConnection 0 |>.deriv]
    exact
      positivePathFirstJointLocalActualLift_temporalGaugeTimeDerivative_zero
  · intro direction
    rw [pathLaw.p286SpatialConnection 0 direction |>.deriv]
    simpa [sourceActionGeneratedP286SpatialConnectionCoordinateVelocity] using
      positivePathFirstJointLocalActualLift_p286SpatialTimeDerivative
        direction
  · intro direction
    rw [pathLaw.p286SpatialBFMomentum 0 direction |>.deriv]
    rw [
      positivePathFirstJointLocalActualLift_p286TemporalBFDerivative_zero]
    exact
      (congrFun positiveP286SpatialBFMomentumVelocity_zero direction).symm
  · intro direction internalPair
    rw [pathLaw.lorentzSpatialConnection 0 direction internalPair |>.deriv]
    exact
      sourceActionGeneratedJointLocalActualLift_lorentzSpatialTimeDerivative
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
          direction internalPair
  · intro direction
    rw [pathLaw.lorentzSpatialBFMomentum 0 direction |>.deriv]
    rw [
      positivePathFirstJointLocalActualLift_lorentzTemporalBFDerivative_zero]
    exact
      (congrFun positiveLorentzSpatialBFMomentumVelocity_zero direction).symm
  · rw [pathLaw.scalarCoordinate 0 |>.deriv]
    exact positivePathFirstJointLocalActualLift_scalarTimeDerivative
  · intro direction
    rw [pathLaw.scalarTemporalMomentum 0 direction |>.deriv]
    rw [
      positivePathFirstJointLocalActualLift_scalarTemporalMomentumDerivative_zero]
    exact
      (congrFun positiveScalarTemporalMomentumVelocity_zero direction).symm
  · rw [pathLaw.matter 0 |>.deriv]
    exact positivePathFirstJointLocalActualLift_matterTimeDerivative
  · intro matter
    rw [pathLaw.conjugateMatterEvaluation 0 matter |>.deriv]
    exact
      positivePathFirstJointLocalActualLift_conjugateTimeDerivative matter

theorem
    positivePathFirstJointLocalActualLift_realizes_C3h100_initial_and_firstJet :
    StageNineJointCanonicalActualInitialLaw positiveSmoothUnifiedSource
        positivePhaseProbeCauchyState 0
          positivePathFirstJointLocalActualLift ∧
      StageNineJointCanonicalActualFirstJetLaw positiveSmoothUnifiedSource
        positivePhaseProbeCauchyState 0
          positivePathFirstJointLocalActualLift :=
  ⟨positivePathFirstJointLocalActualLift_initialLaw,
    positivePathFirstJointLocalActualLift_firstJetLaw⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineJointActionLocalActualLift
