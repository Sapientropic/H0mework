import H0mework.Physics.FixedJoint.FixedWrite
import H0mework.Physics.ConnectionJets.P286GaussRadialSecondJetLift

/-!
# Fixed P506/L0 joint-action zero-fiber acceptance

This module re-evaluates the complete nine-coordinate repaired-root residual
on the one same-source action successor.  The eight coordinates untouched by
the generated write are first read on that new actual.  The remaining P286
connection coordinate is then computed from the action-generated temporal
and Gauss response; only the final whole-carrier equality counts as closure.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionZeroFiber

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaussRadialSecondJetLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineTopologicalFourFormPairing
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedJointZeroP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedJointZeroP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

def fixedP506JointActionSuccessorResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    FixedP506JointActionSuccessor

theorem fixedP506JointActionSuccessor_gravityMultiplier_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField FixedP506JointActionSuccessor 0) =
      0
  rw [fixedP506JointActionSuccessor_pointField_origin]
  have old := fixedP506JointResidual_gravityMultiplier_zero 0
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField FixedP506JointActual 0) =
      0 at old
  exact old

theorem fixedP506JointActionSuccessor_gravityAuxiliary_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).gravityAuxiliary =
      0 := by
  change
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField FixedP506JointActionSuccessor 0) =
      0
  rw [fixedP506JointActionSuccessor_pointField_origin]
  have old := fixedP506JointResidual_gravityAuxiliary_zero 0
  change
    formNativeGravityAuxiliaryEulerResidual
        (toContinuumPointField FixedP506JointActual 0) =
      0 at old
  exact old

theorem fixedP506JointActionSuccessor_p286GaugeAuxiliary_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).p286GaugeAuxiliary =
      0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField FixedP506JointActionSuccessor 0) =
      0
  rw [fixedP506JointActionSuccessor_pointField_origin]
  have old := fixedP506JointResidual_p286GaugeAuxiliary_zero
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField FixedP506JointActual 0) =
      0 at old
  exact old

private theorem installGeneratedGaugeAuxiliaryGerm_lorentzEuler_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (installGeneratedGaugeAuxiliaryGerm base auxiliary) point =
      holonomicFormNativeLorentzEulerThreeForm source 0 base point := by
  rfl

theorem fixedP506JointActionSuccessor_lorentzConnection_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).lorentzConnection =
      0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActionSuccessor 0 =
      0
  rw [show
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActionSuccessor 0 =
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActual 0 by
      exact installGeneratedGaugeAuxiliaryGerm_lorentzEuler_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField 0]
  exact fixedP506JointResidual_lorentzConnection_origin_zero

private theorem installGeneratedGaugeAuxiliaryGerm_scalarEuler_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (installGeneratedGaugeAuxiliaryGerm base auxiliary) direction point =
      diracDualScalarEulerLagrangeDirectionalCoefficient source base direction
        point := by
  rfl

theorem fixedP506JointActionSuccessor_scalar_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).scalar = 0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActionSuccessor direction
          0 =
      0
  rw [show
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActionSuccessor direction
          0 =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 by
      exact installGeneratedGaugeAuxiliaryGerm_scalarEuler_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField direction 0]
  have old := congrFun fixedP506JointResidual_scalar_origin_zero direction
  exact old

private theorem installGeneratedGaugeAuxiliaryGerm_matterEuler_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    diracDualMatterEulerLagrangeDirectionalCoefficient source
        (installGeneratedGaugeAuxiliaryGerm base auxiliary) direction point =
      diracDualMatterEulerLagrangeDirectionalCoefficient source base direction
        point := by
  rfl

theorem fixedP506JointActionSuccessor_matter_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).matter = 0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActionSuccessor direction
          0 =
      0
  rw [show
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActionSuccessor direction
          0 =
      diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 by
      exact installGeneratedGaugeAuxiliaryGerm_matterEuler_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField direction 0]
  have old := congrFun fixedP506JointResidual_matter_origin_zero direction
  exact old

theorem fixedP506JointActionSuccessor_conjugateMatter_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506JointActionSuccessor direction 0 =
      0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [fixedP506JointActionSuccessor_pointField_origin]
  have old := fixedP506JointResidual_conjugateMatter_origin_zero
  change
    (fun candidate =>
      diracDualConjugateMatterDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual candidate 0) =
      0 at old
  have applied := congrFun old direction
  simpa only [diracDualConjugateMatterDirectionalCoefficient,
    Pi.zero_apply] using applied

theorem fixedP506JointActionSuccessor_coframe_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).coframe = 0 := by
  change
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField FixedP506JointActionSuccessor 0) =
      0
  rw [fixedP506JointActionSuccessor_pointField_origin]
  exact fixedP506JointResidual_coframe_origin_zero

/-! ## Action-generated auxiliary first jet -/

/-- The one continuous linear first jet generated by the temporal BF response
and the dimension-normalized Gauss response. -/
def fixedP506FormNativeJointActionAuxiliaryFirstJetLinear :
    BasePoint →L[ℝ] P286GaugeTwoForm :=
  (localBaseCoordinate canonicalLorentzianTimeDirection).smulRight
      (p286SpatialAuxiliaryVelocityEmbedding
        fixedP506FormNativeP286SpatialAuxiliaryVelocity) +
    p286GaussRadialAuxiliaryFirstJetLinear
      fixedP506FormNativeP286GaussCharge

private theorem
    fixedP506FormNativeJointActionAuxiliaryCoordinate_eq_affineFirstJet :
    fixedP506FormNativeJointActionAuxiliaryCoordinate =
      fun point =>
        fixedP506FormNativeJointActionAuxiliaryCoordinate 0 +
          fixedP506FormNativeJointActionAuxiliaryFirstJetLinear point := by
  funext point
  unfold fixedP506FormNativeJointActionAuxiliaryCoordinate
    fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
  rw [currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing,
    p286GaussRadialAuxiliaryProfile_eq_firstJetLinear]
  simp [localBaseCoordinate_apply]
  abel

theorem fixedP506JointActionSuccessor_auxiliaryCoordinate
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        FixedP506JointActionSuccessor point =
      fixedP506FormNativeJointActionAuxiliaryCoordinate point := by
  funext pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
    FixedP506JointActionSuccessor
  rw [installGeneratedGaugeAuxiliaryGerm_gaugeAuxiliary]
  exact p286CoordinateEquiv.apply_symm_apply _

theorem
    fixedP506JointActionSuccessor_auxiliaryDirectionalDerivative
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        FixedP506JointActionSuccessor 0 direction =
      fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
        (coordinateDirection direction) := by
  unfold p286GaugeAuxiliaryDirectionalDerivative
  have coordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate
          FixedP506JointActionSuccessor =
        fixedP506FormNativeJointActionAuxiliaryCoordinate := by
    funext point
    exact fixedP506JointActionSuccessor_auxiliaryCoordinate point
  rw [coordinateEquality,
    fixedP506FormNativeJointActionAuxiliaryCoordinate_eq_affineFirstJet]
  unfold fieldDirectionalDerivative
  rw [((fixedP506FormNativeJointActionAuxiliaryFirstJetLinear.hasFDerivAt)
    |>.const_add
      (fixedP506FormNativeJointActionAuxiliaryCoordinate 0)).fderiv]

private theorem fixedP506FormNativeJointActionAuxiliaryFirstJetLinear_time :
    fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
        (coordinateDirection canonicalLorentzianTimeDirection) =
      p286SpatialAuxiliaryVelocityEmbedding
        fixedP506FormNativeP286SpatialAuxiliaryVelocity := by
  unfold fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
  rw [add_apply]
  simp [localBaseCoordinate_apply, coordinateDirection,
    canonicalLorentzianTimeDirection,
    p286GaussRadialAuxiliaryFirstJetLinear,
    p286BaseCoordinate_apply,
    Fin.sum_univ_three]

private theorem
    fixedP506FormNativeJointActionAuxiliaryFirstJetLinear_spatial
    (axis : Fin 3) :
    fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
        (coordinateDirection axis.succ) =
      (1 / 3 : ℝ) •
        p286GaussAuxiliaryAxisEmbedding
          fixedP506FormNativeP286GaussCharge axis := by
  have radial :=
    p286GaussRadialAuxiliaryProfile_spatialFirstJet
      fixedP506FormNativeP286GaussCharge axis
  rw [p286GaussRadialAuxiliaryProfile_directionalDerivative] at radial
  unfold fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
  rw [add_apply, radial]
  fin_cases axis <;>
    simp [localBaseCoordinate_apply, coordinateDirection,
      canonicalLorentzianTimeDirection]

private theorem fixedP506FormNativeP286ActionTarget_decomposition
    (direction : P286GaugeOneForm) :
    fixedP506FormNativeP286ActionTarget direction =
      fixedP506FormNativeP286TemporalActionTarget
          (direction canonicalLorentzianTimeDirection) +
        fixedP506FormNativeP286SpatialActionTarget
          (fun index => direction index.succ) := by
  calc
    fixedP506FormNativeP286ActionTarget direction =
        fixedP506FormNativeP286ActionTarget
          (p286TemporalGaugeOneForm
              (direction canonicalLorentzianTimeDirection) +
            canonicalP286SpatialGaugeOneForm
              (fun index => direction index.succ)) :=
      congrArg fixedP506FormNativeP286ActionTarget
        (StageNineCurrentP286CompleteActionResponseOperator.p286GaugeOneForm_eq_temporal_add_canonicalSpatial
          direction)
    _ =
        fixedP506FormNativeP286ActionTarget
            (p286TemporalGaugeOneForm
              (direction canonicalLorentzianTimeDirection)) +
          fixedP506FormNativeP286ActionTarget
            (canonicalP286SpatialGaugeOneForm
              (fun index => direction index.succ)) := by
      rw [map_add]
    _ = _ := by
      rfl

private theorem formNativeP286GaugeExteriorDerivativeDirection_eq_pointwise
    (derivativeDirection : LorentzianIndex)
    (direction : P286GaugeOneForm) :
    StageNineFormNativeP286GaugeDerivativeIntegrationByParts.p286GaugeExteriorDerivativeDirection
        derivativeDirection direction =
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeExteriorDerivativeDirection
        derivativeDirection direction := by
  rfl

private theorem fixedP506FormNativeJointAction_timePrincipal
    (direction : P286GaugeOneForm) :
    p286GaugeExteriorPrincipalBilinear
        canonicalLorentzianTimeDirection
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection canonicalLorentzianTimeDirection))
        direction =
      -fixedP506FormNativeP286SpatialActionTarget
        (fun index => direction index.succ) := by
  rw [fixedP506FormNativeJointActionAuxiliaryFirstJetLinear_time]
  change
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (p286SpatialAuxiliaryVelocityEmbedding
          fixedP506FormNativeP286SpatialAuxiliaryVelocity)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection direction) =
      _
  have convention :=
    fixedIdentityP286HodgePairing_eq_neg_topologicalWedge
      (p286SpatialAuxiliaryVelocityEmbedding
        fixedP506FormNativeP286SpatialAuxiliaryVelocity)
      (p286GaugeExteriorDerivativeDirection
        canonicalLorentzianTimeDirection direction)
  calc
    _ =
        -p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding
            fixedP506FormNativeP286SpatialAuxiliaryVelocity)
          (p286GaugeExteriorDerivativeDirection
            canonicalLorentzianTimeDirection direction) := by
      linarith
    _ =
        -p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding
            fixedP506FormNativeP286SpatialAuxiliaryVelocity)
          (StageNineP286GaugeConnectionPointwiseEquation.p286GaugeExteriorDerivativeDirection
            canonicalLorentzianTimeDirection
            (canonicalP286SpatialGaugeOneForm
              (fun index => direction index.succ))) := by
      rw [formNativeP286GaugeExteriorDerivativeDirection_eq_pointwise,
        p286TimeExterior_fullDirection]
    _ =
        -p286SpatialBFLegendreDualOperator
          fixedP506FormNativeP286SpatialAuxiliaryVelocity
          (fun index => direction index.succ) := by
      rw [identityP286SpatialBFLegendre_normalForm]
      rfl
    _ = _ := by
      rw [fixedP506FormNativeP286SpatialAuxiliaryVelocity_response]

private theorem fixedP506FormNativeJointAction_spatialPrincipal
    (direction : P286GaugeOneForm)
    (axis : Fin 3) :
    p286GaugeExteriorPrincipalBilinear axis.succ
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection axis.succ))
        direction =
      -(1 / 3 : ℝ) *
        fixedP506FormNativeP286TemporalActionTarget
          (direction canonicalLorentzianTimeDirection) := by
  rw [fixedP506FormNativeJointActionAuxiliaryFirstJetLinear_spatial]
  change
    generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        ((1 / 3 : ℝ) •
          p286GaussAuxiliaryAxisEmbedding
            fixedP506FormNativeP286GaussCharge axis)
        (p286GaugeExteriorDerivativeDirection axis.succ direction) =
      _
  rw [p286TopologicalGaugeBFCoefficient_smul_left]
  have convention :=
    fixedIdentityP286HodgePairing_eq_neg_topologicalWedge
      (p286GaussAuxiliaryAxisEmbedding
        fixedP506FormNativeP286GaussCharge axis)
      (p286GaugeExteriorDerivativeDirection axis.succ direction)
  calc
    (1 / 3 : ℝ) *
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (p286GaussAuxiliaryAxisEmbedding
            fixedP506FormNativeP286GaussCharge axis)
          (p286GaugeExteriorDerivativeDirection axis.succ direction) =
      -(1 / 3 : ℝ) *
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding
            fixedP506FormNativeP286GaussCharge axis)
          (p286GaugeExteriorDerivativeDirection axis.succ direction) := by
      linarith
    _ =
      -(1 / 3 : ℝ) *
        p286CoordinateLiePairing fixedP506FormNativeP286GaussCharge
          (direction canonicalLorentzianTimeDirection) := by
      rw [formNativeP286GaugeExteriorDerivativeDirection_eq_pointwise,
        identityP286GaussAxisMomentum_fullDirection]
    _ = _ := by
      rw [fixedP506FormNativeP286GaussCharge_response]

theorem fixedP506FormNativeJointAction_principalSum
    (direction : P286GaugeOneForm) :
    (∑ derivativeDirection : LorentzianIndex,
      p286GaugeExteriorPrincipalBilinear derivativeDirection
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection derivativeDirection))
        direction) =
      -fixedP506FormNativeP286ActionTarget direction := by
  rw [Fin.sum_univ_four]
  have time := fixedP506FormNativeJointAction_timePrincipal direction
  simp only [canonicalLorentzianTimeDirection] at time
  rw [time]
  have first :=
    fixedP506FormNativeJointAction_spatialPrincipal direction 0
  have second :=
    fixedP506FormNativeJointAction_spatialPrincipal direction 1
  have third :=
    fixedP506FormNativeJointAction_spatialPrincipal direction 2
  change
    p286GaugeExteriorPrincipalBilinear 1
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection 1)) direction =
      _ at first
  change
    p286GaugeExteriorPrincipalBilinear 2
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection 2)) direction =
      _ at second
  change
    p286GaugeExteriorPrincipalBilinear 3
        (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection 3)) direction =
      _ at third
  rw [first, second, third,
    fixedP506FormNativeP286ActionTarget_decomposition]
  ring

private theorem
    fixedP506JointActionSuccessor_exteriorDerivative_wedge_eq_target
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorDerivative
          FixedP506JointActionSuccessor 0) =
      fixedP506FormNativeP286ActionTarget direction := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  have derivativeEquality :
      p286GaugeAuxiliaryDirectionalDerivative
          FixedP506JointActionSuccessor 0 =
        fun derivativeDirection =>
          fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
            (coordinateDirection derivativeDirection) := by
    funext derivativeDirection
    exact
      fixedP506JointActionSuccessor_auxiliaryDirectionalDerivative
        derivativeDirection
  rw [derivativeEquality]
  calc
    _ =
        -(∑ derivativeDirection : LorentzianIndex,
          p286GaugeExteriorPrincipalBilinear derivativeDirection
            (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
              (coordinateDirection derivativeDirection))
            direction) := by
      exact
        (p286GaugeExteriorPrincipalSum_eq_w13
          (fun derivativeDirection =>
            fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
              (coordinateDirection derivativeDirection))
          direction).symm
    _ = _ := by
      rw [fixedP506FormNativeJointAction_principalSum]
      simp

private theorem
    fixedP506JointActionSuccessor_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate
        FixedP506JointActionSuccessor 0 =
      0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [fixedP506JointActionSuccessor_gaugeConnection]
  exact fixedP506JointActual_gaugeConnectionCoordinate_origin_zero

private theorem fixedP506_zeroConnectionExteriorAction
    (value : P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction 0 value = 0 := by
  have adjointZero : p286GaugeTwoFormAdjoint 0 value = 0 := by
    funext pair
    simp [p286GaugeTwoFormAdjoint]
  funext triple
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [Pi.zero_apply, zero_add]
  rw [adjointZero]
  simp

private theorem
    fixedP506JointActionSuccessor_covariantDerivative_wedge_eq_target
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          FixedP506JointActionSuccessor 0) =
      fixedP506FormNativeP286ActionTarget direction := by
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    fixedP506JointActionSuccessor_exteriorDerivative_wedge_eq_target,
    fixedP506JointActionSuccessor_gaugeConnectionCoordinate_origin_zero,
    fixedP506_zeroConnectionExteriorAction]
  simp [p286GaugeOneFormThreeFormWedgeCoefficient]

theorem fixedP506JointActionSuccessor_p286GaugeConnection_origin_zero :
    (fixedP506JointActionSuccessorResidualSection 0).p286GaugeConnection =
      0 := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActionSuccessor 0 =
      0
  calc
    _ = p286GaugeThreeFormOfDual 0 := by
      apply p286GaugeThreeFormOfDual_unique
      intro direction
      unfold holonomicFormNativeP286GaugeEulerThreeForm
      rw [p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
        fixedP506JointActionSuccessor_covariantDerivative_wedge_eq_target,
        formNativeChargedGaugeThreeForm_evaluation,
        fixedP506JointActionSuccessor_pointField_origin]
      have targetEquality :=
        DFunLike.congr_fun
          fixedP506FormNativeP286ActionTarget_eq_neg_charged direction
      simpa only [LinearMap.zero_apply, LinearMap.neg_apply,
        formNativeChargedGaugeFirstLinearMap_apply] using
          add_eq_zero_iff_eq_neg.mpr targetEquality
    _ = 0 := by
      unfold p286GaugeThreeFormOfDual
      exact map_zero p286GaugeThreeFormWedgeEquiv.symm

/-- Complete nine-coordinate zero fiber on the one generated successor at
the fixed P506/L0 contact. -/
theorem fixedP506JointActionSuccessorResidual_origin_zero :
    fixedP506JointActionSuccessorResidualSection 0 = 0 := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact fixedP506JointActionSuccessor_gravityMultiplier_origin_zero
  · exact fixedP506JointActionSuccessor_gravityAuxiliary_origin_zero
  · exact fixedP506JointActionSuccessor_p286GaugeAuxiliary_origin_zero
  · exact fixedP506JointActionSuccessor_lorentzConnection_origin_zero
  · exact fixedP506JointActionSuccessor_p286GaugeConnection_origin_zero
  · exact fixedP506JointActionSuccessor_scalar_origin_zero
  · exact fixedP506JointActionSuccessor_matter_origin_zero
  · exact fixedP506JointActionSuccessor_conjugateMatter_origin_zero
  · exact fixedP506JointActionSuccessor_coframe_origin_zero

theorem fixedP506JointActionSuccessor_onPointwiseZeroFiber :
    OnDiracDualFormNativePointwiseJointZeroFiber positiveSmoothUnifiedSource
      FixedP506JointActionSuccessor 0 := by
  exact fixedP506JointActionSuccessorResidual_origin_zero

theorem fixedP506JointActionSuccessor_ne_current :
    FixedP506JointActionSuccessor ≠ FixedP506JointActual := by
  intro sameActual
  apply fixedP506JointResidual_origin_ne_zero
  change
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        FixedP506JointActual 0 =
      0
  rw [← sameActual]
  exact fixedP506JointActionSuccessorResidual_origin_zero

/-- Negative/positive regression on the same source and contact: the old
common actual remains outside the zero fiber, while its action-generated
successor lies in it. -/
theorem fixedP506JointActionWrite_origin_regression :
    fixedP506JointResidualSection 0 ≠ 0 ∧
      fixedP506JointActionSuccessorResidualSection 0 = 0 ∧
      FixedP506JointActionSuccessor ≠ FixedP506JointActual :=
  ⟨fixedP506JointResidual_origin_ne_zero,
    fixedP506JointActionSuccessorResidual_origin_zero,
    fixedP506JointActionSuccessor_ne_current⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
