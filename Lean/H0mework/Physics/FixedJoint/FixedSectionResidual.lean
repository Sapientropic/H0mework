import H0mework.Physics.FixedJoint.FixedSixSectorClosure

/-!
# Fixed P506/L0 joint-action successor section residual

This module computes the complete pointwise residual section of the existing
source/action-generated joint successor.  The auxiliary write changes exactly
the three action channels that depend on the P286 two-form:

* the P286 auxiliary equation,
* the P286 connection equation, and
* the coframe equation.

The other six coordinates are transported from the same predecessor actual.
For the connection channel, the generated auxiliary field is reduced to its
actual affine first jet, so the normal form contains no opaque derivative of
the written field.

This is a diagnostic/readout checkpoint, not a new hard gate and not a write
producer.  In particular, neither the support of this section nor its
coordinatewise negative may be used to define a successor.  Any later write
must be generated forward by the same source/current action operator; this
complete section may then be substituted only as its consistency regression.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSectionResidual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaussRadialSecondJetLift
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedP286ResponseReplay
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance probeP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance probeP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Exact source/action normal form of the written auxiliary -/

theorem fixedP506FormNativeGaussCharge_eq_neg_current :
    fixedP506FormNativeP286GaussCharge =
      -currentP286GaussCharge positiveSmoothUnifiedSource
        FixedP506JointActual := by
  unfold fixedP506FormNativeP286GaussCharge currentP286GaussCharge
  rw [show
    fixedP506FormNativeP286TemporalActionTarget =
      -currentP286TemporalActionTarget positiveSmoothUnifiedSource
        FixedP506JointActual by
      apply LinearMap.ext
      intro component
      exact congrArg
        (fun target : Module.Dual ℝ P286GaugeOneForm =>
          target (p286TemporalGaugeOneForm component))
        fixedP506FormNativeP286ActionTarget_eq_neg_currentAction]
  exact map_neg p286CoordinateLiePairingEquiv.symm
    (currentP286TemporalActionTarget positiveSmoothUnifiedSource
      FixedP506JointActual)

theorem fixedP506FormNativeSpatialVelocity_eq_neg_current :
    fixedP506FormNativeP286SpatialAuxiliaryVelocity =
      -currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        FixedP506JointActual := by
  unfold fixedP506FormNativeP286SpatialAuxiliaryVelocity
    currentP286SpatialAuxiliaryVelocity
  rw [show
    fixedP506FormNativeP286SpatialActionTarget =
      -currentP286SpatialActionTarget positiveSmoothUnifiedSource
        FixedP506JointActual by
      apply LinearMap.ext
      intro direction
      exact congrArg
        (fun target : Module.Dual ℝ P286GaugeOneForm =>
          target (canonicalP286SpatialGaugeOneForm direction))
        fixedP506FormNativeP286ActionTarget_eq_neg_currentAction]
  exact map_neg p286SpatialBFLegendreEquiv.symm
    (currentP286SpatialActionTarget positiveSmoothUnifiedSource
      FixedP506JointActual)

theorem fixedP506JointActual_fullActionTarget_eq_UStar :
    currentP286FullActionTarget positiveSmoothUnifiedSource
        FixedP506JointActual =
      currentP286FullActionTarget positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift := by
  apply LinearMap.ext
  intro direction
  apply p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
    positiveSmoothUnifiedSource FixedP506JointActual
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0
  · rw [fixedGlobalMatterDualP286Complete_coframe_origin,
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one]
  · funext formDirection
    apply p286CoordinateEquiv.injective
    change
      holonomicP286GaugeConnectionCoordinate FixedP506JointActual 0
          formDirection =
        holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0
          formDirection
    rw [congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
      formDirection]
    change
      0 =
        holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0
          formDirection
    rw [show
      holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
        c3h181U7ConnectionNormalForm 0 by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [currentUStar_gaugeConnection_eq_currentU7]
      exact
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
          0]
    simp [c3h181U7ConnectionNormalForm]
  · rw [fixedP506JointActual_gaugeAuxiliary_origin_eq_sourceCauchy]
    unfold positiveP506MatterCurrentFullSynchronizedCauchyState
      canonicalCauchyRestriction
    change
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
          (canonicalCauchySlicePoint 0 0) =
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
          0
    rw [canonicalCauchySlicePoint_zero_zero]
  · rw [fixedP506JointActual_scalar_origin]
    symm
    rw [
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_scalar,
      positiveP506MatterCurrentMatterResponseLocalActualLift_scalar,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_scalar]
    rw [congrFun
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.1
      0,
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalar_vacuum]
  · funext derivativeDirection
    rw [fixedP506JointActual_scalarCovariantDerivative_origin_zero]
    symm
    unfold holonomicScalarCovariantDerivative
    rw [
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_scalar,
      positiveP506MatterCurrentMatterResponseLocalActualLift_scalar,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_scalar,
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeConnection,
      positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeConnection,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeConnection,
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.1,
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.1]
    exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarCovariantDerivative_origin_zero
        derivativeDirection
  · rw [fixedP506JointActual_matter_origin]
    symm
    rw [
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_matter,
      positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_matter]
    rw [congrFun
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.1
      0]
    exact currentU7_matter_origin
  · rw [fixedP506JointActual_conjugateMatter_origin]
    symm
    rw [
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_conjugateMatter,
      positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_conjugateMatter]
    rw [congrFun
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.2
      0]
    exact
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin

theorem fixedP506JointActual_gaussCharge_eq_U7 :
    currentP286GaussCharge positiveSmoothUnifiedSource FixedP506JointActual =
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  unfold currentP286GaussCharge
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
  congr 1
  unfold currentP286TemporalActionTarget
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
  rw [fixedP506JointActual_fullActionTarget_eq_UStar,
    positiveP506MatterCurrentUStarP286FullActionTarget_eq_U7]
  apply LinearMap.ext
  intro component
  rfl

theorem fixedP506JointActual_spatialVelocity_eq_U7 :
    currentP286SpatialAuxiliaryVelocity positiveSmoothUnifiedSource
        FixedP506JointActual =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity := by
  unfold currentP286SpatialAuxiliaryVelocity
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity
  congr 1
  unfold currentP286SpatialActionTarget
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget
  rw [fixedP506JointActual_fullActionTarget_eq_UStar,
    positiveP506MatterCurrentUStarP286FullActionTarget_eq_U7]
  apply LinearMap.ext
  intro direction
  rfl

theorem fixedP506FormNativeGaussCharge_eq_neg_U7 :
    fixedP506FormNativeP286GaussCharge =
      -positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  rw [fixedP506FormNativeGaussCharge_eq_neg_current,
    fixedP506JointActual_gaussCharge_eq_U7]

theorem fixedP506FormNativeSpatialVelocity_eq_neg_U7 :
    fixedP506FormNativeP286SpatialAuxiliaryVelocity =
      -positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity := by
  rw [fixedP506FormNativeSpatialVelocity_eq_neg_current,
    fixedP506JointActual_spatialVelocity_eq_U7]

theorem fixedP506JointActual_originAuxiliaryCoordinate_eq_U8 :
    currentP286OriginAuxiliaryCoordinate FixedP506JointActual =
      c3h181FullAuxiliaryCoordinateNormalForm 0 := by
  funext pair
  unfold currentP286OriginAuxiliaryCoordinate
  rw [fixedP506JointActual_gaugeAuxiliary_origin_eq_sourceCauchy]
  unfold positiveP506MatterCurrentFullSynchronizedCauchyState
    canonicalCauchyRestriction
  change
    p286CoordinateEquiv
        (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
          (canonicalCauchySlicePoint 0 0) pair) =
      c3h181FullAuxiliaryCoordinateNormalForm 0 pair
  rw [canonicalCauchySlicePoint_zero_zero]
  change
    holonomicP286GaugeAuxiliaryCoordinate
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 pair =
      c3h181FullAuxiliaryCoordinateNormalForm 0 pair
  rw [
    congrFun
      (positiveP506MatterCurrentP286CompleteResponseLocalActualLift_auxiliaryCoordinate
        0)
      pair,
    congrFun
      (positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_normalForm
        0)
      pair]

/-- Explicit all-point form of the auxiliary generated by the authoritative
form-native action.  The reflection is a theorem about the two action-owned
linear equivalences; it is not selected from a residual sign. -/
def fixedP506FormNativeJointActionAuxiliaryNormalForm
    (point : BasePoint) : P286GaugeTwoForm :=
  c3h181FullAuxiliaryCoordinateNormalForm (-point)

theorem fixedP506FormNativeJointActionAuxiliaryCoordinate_normalForm
    (point : BasePoint) :
    fixedP506FormNativeJointActionAuxiliaryCoordinate point =
      fixedP506FormNativeJointActionAuxiliaryNormalForm point := by
  unfold fixedP506FormNativeJointActionAuxiliaryCoordinate
    fixedP506FormNativeJointActionAuxiliaryNormalForm
  change
    currentP286OriginAuxiliaryCoordinate FixedP506JointActual +
          point canonicalLorentzianTimeDirection •
            p286SpatialAuxiliaryVelocityEmbedding
              fixedP506FormNativeP286SpatialAuxiliaryVelocity +
        currentP286CanonicalGaussRadialAuxiliaryProfile
          fixedP506FormNativeP286GaussCharge point =
      c3h181FullAuxiliaryCoordinateNormalForm (-point)
  rw [fixedP506JointActual_originAuxiliaryCoordinate_eq_U8,
    fixedP506FormNativeSpatialVelocity_eq_neg_U7,
    fixedP506FormNativeGaussCharge_eq_neg_U7,
    currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing]
  funext pair
  fin_cases pair <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      p286GaussRadialAuxiliaryProfile, p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      currentSpatialAuxiliaryVelocity_eq_thirdNegCharge,
      p286SpatialThirdOnly, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] <;>
    module

def fixedP506JointActionSuccessorPointFieldNormalForm
    (point : BasePoint) : StageNineContinuumPointField :=
  withFormNativeP286GaugeAuxiliary
    (toContinuumPointField FixedP506JointActual point)
    (fixedP506FormNativeJointActionAuxiliaryField point)

private theorem installGeneratedGaugeAuxiliaryGerm_pointField_normalForm
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    toContinuumPointField
        (installGeneratedGaugeAuxiliaryGerm base auxiliary) point =
      withFormNativeP286GaugeAuxiliary
        (toContinuumPointField base point) (auxiliary point) := by
  apply StageNineContinuumPointField.ext <;> rfl

theorem fixedP506JointActionSuccessor_pointField_normalForm
    (point : BasePoint) :
    toContinuumPointField FixedP506JointActionSuccessor point =
      fixedP506JointActionSuccessorPointFieldNormalForm point :=
  installGeneratedGaugeAuxiliaryGerm_pointField_normalForm
    FixedP506JointActual fixedP506FormNativeJointActionAuxiliaryField point

theorem
    fixedP506FormNativeJointActionAuxiliaryCoordinate_affine
    (point : BasePoint) :
    fixedP506FormNativeJointActionAuxiliaryCoordinate point =
      fixedP506FormNativeJointActionAuxiliaryCoordinate 0 +
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear point := by
  unfold fixedP506FormNativeJointActionAuxiliaryCoordinate
    fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
  rw [currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing,
    p286GaussRadialAuxiliaryProfile_eq_firstJetLinear]
  simp [localBaseCoordinate_apply]
  abel

theorem
    fixedP506JointActionSuccessor_auxiliaryDirectionalDerivative_at
    (point : BasePoint)
    (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        FixedP506JointActionSuccessor point direction =
      fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
        (coordinateDirection direction) := by
  unfold p286GaugeAuxiliaryDirectionalDerivative
  have coordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate
          FixedP506JointActionSuccessor =
        fixedP506FormNativeJointActionAuxiliaryCoordinate := by
    funext candidate
    exact fixedP506JointActionSuccessor_auxiliaryCoordinate candidate
  rw [coordinateEquality]
  have affineEquality :
      fixedP506FormNativeJointActionAuxiliaryCoordinate =
        fun candidate =>
          fixedP506FormNativeJointActionAuxiliaryCoordinate 0 +
            fixedP506FormNativeJointActionAuxiliaryFirstJetLinear candidate := by
    funext candidate
    exact
      fixedP506FormNativeJointActionAuxiliaryCoordinate_affine candidate
  rw [affineEquality]
  unfold fieldDirectionalDerivative
  have derivativeEquality :
      fderiv ℝ
          (fun candidate =>
            fixedP506FormNativeJointActionAuxiliaryCoordinate 0 +
              fixedP506FormNativeJointActionAuxiliaryFirstJetLinear candidate)
          point =
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear :=
    ((fixedP506FormNativeJointActionAuxiliaryFirstJetLinear.hasFDerivAt
      (x := point))
      |>.const_add
        (fixedP506FormNativeJointActionAuxiliaryCoordinate 0)).fderiv
  rw [derivativeEquality]

def fixedP506JointActionSuccessorP286ConnectionNormalForm
    (point : BasePoint) : P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (holonomicP286GaugeConnectionCoordinate FixedP506JointActual point)
      (fixedP506FormNativeJointActionAuxiliaryCoordinate point)
      (fun direction =>
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection direction)) +
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (fixedP506JointActionSuccessorPointFieldNormalForm point)

theorem
    fixedP506JointActionSuccessor_p286GaugeConnection_normalForm
    (point : BasePoint) :
    (fixedP506JointActionSuccessorResidualSection point
      ).p286GaugeConnection =
      fixedP506JointActionSuccessorP286ConnectionNormalForm point := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm
        positiveSmoothUnifiedSource 0 FixedP506JointActionSuccessor point =
      fixedP506JointActionSuccessorP286ConnectionNormalForm point
  unfold holonomicFormNativeP286GaugeEulerThreeForm
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    fixedP506JointActionSuccessorP286ConnectionNormalForm
  have connectionCoordinateEq :
      holonomicP286GaugeConnectionCoordinate
          FixedP506JointActionSuccessor point =
        holonomicP286GaugeConnectionCoordinate FixedP506JointActual point := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [fixedP506JointActionSuccessor_gaugeConnection]
  have auxiliaryDerivativeEq :
      p286GaugeAuxiliaryDirectionalDerivative
          FixedP506JointActionSuccessor point =
        fun direction =>
          fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
            (coordinateDirection direction) := by
    funext direction
    exact
      fixedP506JointActionSuccessor_auxiliaryDirectionalDerivative_at
        point direction
  rw [connectionCoordinateEq,
    fixedP506JointActionSuccessor_auxiliaryCoordinate,
    auxiliaryDerivativeEq,
    fixedP506JointActionSuccessor_pointField_normalForm]

private theorem
    installGeneratedGaugeAuxiliaryGerm_gravityMultiplierResidual_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (installGeneratedGaugeAuxiliaryGerm base auxiliary) point
      ).gravityMultiplier =
      (diracDualFormNativePointwiseJointResidual source base point
        ).gravityMultiplier := by
  rfl

private theorem
    installGeneratedGaugeAuxiliaryGerm_gravityAuxiliaryResidual_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (installGeneratedGaugeAuxiliaryGerm base auxiliary) point
      ).gravityAuxiliary =
      (diracDualFormNativePointwiseJointResidual source base point
        ).gravityAuxiliary := by
  rfl

private theorem
    installGeneratedGaugeAuxiliaryGerm_lorentzConnectionResidual_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (installGeneratedGaugeAuxiliaryGerm base auxiliary) point
      ).lorentzConnection =
      (diracDualFormNativePointwiseJointResidual source base point
        ).lorentzConnection := by
  rfl

private theorem installGeneratedGaugeAuxiliaryGerm_scalarResidual_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (installGeneratedGaugeAuxiliaryGerm base auxiliary) point
      ).scalar =
      (diracDualFormNativePointwiseJointResidual source base point).scalar := by
  rfl

private theorem installGeneratedGaugeAuxiliaryGerm_matterResidual_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (installGeneratedGaugeAuxiliaryGerm base auxiliary) point
      ).matter =
      (diracDualFormNativePointwiseJointResidual source base point).matter := by
  rfl

private theorem
    installGeneratedGaugeAuxiliaryGerm_conjugateMatterResidual_eq
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (installGeneratedGaugeAuxiliaryGerm base auxiliary) point
      ).conjugateMatter =
      (diracDualFormNativePointwiseJointResidual source base point
        ).conjugateMatter := by
  rfl

def fixedP506JointActionSuccessorResidualSectionNormalForm
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { gravityMultiplier :=
      (fixedP506JointResidualSection point).gravityMultiplier
    gravityAuxiliary :=
      (fixedP506JointResidualSection point).gravityAuxiliary
    p286GaugeAuxiliary :=
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506JointActionSuccessorPointFieldNormalForm point)
    lorentzConnection :=
      (fixedP506JointResidualSection point).lorentzConnection
    p286GaugeConnection :=
      fixedP506JointActionSuccessorP286ConnectionNormalForm point
    scalar := (fixedP506JointResidualSection point).scalar
    matter := (fixedP506JointResidualSection point).matter
    conjugateMatter :=
      (fixedP506JointResidualSection point).conjugateMatter
    coframe :=
      diracDualFormNativeCoframeEulerCovector
        positiveSmoothUnifiedSource point
        (fixedP506JointActionSuccessorPointFieldNormalForm point) }

theorem fixedP506JointActionSuccessorResidualSection_normalForm
    (point : BasePoint) :
    fixedP506JointActionSuccessorResidualSection point =
      fixedP506JointActionSuccessorResidualSectionNormalForm point := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      installGeneratedGaugeAuxiliaryGerm_gravityMultiplierResidual_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField point
  · exact
      installGeneratedGaugeAuxiliaryGerm_gravityAuxiliaryResidual_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField point
  · change
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (toContinuumPointField FixedP506JointActionSuccessor point) =
        formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (fixedP506JointActionSuccessorPointFieldNormalForm point)
    rw [fixedP506JointActionSuccessor_pointField_normalForm]
  · exact
      installGeneratedGaugeAuxiliaryGerm_lorentzConnectionResidual_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField point
  · exact
      fixedP506JointActionSuccessor_p286GaugeConnection_normalForm point
  · exact
      installGeneratedGaugeAuxiliaryGerm_scalarResidual_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField point
  · exact
      installGeneratedGaugeAuxiliaryGerm_matterResidual_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField point
  · exact
      installGeneratedGaugeAuxiliaryGerm_conjugateMatterResidual_eq
        positiveSmoothUnifiedSource FixedP506JointActual
        fixedP506FormNativeJointActionAuxiliaryField point
  · change
      diracDualFormNativeCoframeEulerCovector
          positiveSmoothUnifiedSource point
          (toContinuumPointField FixedP506JointActionSuccessor point) =
        diracDualFormNativeCoframeEulerCovector
          positiveSmoothUnifiedSource point
          (fixedP506JointActionSuccessorPointFieldNormalForm point)
    rw [fixedP506JointActionSuccessor_pointField_normalForm]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
