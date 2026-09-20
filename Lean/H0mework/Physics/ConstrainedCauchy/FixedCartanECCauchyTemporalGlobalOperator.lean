import H0mework.Physics.CartanAction.CartanECCauchyTemporalGlobalOperator
import H0mework.Physics.GravityTail.FixedInputRegularity
import H0mework.Physics.CoframeVariation.CoframeECCurvatureTargetLocalRegularity
import H0mework.Physics.CoframeVariation.CoframeGaugeEulerParameterContinuity
import H0mework.Physics.CoframeVariation.CoframeMatterEulerParameterContinuity
import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity
import H0mework.Physics.GravityTail.FixedCoframeLoadTemporalSpatial01
import H0mework.Physics.SynchronizedJoint.FixedJointSuccessorLorentzTemporalTrace
import H0mework.Physics.DualVariation.FourLegCriticalLocusCorrespondence
import H0mework.Physics.CoframeVariation.IIPlusCoframeECBalance
import H0mework.Physics.DualVariation.JointResidualCarrier

/-!
# Fixed P506/L0 Cartan--EC Cauchy temporal successor

This module specializes the source/current-only Cauchy gravity writer to the
exact action-selected P506/L0 gravity prefix.  It replaces the rejected
four-dimensional radial connection compiler; it does not consume that
actual's residual, support, `q1` coordinate, target field, or zero-fiber
receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator

open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTangentSimplicityResponse
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeFirstJet
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
open StageNineDiracDualFormNativeFixedP506ActionSelectedJointSuccessorLorentzTemporalTrace
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailInputRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

local instance fixedCartanTorsionNormedAddCommGroup :
    NormedAddCommGroup PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.normedAddCommGroup

local instance fixedCartanTorsionNormedSpace :
    NormedSpace ℝ PointwiseCartanTorsionTwoForm :=
  pointwiseCartanTorsionTwoFormCoordinateEquiv.normedSpace ℝ

private def fixedCartanTorsionCoordinateLinearEquiv :
    PointwiseCartanTorsionTwoForm ≃ₗ[ℝ]
      (Fin 6 → LorentzianIndex → ℝ) where
  toFun := PointwiseCartanTorsionTwoForm.component
  invFun := PointwiseCartanTorsionTwoForm.mk
  left_inv torsion := by cases torsion; rfl
  right_inv _ := rfl
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar torsion; rfl

local instance fixedCartanTorsionFiniteDimensional :
    FiniteDimensional ℝ PointwiseCartanTorsionTwoForm :=
  FiniteDimensional.of_injective
    fixedCartanTorsionCoordinateLinearEquiv.toLinearMap
    fixedCartanTorsionCoordinateLinearEquiv.injective

local instance fixedProfileP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity.p286CoordinateIndexFintype

local instance fixedProfileMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private def fixedLorentzBivectorOneFormConnectionLinearMap :
    LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun := lorentzSkewConnectionOfBivectorOneForm
  map_add' := lorentzSkewConnectionOfBivectorOneForm_add
  map_smul' := lorentzSkewConnectionOfBivectorOneForm_smul

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

/-- Exact action-selected current preceding the rejected radial path. -/
def fixedP506L0CartanECCauchyTemporalInput :
    StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Coupled

/-- Pointwise Cartan/reaction restart used by the Cauchy compiler. -/
def fixedP506L0CartanECCauchyTemporalBase :
    StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source fixedP506L0CartanECCauchyTemporalInput

/-- One source-native P506/L0 Cauchy-temporal successor. -/
def fixedP506L0CartanECCauchyTemporalGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    Source fixedP506L0CartanECCauchyTemporalInput

private abbrev Input := fixedP506L0CartanECCauchyTemporalInput
private abbrev Base := fixedP506L0CartanECCauchyTemporalBase
private abbrev Output := fixedP506L0CartanECCauchyTemporalGlobalActual

private def OutputField (space : StageNineSpatialPoint) :
    StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (toContinuumPointField Output (canonicalCauchySlicePoint 0 space))

private theorem input_smooth : Input.Smooth :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_smooth

@[simp] theorem fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one :
    Input.coframe = fun _ => (1 : LorentzianCoframe) :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one

private theorem input_nondegenerate : Input.Nondegenerate := by
  intro point
  rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  norm_num

@[simp] theorem fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one :
    Base.coframe = fun _ => (1 : LorentzianCoframe) := by
  rw [show Base.coframe = Input.coframe by rfl]
  exact fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one

private theorem input_coframeFirstJetAt (point : BasePoint) :
    holonomicCoframeFirstJetAt Input.coframe point =
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt]

private theorem input_spinResponse_contDiff :
    ContDiff ℝ ∞ (diracDualFormNativeActionSpinResponseAt Source Input) :=
  diracDualFormNativeActionSpinResponseAt_contDiff
    Source Input input_smooth input_nondegenerate

private theorem input_cartanTorsion_contDiff :
    ContDiff ℝ ∞
      (diracDualFormNativeActionCartanTorsionAt Source Input) := by
  have inverseSmooth :=
    (cartanTorsionThreeFormLinearEquiv
      (1 : LorentzianCoframe) (by norm_num)
      ).symm.toContinuousLinearEquiv.contDiff.comp input_spinResponse_contDiff
  change ContDiff ℝ ∞ fun point =>
    (cartanTorsionThreeFormLinearEquiv
      (1 : LorentzianCoframe) (by norm_num)).symm
      (diracDualFormNativeActionSpinResponseAt Source Input point) at inverseSmooth
  rw [show
    (diracDualFormNativeActionCartanTorsionAt Source Input) =
      fun point => cartanTorsionOfThreeForm (1 : LorentzianCoframe)
        (diracDualFormNativeActionSpinResponseAt Source Input point) by
    funext point
    unfold diracDualFormNativeActionCartanTorsionAt
    rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]]
  simpa only [cartanTorsionThreeFormLinearEquiv_symm_apply] using inverseSmooth

private theorem input_cartanContorsion_contDiff :
    ContDiff ℝ ∞
      (diracDualFormNativeActionCartanContorsionAt Source Input) := by
  have inverseSmooth :=
    (cartanContorsionTorsionLinearEquiv
      (1 : LorentzianCoframe) (by norm_num)
      ).symm.toContinuousLinearEquiv.contDiff.comp input_cartanTorsion_contDiff
  change ContDiff ℝ ∞ fun point =>
    (cartanContorsionTorsionLinearEquiv
      (1 : LorentzianCoframe) (by norm_num)).symm
      (diracDualFormNativeActionCartanTorsionAt Source Input point) at inverseSmooth
  rw [show
    (diracDualFormNativeActionCartanContorsionAt Source Input) =
      fun point => contorsionOfCartanTorsion (1 : LorentzianCoframe)
        (diracDualFormNativeActionCartanTorsionAt Source Input point) by
    funext point
    unfold diracDualFormNativeActionCartanContorsionAt
    rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]]
  simpa only [cartanContorsionTorsionLinearEquiv_symm_apply] using inverseSmooth

private theorem base_connection_eq (point : BasePoint) :
    Base.gravityConnection point =
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
          PointwiseLorentzianCoframeJet).lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt Source Input point) := by
  unfold Base fixedP506L0CartanECCauchyTemporalBase
    cartanECCauchyTemporalBase
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt cartanAffineSpinConnection
  change
    (holonomicCoframeFirstJetAt Input.coframe point).lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt Source Input point) = _
  rw [input_coframeFirstJetAt]

private theorem input_spinResponse_eq_coupled (point : BasePoint) :
    diracDualFormNativeActionSpinResponseAt Source Input point =
      diracDualFormNativeActionSpinResponseAt Source Coupled point := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
  · rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one,
      fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one]
  · rfl
  · rfl

private theorem input_cartanContorsion_eq_coupled (point : BasePoint) :
    diracDualFormNativeActionCartanContorsionAt Source Input point =
      diracDualFormNativeActionCartanContorsionAt Source Coupled point := by
  unfold diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [input_spinResponse_eq_coupled]
  rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one,
    fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one]

private theorem base_connection_eq_coupledAction (point : BasePoint) :
    Base.gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt Source Coupled point := by
  rw [base_connection_eq]
  unfold diracDualFormNativeActionCartanConnectionAt cartanAffineSpinConnection
  rw [input_cartanContorsion_eq_coupled]
  rw [fixedP506L0ActionSelectedCoupledTemporalActual_coframe_eq_one]
  change
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet).lorentzSpinConnection + _ =
      (holonomicCoframeFirstJetAt (fun _ => (1 : LorentzianCoframe)) point
        ).lorentzSpinConnection + _
  rw [show
    holonomicCoframeFirstJetAt (fun _ => (1 : LorentzianCoframe)) point =
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet) by
    apply coframeJet_eq_of_fields_eq
    · rfl
    · funext derivativeDirection internal coordinate
      simp [holonomicCoframeFirstJetAt]]

/-- Every temporal first derivative of the Cartan Cauchy base connection is
the same action-selected zero derivative, not a coordinate-specific trace. -/
theorem base_connection_temporalDerivative_origin_zero
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative fixedP506L0CartanECCauchyTemporalBase 0
        canonicalLorentzianTimeDirection formDirection internalOut
          internalIn = 0 := by
  unfold gravityConnectionDerivative
  rw [show
    (fun point => Base.gravityConnection point formDirection internalOut
      internalIn) =
      fun point =>
        diracDualFormNativeActionCartanConnectionAt Source Coupled point
          formDirection internalOut internalIn by
    funext point
    rw [base_connection_eq_coupledAction]]
  exact
    fixedP506L0ActionSelectedCoupled_cartanConnection_component_temporalDerivative_zero
      formDirection internalOut internalIn

private theorem base_connection_contDiff :
    ContDiff ℝ ∞ Base.gravityConnection := by
  have liftedSmooth :=
    fixedLorentzBivectorOneFormConnectionLinearMap.toContinuousLinearMap
      |>.contDiff.comp input_cartanContorsion_contDiff
  change ContDiff ℝ ∞ fun point =>
    lorentzSkewConnectionOfBivectorOneForm
      (diracDualFormNativeActionCartanContorsionAt Source Input point) at liftedSmooth
  rw [show Base.gravityConnection = fun point =>
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
          PointwiseLorentzianCoframeJet).lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt Source Input point) by
    funext point
    exact base_connection_eq point]
  exact contDiff_const.add liftedSmooth

private theorem base_connection_component_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      Base.gravityConnection point formDirection internalOut internalIn :=
  contDiff_pi.mp
    (contDiff_pi.mp
      (contDiff_pi.mp base_connection_contDiff formDirection)
      internalOut)
    internalIn

private theorem base_auxiliary_contDiff :
    ContDiff ℝ ∞ Base.gravityAuxiliary := by
  change ContDiff ℝ ∞ fun point => physicalIIPlusBivector (Input.coframe point)
  exact physicalIIPlusBivector_contDiff.comp
    (holonomicCoframe_contDiff Input input_smooth)

private abbrev Prepared : StageNineHolonomicConfiguration :=
  diracDualFormNativeCartanSimplicityPreparedCurrent Source Input

private theorem connectionWritten_smooth :
    (diracDualFormNativeCartanConnectionWrittenCurrent Source Input).Smooth := by
  rcases input_smooth with
    ⟨coframeSmooth, _connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      (by
        intro formDirection internalOut internalIn
        change ContDiff ℝ ∞ fun point =>
          Base.gravityConnection point formDirection internalOut internalIn
        exact base_connection_component_contDiff _ _ _),
      auxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

private theorem prepared_smooth : Prepared.Smooth := by
  exact restrictHolonomicConfigurationToIIPlus_smooth _ connectionWritten_smooth

private theorem base_multiplier_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      Base.gravitySimplicityMultiplier point internalPair spacetimePair := by
  unfold Base fixedP506L0CartanECCauchyTemporalBase
    cartanECCauchyTemporalBase
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    diracDualFormNativeCartanReactionCurrentField
  change ContDiff ℝ ∞ fun point =>
    formNativeGravityReactionField Prepared point internalPair spacetimePair
  unfold formNativeGravityReactionField
  have dualSmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (Prepared.gravityAuxiliary point) := by
    change ContDiff ℝ ∞ fun point =>
      gravityInternalDualLinear (Prepared.gravityAuxiliary point)
    exact gravityInternalDualLinear.toContinuousLinearMap.contDiff.comp
      (holonomicGravityAuxiliary_contDiff Prepared prepared_smooth)
  have curvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature Prepared point
        internalPair spacetimePair :=
    contDiff_const.mul
      (holonomicGravityCurvature_component_contDiff Prepared prepared_smooth
        internalPair spacetimePair)
  exact
    (contDiff_pi.mp (contDiff_pi.mp dualSmooth internalPair)
      spacetimePair).sub curvatureSmooth

/-- The exact fixed Cartan restart consumed by the Cauchy compiler is smooth;
no arbitrary-current regularity receipt is supplied to the producer. -/
theorem fixedP506L0CartanECCauchyTemporalBase_smooth : Base.Smooth := by
  rcases input_smooth with
    ⟨coframeSmooth, _connectionSmooth, _auxiliarySmooth, _multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, base_connection_component_contDiff,
      (by
        intro internalPair spacetimePair
        exact contDiff_pi.mp
          (contDiff_pi.mp base_auxiliary_contDiff internalPair) spacetimePair),
      base_multiplier_component_contDiff, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

/-! ## Exact occurrence-profile regularity -/

private abbrev ECPrepared : StageNineHolonomicConfiguration :=
  diracDualFormNativeECNormalPreparedActual Base

private theorem ecPrepared_smooth : ECPrepared.Smooth :=
  restrictHolonomicConfigurationToIIPlus_smooth Base
    fixedP506L0CartanECCauchyTemporalBase_smooth

private def FixedField (contact : BasePoint) : StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus (toContinuumPointField Base contact)

private theorem fixedField_coframe_contDiff :
    ContDiff ℝ ∞ fun contact => (FixedField contact).coframe := by
  change ContDiff ℝ ∞ Base.coframe
  exact holonomicCoframe_contDiff Base
    fixedP506L0CartanECCauchyTemporalBase_smooth

private theorem fixedGaugeParameter_contDiff :
    ContDiff ℝ ∞ fun contact =>
      coframeGaugeActionParameterOfField (FixedField contact) := by
  apply ContDiff.prodMk
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (ECPrepared.gaugeAuxiliary contact pair)
    exact ecPrepared_smooth.2.2.2.2.2.1 pair
  · apply contDiff_pi'
    intro pair
    change ContDiff ℝ ∞ fun contact =>
      p286CoordinateEquiv (holonomicGaugeCurvature ECPrepared contact pair)
    exact holonomicGaugeCurvature_coordinate_contDiff
      ECPrepared ecPrepared_smooth pair

private theorem fixedMatterParameter_contDiff :
    ContDiff ℝ ∞ fun contact =>
      coframeMatterActionParameterOfField (FixedField contact) := by
  have scalarRegular : ContDiff ℝ ∞ ECPrepared.scalar :=
    ecPrepared_smooth.2.2.2.2.2.2.1
  have scalarDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      holonomicScalarCovariantDerivative ECPrepared contact := by
    apply contDiff_pi'
    intro direction
    exact holonomicScalarCovariantDerivative_contDiff_local
      ECPrepared ecPrepared_smooth direction
  have matterRegular : ContDiff ℝ ∞ fun contact =>
      matterCoordinateEquiv (ECPrepared.matter contact) :=
    ecPrepared_smooth.2.2.2.2.2.2.2.1
  have matterDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative ECPrepared contact direction) := by
    apply contDiff_pi'
    intro direction
    exact holonomicMatterCovariantDerivative_coordinate_contDiff_local
      ECPrepared ecPrepared_smooth direction
  have conjugateRegular : ContDiff ℝ ∞ fun contact =>
      matterDualCoordinates (ECPrepared.conjugateMatter contact) :=
    holonomicConjugateMatterCoordinates_contDiff ECPrepared ecPrepared_smooth
  change ContDiff ℝ ∞ fun contact =>
    (ECPrepared.scalar contact,
      holonomicScalarCovariantDerivative ECPrepared contact,
      matterCoordinateEquiv (ECPrepared.matter contact),
      (fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative ECPrepared contact direction)),
      matterDualCoordinates (ECPrepared.conjugateMatter contact))
  exact scalarRegular.prodMk
    (scalarDerivativeRegular.prodMk
      (matterRegular.prodMk
        (matterDerivativeRegular.prodMk conjugateRegular)))

private theorem profileField_eq_fixedField (contact : BasePoint) :
    diracDualFormNativeECNormalContactField
        (cartanECCauchyTemporalProfileInput Source Input contact) =
      FixedField contact := by
  unfold diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual FixedField
    cartanECCauchyTemporalProfileInput
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  rw [fullyRecenterHolonomicConfiguration_pointField_origin_unconditional]
  rfl

private theorem outputGaugeParameter_eq_fixedField
    (space : StageNineSpatialPoint) :
    coframeGaugeActionParameterOfField (OutputField space) =
      coframeGaugeActionParameterOfField
        (FixedField (canonicalCauchySlicePoint 0 space)) := by
  rfl

private theorem outputMatterParameter_eq_fixedField
    (space : StageNineSpatialPoint) :
    coframeMatterActionParameterOfField (OutputField space) =
      coframeMatterActionParameterOfField
        (FixedField (canonicalCauchySlicePoint 0 space)) := by
  unfold coframeMatterActionParameterOfField OutputField FixedField
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext direction
      rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext direction
          change
            matterCoordinateEquiv
                (holonomicMatterCovariantDerivative Output
                  (canonicalCauchySlicePoint 0 space) direction) =
              matterCoordinateEquiv
                (holonomicMatterCovariantDerivative Base
                  (canonicalCauchySlicePoint 0 space) direction)
          congr 1
          have connectionEq :
              Output.gravityConnection
                  (canonicalCauchySlicePoint 0 space) =
                Base.gravityConnection
                  (canonicalCauchySlicePoint 0 space) :=
            sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
              Source Input space
          have matterEq : Output.matter = Base.matter := rfl
          have gaugeEq : Output.gaugeConnection = Base.gaugeConnection := rfl
          unfold holonomicMatterCovariantDerivative
          rw [connectionEq, matterEq, gaugeEq]
        · rfl

private theorem outputGaugeEuler_eq_fixedField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeGaugeEulerCovector Source
        (OutputField space) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (FixedField (canonicalCauchySlicePoint 0 space)) := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [diracDualFormNativeCoframeGaugeEulerCovector_eq_coordinateFDeriv,
    diracDualFormNativeCoframeGaugeEulerCovector_eq_coordinateFDeriv,
    outputGaugeParameter_eq_fixedField]
  rfl

private theorem outputMatterEuler_eq_fixedField
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeMatterEulerCovector Source
        (canonicalCauchySlicePoint 0 space) (OutputField space) =
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (FixedField (canonicalCauchySlicePoint 0 space)) := by
  rw [
    diracDualFormNativeCoframeMatterEulerCovector_point_independent
      Source (canonicalCauchySlicePoint 0 space) (OutputField space)]
  apply ContinuousLinearMap.ext
  intro variation
  rw [diracDualFormNativeCoframeMatterEulerCovector_eq_coordinateFDeriv,
    diracDualFormNativeCoframeMatterEulerCovector_eq_coordinateFDeriv,
    outputMatterParameter_eq_fixedField]
  rfl

private theorem profileGaugeEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Input contact))
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Input contact))
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (FixedField contact) (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq_fixedField]]
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact
    diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_one
      Source FixedField contact
      (fixedGaugeParameter_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (fixedField_coframe_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (by
        change Matrix.det (Base.coframe contact) ≠ 0
        rw [fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]
        norm_num)
      row column

private theorem profileMatterEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Input contact))
        (coframeCoordinateDirection row column) := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Input contact))
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (FixedField contact) (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq_fixedField]]
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact
    diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_one
      Source 0 FixedField contact
      (fixedMatterParameter_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (fixedField_coframe_contDiff.contDiffAt.of_le
        (show (1 : WithTop ℕ∞) ≤ ∞ by simp))
      (by
        change Matrix.det (Base.coframe contact) ≠ 0
        rw [fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]
        norm_num)
      row column

private theorem profileLoad_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeIdentityECLoad Source
        (cartanECCauchyTemporalProfileInput Source Input contact)
        (coframeCoordinateDirection row column) := by
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  exact
    (contDiff_const.add
      (profileGaugeEuler_coordinate_contDiff row column)).add
      (profileMatterEuler_coordinate_contDiff row column)

private theorem profileCurrentCurvature_eq_base (contact : BasePoint) :
    diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Input contact) =
      holonomicGravityCurvature ECPrepared contact := by
  unfold diracDualFormNativeECCauchyCurrentCurvature
    diracDualFormNativeECNormalPreparedActual
    cartanECCauchyTemporalProfileInput ECPrepared
  change
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration Base contact) 0 =
      holonomicGravityCurvature
        (restrictHolonomicConfigurationToIIPlus Base) contact
  change
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration Base contact) 0 =
      holonomicGravityCurvature Base contact
  exact fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
    Base contact

private theorem profileCurrentCurvature_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
          (cartanECCauchyTemporalProfileInput Source Input contact)
          internalPair spacetimePair := by
  rw [show
    (fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
          (cartanECCauchyTemporalProfileInput Source Input contact)
          internalPair spacetimePair) =
      fun contact =>
        holonomicGravityCurvature ECPrepared contact
          internalPair spacetimePair by
    funext contact
    rw [profileCurrentCurvature_eq_base]]
  exact
    (holonomicGravityCurvature_component_contDiff ECPrepared ecPrepared_smooth
      internalPair spacetimePair).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by simp)

private theorem profileDesiredEvolution_coordinate_contDiff
    (row : Fin 4) (direction : Fin 3) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeECDesiredEvolutionObservation Source
          (cartanECCauchyTemporalProfileInput Source Input contact)
          row direction := by
  unfold diracDualFormNativeECDesiredEvolutionObservation
    identityECSpatialCoframeCoordinatesOfCovector
  exact (profileLoad_coordinate_contDiff row direction.succ).neg

private def temporalCoordinatesLinearMap :
    PhysicalBivector →ₗ[ℝ] IdentityECTemporalCurvatureCoordinates where
  toFun := identityECTemporalCurvatureCoordinatesOf
  map_add' := identityECTemporalCurvatureCoordinatesOf_add
  map_smul' := by intro parameter curvature; rfl

private def temporalCurvatureLinearMap :
    IdentityECTemporalCurvatureCoordinates →ₗ[ℝ] PhysicalBivector where
  toFun := identityECTemporalCurvatureOfCoordinates
  map_add' := identityECTemporalCurvatureOfCoordinates_add
  map_smul' := by
    intro parameter coordinates
    funext internalPair spacetimePair
    fin_cases spacetimePair <;>
      simp [identityECTemporalCurvatureOfCoordinates]

private def temporalObservationLinearMap :
    PhysicalBivector →ₗ[ℝ] IdentityECSpatialCoframeCovectorCoordinates where
  toFun := identityDiracDualECTemporalEvolutionObservation
  map_add' := identityDiracDualECTemporalEvolutionObservation_add
  map_smul' := by
    intro parameter curvature
    funext row direction
    unfold identityDiracDualECTemporalEvolutionObservation
      identityDiracDualECCurvatureObservation
    change
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
            (coframeCoordinateDirection row direction.succ))
          (gravityInternalPairVarianceNormalization (parameter • curvature)) =
        parameter *
          gravityTopologicalWedgeCoefficient
            (physicalIIPlusCoframeTangent (1 : LorentzianCoframe)
              (coframeCoordinateDirection row direction.succ))
            (gravityInternalPairVarianceNormalization curvature)
    rw [map_smul, gravityTopologicalWedgeCoefficient_smul_right]

private def temporalSectionCoordinatesLinearMap :
    IdentityECSpatialCoframeCovectorCoordinates →ₗ[ℝ]
      IdentityECTemporalCurvatureCoordinates where
  toFun := identityDiracDualECTemporalEvolutionSectionCoordinates
  map_add' := identityDiracDualECTemporalEvolutionSectionCoordinates_add
  map_smul' := by
    intro parameter response
    funext internalPair direction
    fin_cases internalPair <;> fin_cases direction <;>
      simp [identityDiracDualECTemporalEvolutionSectionCoordinates] <;> ring

private def spatialCurvatureLinearMap :
    PhysicalBivector →ₗ[ℝ] PhysicalBivector :=
  LinearMap.id - temporalCurvatureLinearMap.comp temporalCoordinatesLinearMap

private def spatialObservationLinearMap :
    PhysicalBivector →ₗ[ℝ] IdentityECSpatialCoframeCovectorCoordinates :=
  temporalObservationLinearMap.comp spatialCurvatureLinearMap

private def temporalKernelLinearMap :
    IdentityECTemporalCurvatureCoordinates →ₗ[ℝ]
      IdentityECTemporalCurvatureCoordinates :=
  LinearMap.id -
    temporalSectionCoordinatesLinearMap.comp
      (temporalObservationLinearMap.comp temporalCurvatureLinearMap)

private theorem spatialObservationLinearMap_apply
    (curvature : PhysicalBivector) :
    spatialObservationLinearMap curvature =
      identityDiracDualECTemporalEvolutionObservation
        (identityECSpatialCurvaturePart curvature) := by
  rfl

private theorem temporalKernelLinearMap_apply
    (coordinates : IdentityECTemporalCurvatureCoordinates) :
    temporalKernelLinearMap coordinates =
      identityDiracDualECTemporalEvolutionKernelPart coordinates := by
  rfl

private theorem profileCurrentCurvature_contDiff :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Input contact) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  exact profileCurrentCurvature_component_contDiff internalPair spacetimePair

private theorem profileDesiredEvolution_contDiff :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeECDesiredEvolutionObservation Source
        (cartanECCauchyTemporalProfileInput Source Input contact) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro direction
  exact profileDesiredEvolution_coordinate_contDiff row direction

private theorem temporalIncrement_normalForm
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECTemporalCurvatureIncrement source current =
      identityDiracDualECTemporalEvolutionTargetCoordinates
          (identityECTemporalCurvatureCoordinatesOf
            (diracDualFormNativeECCauchyCurrentCurvature current))
          (diracDualFormNativeECDesiredEvolutionObservation source current -
            identityDiracDualECTemporalEvolutionObservation
              (identityECSpatialCurvaturePart
                (diracDualFormNativeECCauchyCurrentCurvature current))) -
        identityECTemporalCurvatureCoordinatesOf
          (diracDualFormNativeECCauchyCurrentCurvature current) := by
  funext internalPair direction
  unfold diracDualFormNativeECTemporalCurvatureIncrement
    diracDualFormNativeECCauchyCurvatureTarget
    identityECTemporalCurvatureCoordinatesOf
  simp only [Pi.sub_apply]
  rw [identityDiracDualECTotalEvolutionCurvatureTarget_temporal]
  rfl

private theorem profileIncrement_coordinate_contDiff
    (internalPair : Fin 6) (direction : Fin 3) :
    ContDiff ℝ 1 fun contact =>
      diracDualFormNativeECTemporalCurvatureIncrement Source
          (cartanECCauchyTemporalProfileInput Source Input contact)
          internalPair direction := by
  let currentCurve := fun contact =>
    diracDualFormNativeECCauchyCurrentCurvature
      (cartanECCauchyTemporalProfileInput Source Input contact)
  let desiredCurve := fun contact =>
    diracDualFormNativeECDesiredEvolutionObservation Source
      (cartanECCauchyTemporalProfileInput Source Input contact)
  have currentCoordinatesRegular : ContDiff ℝ 1 fun contact =>
      temporalCoordinatesLinearMap (currentCurve contact) :=
    temporalCoordinatesLinearMap.toContinuousLinearMap.contDiff.comp
      profileCurrentCurvature_contDiff
  have spatialObservationRegular : ContDiff ℝ 1 fun contact =>
      spatialObservationLinearMap (currentCurve contact) :=
    spatialObservationLinearMap.toContinuousLinearMap.contDiff.comp
      profileCurrentCurvature_contDiff
  have responseRegular : ContDiff ℝ 1 fun contact =>
      desiredCurve contact - spatialObservationLinearMap (currentCurve contact) :=
    profileDesiredEvolution_contDiff.sub spatialObservationRegular
  have targetRegular : ContDiff ℝ 1 fun contact =>
      identityDiracDualECTemporalEvolutionTargetCoordinates
        (identityECTemporalCurvatureCoordinatesOf (currentCurve contact))
        (desiredCurve contact -
          identityDiracDualECTemporalEvolutionObservation
            (identityECSpatialCurvaturePart (currentCurve contact))) := by
    rw [show
      (fun contact =>
        identityDiracDualECTemporalEvolutionTargetCoordinates
          (identityECTemporalCurvatureCoordinatesOf (currentCurve contact))
          (desiredCurve contact -
            identityDiracDualECTemporalEvolutionObservation
              (identityECSpatialCurvaturePart (currentCurve contact)))) =
      fun contact =>
        temporalKernelLinearMap
            (temporalCoordinatesLinearMap (currentCurve contact)) +
          temporalSectionCoordinatesLinearMap
            (desiredCurve contact -
              spatialObservationLinearMap (currentCurve contact)) by
      funext contact
      unfold identityDiracDualECTemporalEvolutionTargetCoordinates
      rw [temporalKernelLinearMap_apply,
        spatialObservationLinearMap_apply]
      rfl]
    exact
      (temporalKernelLinearMap.toContinuousLinearMap.contDiff.comp
        currentCoordinatesRegular).add
      (temporalSectionCoordinatesLinearMap.toContinuousLinearMap.contDiff.comp
        responseRegular)
  rw [show
    (fun contact =>
      diracDualFormNativeECTemporalCurvatureIncrement Source
          (cartanECCauchyTemporalProfileInput Source Input contact)
          internalPair direction) =
      fun contact =>
        (identityDiracDualECTemporalEvolutionTargetCoordinates
            (identityECTemporalCurvatureCoordinatesOf (currentCurve contact))
            (desiredCurve contact -
              identityDiracDualECTemporalEvolutionObservation
                (identityECSpatialCurvaturePart (currentCurve contact))) -
          identityECTemporalCurvatureCoordinatesOf (currentCurve contact))
          internalPair direction by
    funext contact
    exact congrFun (congrFun
      (temporalIncrement_normalForm Source
        (cartanECCauchyTemporalProfileInput Source Input contact))
      internalPair) direction]
  exact
    (contDiff_pi.mp (contDiff_pi.mp targetRegular internalPair) direction).sub
      (contDiff_pi.mp
        (contDiff_pi.mp currentCoordinatesRegular internalPair) direction)

private theorem profileCoordinate_contDiff
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiff ℝ 1 fun contact =>
      cartanECCauchyTemporalConnectionCorrectionProfile Source Input contact
        formDirection internalPair := by
  fin_cases formDirection
  · exact contDiff_const
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      profileIncrement_coordinate_contDiff internalPair 0
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      profileIncrement_coordinate_contDiff internalPair 1
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      profileIncrement_coordinate_contDiff internalPair 2

private theorem contactTranslation_contDiff (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

private theorem correctionPrimitive_coordinate_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    ContDiffAt ℝ 1
      (fun point =>
        cartanECCauchyTemporalConnectionCorrectionPrimitive Source Input point
          formDirection internalPair)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  let translation := canonicalSpacetimeContactTranslation point
  let profile : BasePoint → ℝ := fun contact =>
    cartanECCauchyTemporalConnectionCorrectionProfile Source Input contact
      formDirection internalPair
  have profileRecentered : ContDiffAt ℝ 1 (profile ∘ translation) 0 := by
    have outer : ContDiffAt ℝ 1 profile (translation 0) := by
      simpa [profile, translation, point] using
        (profileCoordinate_contDiff formDirection internalPair).contDiffAt
    exact outer.comp 0
      ((contactTranslation_contDiff point).contDiffAt.of_le (by norm_num))
  have primitiveRecentered : ContDiffAt ℝ 1
      (canonicalTimePrimitive profile ∘ translation) 0 := by
    rw [show canonicalTimePrimitive profile ∘ translation =
        canonicalTimePrimitive (profile ∘ translation) by
      simpa [translation, point] using
        canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
          profile space]
    exact canonicalTimePrimitive_contDiffAt_of_contDiffAt
      (profile ∘ translation) profileRecentered
  have inverseRegular : ContDiffAt ℝ 1
      (canonicalSpacetimeContactTranslation (-point)) point :=
    (contactTranslation_contDiff (-point)).contDiffAt.of_le (by norm_num)
  have primitiveRecenteredAtInverse : ContDiffAt ℝ 1
      (canonicalTimePrimitive profile ∘ translation)
      (canonicalSpacetimeContactTranslation (-point) point) := by
    simpa [canonicalSpacetimeContactTranslation] using primitiveRecentered
  have primitiveAtPoint :=
    primitiveRecenteredAtInverse.comp point inverseRegular
  simpa [cartanECCauchyTemporalConnectionCorrectionPrimitive,
    profile, translation, point, Function.comp_def,
    canonicalSpacetimeContactTranslation, add_assoc] using primitiveAtPoint

private theorem correctionPrimitive_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (cartanECCauchyTemporalConnectionCorrectionPrimitive Source Input)
      (canonicalCauchySlicePoint 0 space) := by
  apply contDiffAt_pi'
  intro formDirection
  apply contDiffAt_pi'
  intro internalPair
  exact correctionPrimitive_coordinate_contDiffAt_zeroSlice
    space formDirection internalPair

private theorem output_connection_component_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        Output.gravityConnection point formDirection internalOut internalIn)
      (canonicalCauchySlicePoint 0 space) := by
  have liftedRegular :=
    fixedLorentzBivectorOneFormConnectionLinearMap.toContinuousLinearMap
      |>.contDiff.contDiffAt.comp
        (canonicalCauchySlicePoint 0 space)
        (correctionPrimitive_contDiffAt_zeroSlice space)
  change ContDiffAt ℝ 1 (fun point =>
    lorentzSkewConnectionOfBivectorOneForm
      (cartanECCauchyTemporalConnectionCorrectionPrimitive Source Input point)
    ) (canonicalCauchySlicePoint 0 space) at liftedRegular
  have outputRegular : ContDiffAt ℝ 1 Output.gravityConnection
      (canonicalCauchySlicePoint 0 space) := by
    change ContDiffAt ℝ 1 (fun point =>
      Base.gravityConnection point +
        lorentzSkewConnectionOfBivectorOneForm
          (cartanECCauchyTemporalConnectionCorrectionPrimitive
            Source Input point)) (canonicalCauchySlicePoint 0 space)
    exact (base_connection_contDiff.contDiffAt.of_le (by norm_num)).add
      liftedRegular
  exact
    (contDiffAt_pi.mp
      (contDiffAt_pi.mp
        (contDiffAt_pi.mp outputRegular formDirection)
        internalOut)
      internalIn).differentiableAt (by norm_num)

private theorem canonicalTimeLine_continuous
    (space : StageNineSpatialPoint) :
    Continuous (fun time => canonicalCauchySlicePoint time space) := by
  rw [show
    (fun time => canonicalCauchySlicePoint time space) =
      fun time =>
        canonicalCauchySlicePoint 0 space +
          time • coordinateDirection canonicalLorentzianTimeDirection by
    funext time
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
  fun_prop

private theorem profile_timeLine_continuous
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    Continuous fun time =>
      cartanECCauchyTemporalConnectionCorrectionProfile Source Input
        (canonicalCauchySlicePoint time space) formDirection internalPair :=
  (profileCoordinate_contDiff formDirection internalPair).continuous.comp
    (canonicalTimeLine_continuous space)

/-- On the complete zero-time slice the fixed source-native successor has
exactly the occurrence-local EC Cauchy target curvature at every point. -/
theorem fixedP506L0CartanECCauchyTemporalGlobalActual_curvature_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature Output (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeECCauchyCurvatureTarget Source
        (cartanECCauchyTemporalProfileInput Source Input
          (canonicalCauchySlicePoint 0 space)) := by
  apply
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_curvature_zeroSlice
  · intro formDirection internalOut internalIn
    exact (base_connection_component_contDiff
      formDirection internalOut internalIn).differentiable
        (by simp) |>.differentiableAt
  · intro formDirection internalOut internalIn
    exact output_connection_component_differentiableAt_zeroSlice
      space formDirection internalOut internalIn
  · intro formDirection internalPair
    exact (profile_timeLine_continuous space formDirection internalPair
      ).continuousAt
  · intro formDirection internalPair
    exact (profile_timeLine_continuous space formDirection internalPair
      ).stronglyMeasurableAtFilter MeasureTheory.volume (nhds 0)

/-- The same emitted P506/L0 actual closes all twelve independent EC
evolution rows on its complete zero-time Cauchy slice. -/
theorem fixedP506L0CartanECCauchyTemporalGlobalActual_evolutionBalance_zeroSlice
    (space : StageNineSpatialPoint) :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature Output
            (canonicalCauchySlicePoint 0 space)) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad Source
            (cartanECCauchyTemporalProfileInput Source Input
              (canonicalCauchySlicePoint 0 space))) =
      0 := by
  apply
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_evolutionBalance_zeroSlice
  · intro formDirection internalOut internalIn
    exact (base_connection_component_contDiff
      formDirection internalOut internalIn).differentiable
        (by simp) |>.differentiableAt
  · intro formDirection internalOut internalIn
    exact output_connection_component_differentiableAt_zeroSlice
      space formDirection internalOut internalIn
  · intro formDirection internalPair
    exact (profile_timeLine_continuous space formDirection internalPair
      ).continuousAt
  · intro formDirection internalPair
    exact (profile_timeLine_continuous space formDirection internalPair
      ).stronglyMeasurableAtFilter MeasureTheory.volume (nhds 0)

/-- Direct whole-residual readback: the emitted Cauchy actual closes every
spatial-column coframe Euler coordinate on the complete zero-time slice.
This includes the `E03` direction that rejected the previous `U_joint`. -/
theorem
    fixedP506L0CartanECCauchyTemporalGlobalActual_coframeResidual_spatial_zeroSlice
    (space : StageNineSpatialPoint)
    (row : LorentzianIndex)
    (direction : Fin 3) :
    (diracDualFormNativePointwiseJointResidual Source Output
      (canonicalCauchySlicePoint 0 space)).coframe
        (coframeCoordinateDirection row direction.succ) =
      0 := by
  let point := canonicalCauchySlicePoint 0 space
  let variation := coframeCoordinateDirection row direction.succ
  have outputSimplicity : FormNativeGravitySimplicityEquation Output :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
      Source Input
  have outputAuxiliary : FormNativeGravityAuxiliaryEquation Output :=
    installFormNativeGravityReaction_auxiliaryEquation
      (cartanECCauchyTemporalConnectedActual Source Input)
  have reduction :=
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      Source Output outputSimplicity outputAuxiliary
      (fun _ => variation) point
  change
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity Source point
        (toContinuumPointField Output point) variation =
      diracDualFormNativeCoframeEulerCovector Source point
        (toContinuumPointField Output point) variation at reduction
  change
    diracDualFormNativeCoframeEulerCovector Source point
        (toContinuumPointField Output point) variation =
      0
  rw [← reduction]
  rw [
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
      Source point (toContinuumPointField Output point)
      (by
        change Matrix.det (Input.coframe point) ≠ 0
        rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
        norm_num)
      variation]
  have outputCoframeOne :
      (toContinuumPointField Output point).coframe =
        (1 : LorentzianCoframe) := by
    change Input.coframe point = 1
    rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  rw [outputCoframeOne]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField Output point).gravityCurvature) =
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output point) variation by
      rfl]
  rw [← identityDiracDualECCurvatureObservation_intrinsic_apply variation]
  change
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output point) variation +
        identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) variation +
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (OutputField space) variation +
        diracDualFormNativeCoframeMatterEulerCovector Source point
          (OutputField space) variation =
      0
  rw [outputGaugeEuler_eq_fixedField, outputMatterEuler_eq_fixedField]
  have balance := congrFun (congrFun
    (fixedP506L0CartanECCauchyTemporalGlobalActual_evolutionBalance_zeroSlice
      space) row) direction
  change
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output point) variation +
        (diracDualFormNativeIdentityECLoad Source
          (cartanECCauchyTemporalProfileInput Source Input point)) variation =
      0 at balance
  unfold diracDualFormNativeIdentityECLoad at balance
  rw [profileField_eq_fixedField] at balance
  simpa only [add_apply, add_assoc] using balance

/-! ## Preserved temporal constraint read -/

private abbrev OldCarry : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private theorem positiveActual_coframe_one (point : BasePoint) :
    positiveSourceTargetMatterActual.coframe point = 1 := by
  rw [positiveSourceTargetMatterActual,
    sourceActionGeneratedJointLocalActualLift_coframe_at]
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

private theorem input_spinResponse_zeroSlice_eq_positive
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionSpinResponseAt Source Input
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionSpinResponseAt Source
        positiveSourceTargetMatterActual 0 := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · calc
      Input.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
        rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
      _ = positiveSourceTargetMatterActual.coframe 0 :=
        (positiveActual_coframe_one 0).symm
  · calc
      Input.matter (canonicalCauchySlicePoint 0 space) =
          diracSpinTwoMatterProbe :=
        fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant space
      _ = positiveSourceTargetMatterCauchyState.matter 0 :=
        positiveSourceTargetMatterCauchyState_matter.symm
      _ = positiveSourceTargetMatterActual.matter 0 :=
        (sourceActionGeneratedJointLocalActualLift_initialMatter
          Source positiveSourceTargetMatterCauchyState 0).symm
  · calc
      Input.conjugateMatter (canonicalCauchySlicePoint 0 space) =
          diracSpinZeroMatterCoordinate :=
        fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
          space
      _ = positiveSourceTargetMatterCauchyState.conjugateMatter 0 :=
        positiveSourceTargetMatterCauchyState_conjugate.symm
      _ = positiveSourceTargetMatterActual.conjugateMatter 0 :=
        (sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
          Source positiveSourceTargetMatterCauchyState 0).symm

private theorem input_cartanContorsion_zeroSlice_eq_positiveNormalForm
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanContorsionAt Source Input
        (canonicalCauchySlicePoint 0 space) =
      positiveDiracDualCartanContorsionNormalForm := by
  calc
    _ = diracDualFormNativeActionCartanContorsionAt Source
          positiveSourceTargetMatterActual 0 := by
      unfold diracDualFormNativeActionCartanContorsionAt
        diracDualFormNativeActionCartanTorsionAt
      rw [show Input.coframe (canonicalCauchySlicePoint 0 space) =
          positiveSourceTargetMatterActual.coframe 0 by
        calc
          _ = 1 := by
            rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
          _ = _ := (positiveActual_coframe_one 0).symm,
        input_spinResponse_zeroSlice_eq_positive]
    _ = _ := fixedActionCartanContorsion_eq_positiveNormalForm

private def identityZeroCoframeJet : PointwiseLorentzianCoframeJet where
  coframe := 1
  derivative := 0

private theorem identityZeroCoframeJet_loweredLeviCivitaVector_eq_zero
    (first second : LorentzianIndex) :
    identityZeroCoframeJet.loweredLeviCivitaVector first second = 0 := by
  funext internal
  simp [PointwiseLorentzianCoframeJet.loweredLeviCivitaVector,
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection,
    PointwiseLorentzianCoframeJet.metricDerivative,
    identityZeroCoframeJet]

private theorem identityZeroCoframeJet_leviCivitaConnection_eq_zero :
    identityZeroCoframeJet.leviCivitaConnection = 0 := by
  funext upper first second
  unfold PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  rw [identityZeroCoframeJet_loweredLeviCivitaVector_eq_zero]
  simp

private theorem identityZeroCoframeJet_coordinateConnectionMatrix_eq_zero
    (direction : LorentzianIndex) :
    identityZeroCoframeJet.coordinateConnectionMatrix direction = 0 := by
  unfold PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
  rw [identityZeroCoframeJet_leviCivitaConnection_eq_zero]
  rfl

private theorem identityZeroCoframeJet_lorentzSpinConnection_eq_zero :
    identityZeroCoframeJet.lorentzSpinConnection = 0 := by
  funext formDirection internalOut internalIn
  change identityZeroCoframeJet.lorentzSpinConnectionMatrix
      formDirection internalOut internalIn = 0
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
  rw [identityZeroCoframeJet_coordinateConnectionMatrix_eq_zero]
  simp [PointwiseLorentzianCoframeJet.coframeDerivativeMatrix,
    identityZeroCoframeJet]

theorem base_connection_zeroSlice_eq_fixedAction
    (space : StageNineSpatialPoint) :
    fixedP506L0CartanECCauchyTemporalBase.gravityConnection
        (canonicalCauchySlicePoint 0 space) = fixedActionCartanConnection := by
  let point := canonicalCauchySlicePoint 0 space
  rw [base_connection_eq point,
    input_cartanContorsion_zeroSlice_eq_positiveNormalForm,
    fixedActionCartanConnection_eq_positiveNormalForm]
  change
    identityZeroCoframeJet.lorentzSpinConnection +
        lorentzSkewConnectionOfBivectorOneForm
          positiveDiracDualCartanContorsionNormalForm =
      lorentzSkewConnectionOfBivectorOneForm
        positiveDiracDualCartanContorsionNormalForm
  rw [identityZeroCoframeJet_lorentzSpinConnection_eq_zero]
  simp

theorem base_connection_spatialDerivative_origin_zero
    (axis : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative fixedP506L0CartanECCauchyTemporalBase 0 axis.succ
        formDirection internalOut internalIn = 0 := by
  let field : BasePoint → ℝ := fun point =>
    Base.gravityConnection point formDirection internalOut internalIn
  have pointZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have fieldDifferentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    exact
      ((fixedP506L0CartanECCauchyTemporalBase_smooth.2.1
          formDirection internalOut internalIn).differentiable
        (by simp)).differentiableAt
  have sliceDerivative := fieldDifferentiable.hasFDerivAt.comp
    (0 : StageNineSpatialPoint)
    (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  have sliceConstant :
      field ∘ canonicalCauchySlicePoint 0 =
        fun _ : StageNineSpatialPoint =>
          fixedActionCartanConnection formDirection internalOut internalIn := by
    funext space
    exact congrFun (congrFun (congrFun
      (base_connection_zeroSlice_eq_fixedAction space)
      formDirection) internalOut) internalIn
  have sliceFderivZero :
      fderiv ℝ (field ∘ canonicalCauchySlicePoint 0)
          (0 : StageNineSpatialPoint) = 0 := by
    rw [sliceConstant]
    simp
  rw [sliceDerivative.fderiv] at sliceFderivZero
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] ℝ =>
      derivative (canonicalSpatialCoordinateDirection axis))
    sliceFderivZero
  unfold gravityConnectionDerivative
  rw [← pointZero]
  change
    (fderiv ℝ field
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)))
        (coordinateDirection axis.succ) = 0
  simpa [field, ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

private theorem base_connection_origin_eq_input :
    Base.gravityConnection 0 = Input.gravityConnection 0 := by
  calc
    Base.gravityConnection 0 = fixedActionCartanConnection := by
      have pointZero :
          canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
        ext direction
        fin_cases direction <;>
          simp [canonicalCauchySlicePoint,
            canonicalLorentzianTimeDirection, Fin.sum_univ_three]
      rw [← pointZero]
      exact base_connection_zeroSlice_eq_fixedAction 0
    _ = Input.gravityConnection 0 :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_fixedAction.symm

private theorem baseGaugeParameter_eq_input :
    coframeGaugeActionParameterOfField
        (diracDualFormNativeECNormalContactField Base) =
      coframeGaugeActionParameterOfField
        (diracDualFormNativeCoframeECContactField Input 0) := by
  rfl

private theorem baseMatterParameter_eq_input :
    coframeMatterActionParameterOfField
        (diracDualFormNativeECNormalContactField Base) =
      coframeMatterActionParameterOfField
        (diracDualFormNativeCoframeECContactField Input 0) := by
  unfold coframeMatterActionParameterOfField
    diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
    diracDualFormNativeCoframeECContactField
    diracDualFormNativeCoframeECContactPreparedActual
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext direction
      rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext direction
          change
            matterCoordinateEquiv
                (holonomicMatterCovariantDerivative Base 0 direction) =
              matterCoordinateEquiv
                (holonomicMatterCovariantDerivative Input 0 direction)
          congr 1
          unfold holonomicMatterCovariantDerivative
          rw [base_connection_origin_eq_input]
          rfl
        · rfl

private theorem baseGaugeEuler_eq_input :
    diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField Base) =
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeCoframeECContactField Input 0) := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [diracDualFormNativeCoframeGaugeEulerCovector_eq_coordinateFDeriv,
    diracDualFormNativeCoframeGaugeEulerCovector_eq_coordinateFDeriv,
    baseGaugeParameter_eq_input]
  rfl

private theorem baseMatterEuler_eq_input :
    diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField Base) =
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeCoframeECContactField Input 0) := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [diracDualFormNativeCoframeMatterEulerCovector_eq_coordinateFDeriv,
    diracDualFormNativeCoframeMatterEulerCovector_eq_coordinateFDeriv,
    baseMatterParameter_eq_input]
  rfl

theorem base_load_eq_input :
    diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
        fixedP506L0CartanECCauchyTemporalBase =
      diracDualFormNativeCoframeECContactLoad positiveSmoothUnifiedSource
        fixedP506L0CartanECCauchyTemporalInput 0 := by
  unfold diracDualFormNativeIdentityECLoad
    diracDualFormNativeCoframeECContactLoad
  have inputCoframe : Input.coframe 0 = 1 := by
    rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  rw [inputCoframe]
  change
    identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (diracDualFormNativeECNormalContactField Base) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (diracDualFormNativeECNormalContactField Base) =
      identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (diracDualFormNativeCoframeECContactField Input 0) +
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (diracDualFormNativeCoframeECContactField Input 0)
  rw [baseGaugeEuler_eq_input, baseMatterEuler_eq_input]

private theorem base_curvatureConstraint_temporalDiagonal00 :
    identityDiracDualECConstraintObservation
        (holonomicGravityCurvature Base 0) 0 = (1 / 8 : ℝ) := by
  rw [congrFun
    (identityDiracDualECConstraintObservation_explicit
      (holonomicGravityCurvature Base 0)) 0]
  change
    -(holonomicGravityCurvature Base 0 3 3 +
        holonomicGravityCurvature Base 0 4 4 +
        holonomicGravityCurvature Base 0 5 5) = (1 / 8 : ℝ)
  unfold holonomicGravityCurvature
  simp [pairFirst, pairSecond, minkowskiInternalSign]
  have baseOrigin : Base.gravityConnection 0 = fixedActionCartanConnection := by
    have pointZero :
        canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
      ext direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]
    rw [← pointZero]
    exact base_connection_zeroSlice_eq_fixedAction 0
  rw [show
      gravityConnectionDerivative Base 0 2 3 2 3 = 0 by
        exact base_connection_spatialDerivative_origin_zero 1 3 2 3,
    show gravityConnectionDerivative Base 0 3 2 2 3 = 0 by
      exact base_connection_spatialDerivative_origin_zero 2 2 2 3,
    show gravityConnectionDerivative Base 0 3 1 3 1 = 0 by
      exact base_connection_spatialDerivative_origin_zero 2 1 3 1,
    show gravityConnectionDerivative Base 0 1 3 3 1 = 0 by
      exact base_connection_spatialDerivative_origin_zero 0 3 3 1,
    show gravityConnectionDerivative Base 0 1 2 1 2 = 0 by
      exact base_connection_spatialDerivative_origin_zero 0 2 1 2,
    show gravityConnectionDerivative Base 0 2 1 1 2 = 0 by
      exact base_connection_spatialDerivative_origin_zero 1 1 1 2,
    baseOrigin,
    fixedActionCartanConnection_eq_positiveNormalForm]
  simp [pairFirst, pairSecond, minkowskiInternalSign,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    Fin.sum_univ_four, Fin.sum_univ_six]
  norm_num

private theorem input_load_temporalDiagonal00 :
    diracDualFormNativeCoframeECContactLoad Source Input 0
        (coframeCoordinateDirection 0 0) = -(665 / 216 : ℝ) := by
  have transported := DFunLike.congr_fun
    fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad
    (coframeCoordinateDirection 0 0)
  change
    diracDualFormNativeCoframeECContactLoad Source Input 0
        (coframeCoordinateDirection 0 0) =
      diracDualFormNativeIdentityECLoad Source OldCarry
        (coframeCoordinateDirection 0 0) at transported
  rw [transported]
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  have intrinsic := congrFun identityDiracDualECIntrinsicConstraintObservation 0
  change
    identityDiracDualECCurvatureObservation
        (gravityInternalPairVarianceNormalization
          (coframeWedge (1 : LorentzianCoframe)))
        (coframeCoordinateDirection 0 0) = -(3 : ℝ) at intrinsic
  rw [intrinsic]
  have stress :=
    fixedP506L0FinalCommonPreECLiveNonGravityStress_temporalDiagonal00
  unfold diracDualFormNativeECLiveNonGravityCoframeStress at stress
  simp only [add_apply] at stress
  rw [add_assoc, stress]
  norm_num

/-- The current-native Cartan base cannot already be the fixed point of its
own ordinary EC contact at the canonical occurrence.  Its curvature read is
`1/8`, while the matching source/action load is `-665/216`. -/
theorem fixedP506L0CartanECCauchyTemporalBase_curvature_ne_contactTarget_origin :
    holonomicGravityCurvature fixedP506L0CartanECCauchyTemporalBase 0 ≠
      diracDualFormNativeCoframeECContactCurvatureTarget
        positiveSmoothUnifiedSource fixedP506L0CartanECCauchyTemporalBase 0 := by
  intro fixedPoint
  let variation := coframeCoordinateDirection 0 0
  have coframeOne : Base.coframe 0 = (1 : LorentzianCoframe) :=
    congrFun fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one 0
  have contactLoad :
      diracDualFormNativeCoframeECContactLoad Source Base 0 variation =
        -(665 / 216 : ℝ) := by
    have loadEq :
        diracDualFormNativeCoframeECContactLoad Source Base 0 =
          diracDualFormNativeIdentityECLoad Source Base := by
      unfold diracDualFormNativeCoframeECContactLoad
        diracDualFormNativeIdentityECLoad
        diracDualFormNativeCoframeECContactField
        diracDualFormNativeECNormalContactField
        diracDualFormNativeCoframeECContactPreparedActual
        diracDualFormNativeECNormalPreparedActual
      rw [coframeOne]
      rfl
    rw [DFunLike.congr_fun loadEq variation, base_load_eq_input]
    exact input_load_temporalDiagonal00
  have targetObservation :
      coframeDiracDualECCurvatureObservation (Base.coframe 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget Source Base 0) =
        -diracDualFormNativeCoframeECContactLoad Source Base 0 := by
    unfold diracDualFormNativeCoframeECContactCurvatureTarget
    exact coframeDiracDualECCurvatureObservation_target _
      (by rw [coframeOne]; norm_num) _ _
  have observedFixedPoint := congrArg
    (fun curvature : PhysicalBivector =>
      coframeDiracDualECCurvatureObservation (Base.coframe 0)
        curvature variation) fixedPoint
  rw [coframeOne] at observedFixedPoint
  change
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Base 0) variation =
      identityDiracDualECCurvatureObservation
        (diracDualFormNativeCoframeECContactCurvatureTarget Source Base 0)
        variation at observedFixedPoint
  have curvature := base_curvatureConstraint_temporalDiagonal00
  change
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Base 0) variation = (1 / 8 : ℝ)
      at curvature
  have targetCoordinate := DFunLike.congr_fun targetObservation variation
  rw [coframeOne] at targetCoordinate
  change
    identityDiracDualECCurvatureObservation
        (diracDualFormNativeCoframeECContactCurvatureTarget Source Base 0)
        variation =
      -diracDualFormNativeCoframeECContactLoad Source Base 0 variation
      at targetCoordinate
  rw [contactLoad] at targetCoordinate
  rw [curvature, targetCoordinate] at observedFixedPoint
  norm_num at observedFixedPoint

private theorem output_normalContactField_eq :
    diracDualFormNativeECNormalContactField Output =
      restrictContinuumPointFieldToIIPlus
        (toContinuumPointField Output 0) := by
  rfl

private theorem base_normalContactField_eq :
    diracDualFormNativeECNormalContactField Base = FixedField 0 := by
  rfl

private theorem output_load_eq_base :
    diracDualFormNativeIdentityECLoad Source Output =
      diracDualFormNativeIdentityECLoad Source Base := by
  unfold diracDualFormNativeIdentityECLoad
  rw [output_normalContactField_eq]
  have pointZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have outputFieldZero :
      restrictContinuumPointFieldToIIPlus
          (toContinuumPointField Output 0) =
        OutputField 0 := by
    unfold OutputField
    rw [pointZero]
  have gaugeEq := outputGaugeEuler_eq_fixedField 0
  have matterEq := outputMatterEuler_eq_fixedField 0
  rw [pointZero] at gaugeEq matterEq
  rw [outputFieldZero, gaugeEq, matterEq, ← base_normalContactField_eq]

private theorem output_load_temporalDiagonal00 :
    diracDualFormNativeIdentityECLoad Source Output
        (coframeCoordinateDirection 0 0) = -(665 / 216 : ℝ) := by
  rw [output_load_eq_base, base_load_eq_input]
  exact input_load_temporalDiagonal00

private theorem output_curvatureConstraint_temporalDiagonal00 :
    identityDiracDualECConstraintObservation
        (holonomicGravityCurvature Output 0) 0 = (1 / 8 : ℝ) := by
  have curvature :=
    fixedP506L0CartanECCauchyTemporalGlobalActual_curvature_zeroSlice
      (0 : StageNineSpatialPoint)
  have pointZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [pointZero] at curvature
  rw [curvature]
  unfold diracDualFormNativeECCauchyCurvatureTarget
  rw [identityDiracDualECConstraintObservation_totalTarget]
  unfold diracDualFormNativeECCauchyCurrentCurvature
    diracDualFormNativeECNormalPreparedActual
    cartanECCauchyTemporalProfileInput
  change
    identityDiracDualECConstraintObservation
        (holonomicGravityCurvature
          (fullyRecenterHolonomicConfiguration Base 0) 0) 0 = _
  rw [fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional]
  exact base_curvatureConstraint_temporalDiagonal00

private theorem output_constraintBalance_temporalDiagonal00 :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0)
          (coframeCoordinateDirection 0 0) +
        diracDualFormNativeIdentityECLoad Source Output
          (coframeCoordinateDirection 0 0) =
      -(319 / 108 : ℝ) := by
  have curvature := output_curvatureConstraint_temporalDiagonal00
  change
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Output 0)
        (coframeCoordinateDirection 0 0) = (1 / 8 : ℝ) at curvature
  rw [curvature, output_load_temporalDiagonal00]
  norm_num

/-- The temporal writer closes the twelve EC evolution rows, but the same
source-native output retains the exact temporal coframe constraint read
`1/8 - 665/216 = -319/108`.  This rejects the temporal-only successor; the
read is not consumed by any writer. -/
theorem
    fixedP506L0CartanECCauchyTemporalGlobalActual_coframeResidual_temporalDiagonal00 :
    (diracDualFormNativePointwiseJointResidual Source Output 0).coframe
        (coframeCoordinateDirection 0 0) = -(319 / 108 : ℝ) := by
  let variation := coframeCoordinateDirection 0 0
  have outputSimplicity : FormNativeGravitySimplicityEquation Output :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
      Source Input
  have outputAuxiliary : FormNativeGravityAuxiliaryEquation Output :=
    installFormNativeGravityReaction_auxiliaryEquation
      (cartanECCauchyTemporalConnectedActual Source Input)
  have reduction :=
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      Source Output outputSimplicity outputAuxiliary
      (fun _ => variation) 0
  change
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity Source 0
        (toContinuumPointField Output 0) variation =
      diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField Output 0) variation at reduction
  change
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField Output 0) variation = _
  rw [← reduction]
  rw [
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
      Source 0 (toContinuumPointField Output 0)
      (by
        change Matrix.det (Input.coframe 0) ≠ 0
        rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
        norm_num)
      variation]
  have outputCoframeOne :
      (toContinuumPointField Output 0).coframe =
        (1 : LorentzianCoframe) := by
    change Input.coframe 0 = 1
    rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  rw [outputCoframeOne]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField Output 0).gravityCurvature) =
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0) variation by
      rfl]
  rw [← identityDiracDualECCurvatureObservation_intrinsic_apply variation]
  have balance := output_constraintBalance_temporalDiagonal00
  unfold diracDualFormNativeIdentityECLoad at balance
  rw [output_normalContactField_eq] at balance
  simpa only [add_apply, add_assoc] using balance

theorem
    fixedP506L0CartanECCauchyTemporalGlobalActual_not_onPointwiseJointZeroFiber_origin :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber Source Output 0 := by
  intro zeroFiber
  have projected := congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.coframe (coframeCoordinateDirection 0 0)) zeroFiber
  rw [
    fixedP506L0CartanECCauchyTemporalGlobalActual_coframeResidual_temporalDiagonal00]
    at projected
  norm_num at projected

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
