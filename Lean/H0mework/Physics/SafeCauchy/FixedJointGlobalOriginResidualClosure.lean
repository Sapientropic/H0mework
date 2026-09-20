import H0mework.Physics.SafeCauchy.FixedJointGlobalDevelopment
import H0mework.Physics.SafeCauchy.FixedArbitraryCoframeJointZeroFiber
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity
import H0mework.Physics.CartanAction.CartanReactionCurrentRestartGlobalRegularity
import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity
import H0mework.Physics.TimePrimitive.SecondAmbientJetRegularity
import H0mework.Physics.DualVariation.PointwiseP286RequiredExteriorProfileRegularity
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity
import H0mework.Physics.GaugeAction.P286GaugeConnectionAlgebraicCurrentRegularity
import H0mework.Physics.Coframe.CoframeNativeMatterDualGlobalRadialActionAcceptance
import H0mework.Physics.Coframe.CoframeNativeMatterFrameActionReadout
import H0mework.Physics.Coframe.CoframeNativeConjugateMatterFrameActionReadout
import H0mework.Physics.CoframeResponse.MatterActionAcceptance
import H0mework.Physics.CoframeResponse.MatterEulerAcceptance

/-!
# Fixed P506 Cauchy-safe joint global origin closure

The source/current-only joint occurrence writes the complete temporal,
constitutive, P286, Cartan--EC, frame-primal, frame-adjoint, and gravity
reaction chain into one common global actual.  This module proves that the
resulting actual lies in the complete nine-channel joint zero fiber at the
canonical spacetime origin.

Residuals are used only by the final readout.  Every field and first-jet
change consumed below is emitted by the joint action occurrence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalOriginResidualClosure

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open Filter
open StageNineCanonicalTimePrimitiveMeasurableGermCalculus
open StageNineCanonicalCauchyState
open StageNineCanonicalRestrictionP286CoherentRegularity
open StageNineConjugateMatterVariation
open StageNineConjugateMatterActionTimeVelocity
open StageNineCoframeFirstJet
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineCoframeNativeMatterDualGlobalRadialActionAcceptance
open StageNineCoframeNativeMatterFrameAction
open StageNineCoframeNativeMatterFrameActionReadout
open StageNineCoframeNativeMatterOriginActionWrite
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeHolonomicCauchySafeRealization
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureTargetLocalRegularity
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeArbitraryCoframeJointZeroFiber
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativePointwiseP286RequiredExteriorProfileRegularity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineLorentzConnectionVariation
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineMatterPointwiseEquation
open StageNineMatterActionTimeVelocity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineRadialCurveIntegralFirstJet
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance cauchySafeOriginP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance cauchySafeOriginP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance cauchySafeOriginMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev LocalTemporal : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
    Source (fullyRecenterHolonomicConfiguration Current 0)

private abbrev GlobalTemporal : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalTemporalCurrent Source Current

private abbrev LocalConstitutive : StageNineHolonomicConfiguration :=
  diracDualFormNativeConstitutiveWrittenCurrent Source LocalTemporal

private abbrev GlobalConstitutive : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalConstitutiveCurrent Source Current

private abbrev LocalP286 : StageNineHolonomicConfiguration :=
  formNativeCurrentP286CompleteActionResponseOperator Source LocalConstitutive

private abbrev GlobalP286 : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalP286Current Source Current

private abbrev GlobalEC : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
    Source GlobalP286 0

private abbrev LocalEC : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
    Source LocalP286 0

private abbrev GlobalECPath : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECPathCurrent Source Current

private abbrev GlobalPrimal : StageNineHolonomicConfiguration :=
  actionGeneratedGlobalFrameTimeMatterActual GlobalECPath

private abbrev GlobalMatterDual : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalMatterDualCurrent Source Current

private abbrev GlobalFinal : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual

private theorem current_smooth : Current.Smooth := by
  exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_smooth
    Source Prepared
    fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate

private theorem current_nondegenerate : Current.Nondegenerate := by
  intro point
  change Matrix.det (Prepared.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

private theorem current_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Current.coframe point) ≠ 0 := by
  change coframeTemporalPrincipalScalar (Prepared.coframe point) ≠ 0
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
      point

private theorem matterCorrection_contDiffAt_origin :
    ContDiffAt ℝ 1
      (completeJointMatterTemporalCoordinateCorrection Source Current) 0 :=
  (completeJointMatterTemporalCoordinateCorrection_contDiffAt
    Source Current current_smooth 0 (current_nondegenerate 0)
    (current_noncharacteristic 0)).of_le (by simp)

private theorem adjointCorrection_contDiffAt_origin :
    ContDiffAt ℝ 1
      (completeJointAdjointTemporalCoordinateCorrection Source Current) 0 :=
  (completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
    Source Current current_smooth 0 (current_nondegenerate 0)
    (current_noncharacteristic 0)).of_le (by simp)

private theorem scalarAcceleration_contDiffAt_origin :
    ContDiffAt ℝ 1
      (completeJointCauchySafeScalarAccelerationProfile Source Current) 0 :=
  (completeJointCauchySafeScalarAccelerationProfile_contDiffAt Source Current
    current_smooth 0 (current_nondegenerate 0)
    (scalarCoordinateTimePrincipalWeight_ne_zero Current 0
      (current_nondegenerate 0) (current_noncharacteristic 0))).of_le
        (by simp)

private theorem current_scalar_contDiff : ContDiff ℝ ∞ Current.scalar :=
  current_smooth.2.2.2.2.2.2.1

private theorem current_matterCoordinates_contDiff :
    ContDiff ℝ ∞
      (fun point => matterCoordinateEquiv (Current.matter point)) :=
  current_smooth.2.2.2.2.2.2.2.1

private theorem current_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates Current) :=
  holonomicConjugateMatterCoordinates_contDiff Current current_smooth

private theorem matterPrimitive_contDiffAt_origin :
    ContDiffAt ℝ 1
      (canonicalTimePrimitive
        (completeJointMatterTemporalCoordinateCorrection Source Current)) 0 :=
  canonicalTimePrimitive_contDiffAt_of_contDiffAt _
    matterCorrection_contDiffAt_origin

private theorem adjointPrimitive_contDiffAt_origin :
    ContDiffAt ℝ 1
      (canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Current)) 0 :=
  canonicalTimePrimitive_contDiffAt_of_contDiffAt _
    adjointCorrection_contDiffAt_origin

private theorem scalarSecondPrimitive_contDiffAt_origin :
    ContDiffAt ℝ 1
      (canonicalTimeSecondPrimitive
        (completeJointCauchySafeScalarAccelerationProfile Source Current)) 0 :=
  canonicalTimeSecondPrimitive_contDiffAt_of_contDiffAt _
    scalarAcceleration_contDiffAt_origin

private theorem globalTemporal_scalar_eq :
    GlobalTemporal.scalar =
      Current.scalar + canonicalTimeSecondPrimitive
        (completeJointCauchySafeScalarAccelerationProfile Source Current) := by
  rfl

private theorem globalTemporal_matterCoordinates_eq :
    (fun point => matterCoordinateEquiv (GlobalTemporal.matter point)) =
      (fun point => matterCoordinateEquiv (Current.matter point)) +
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Current) := by
  funext point
  simp [GlobalTemporal, cauchySafeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]

private theorem globalTemporal_conjugateMatterCoordinates_eq :
    holonomicConjugateMatterCoordinates GlobalTemporal =
      holonomicConjugateMatterCoordinates Current +
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Current) := by
  funext point
  simp [GlobalTemporal, cauchySafeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
    holonomicConjugateMatterCoordinates, matterDualCoordinates_add]

private theorem globalTemporal_scalar_contDiffAt_origin :
    ContDiffAt ℝ 1 GlobalTemporal.scalar 0 := by
  rw [globalTemporal_scalar_eq]
  exact current_scalar_contDiff.contDiffAt.of_le (by simp) |>.add
    scalarSecondPrimitive_contDiffAt_origin

private theorem globalTemporal_matterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (GlobalTemporal.matter point)) 0 := by
  rw [globalTemporal_matterCoordinates_eq]
  exact current_matterCoordinates_contDiff.contDiffAt.of_le (by simp) |>.add
    matterPrimitive_contDiffAt_origin

private theorem globalTemporal_conjugateMatterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1 (holonomicConjugateMatterCoordinates GlobalTemporal) 0 := by
  rw [globalTemporal_conjugateMatterCoordinates_eq]
  exact current_conjugateMatterCoordinates_contDiff.contDiffAt.of_le (by simp)
    |>.add adjointPrimitive_contDiffAt_origin

private theorem current_coframe_contDiff :
    ContDiff ℝ ∞ Current.coframe :=
  holonomicCoframe_contDiff Current current_smooth

private theorem current_gaugeConnectionCoordinate_contDiff :
    ContDiff ℝ ∞ (holonomicP286GaugeConnectionCoordinate Current) :=
  holonomicP286GaugeConnectionCoordinate_contDiff Current current_smooth

private theorem current_gaugeCurvatureCoordinate_contDiff :
    ContDiff ℝ ∞ (holonomicP286GaugeCurvatureCoordinate Current) := by
  apply contDiff_pi'
  intro pair
  apply contDiff_piLp'
  intro coordinate
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (holonomicGaugeCurvature_coordinate_contDiff Current current_smooth pair)

private theorem globalTemporal_gaugeConnection_eq :
    GlobalTemporal.gaugeConnection = Current.gaugeConnection := by
  rfl

private theorem globalTemporal_coframe_eq :
    GlobalTemporal.coframe = Current.coframe :=
  sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_coframe
    Source Current

private theorem globalConstitutive_coframe_eq_current :
    GlobalConstitutive.coframe = Current.coframe := by
  calc
    GlobalConstitutive.coframe = GlobalTemporal.coframe := by rfl
    _ = Current.coframe := globalTemporal_coframe_eq

private theorem globalConstitutive_coframe_contDiffAt_origin :
    ContDiffAt ℝ 0 GlobalConstitutive.coframe 0 := by
  rw [globalConstitutive_coframe_eq_current]
  exact current_coframe_contDiff.contDiffAt.of_le (by simp)

private theorem globalConstitutive_nondegenerate (point : BasePoint) :
    Matrix.det (GlobalConstitutive.coframe point) ≠ 0 := by
  rw [globalConstitutive_coframe_eq_current]
  exact current_nondegenerate point

private theorem globalConstitutive_gaugeConnection_eq :
    GlobalConstitutive.gaugeConnection = Current.gaugeConnection := by
  calc
    GlobalConstitutive.gaugeConnection = GlobalTemporal.gaugeConnection :=
      diracDualFormNativeConstitutiveWrittenCurrent_gaugeConnection
        Source GlobalTemporal
    _ = Current.gaugeConnection := globalTemporal_gaugeConnection_eq

private theorem globalConstitutive_gaugeConnectionCoordinate_eq :
    holonomicP286GaugeConnectionCoordinate GlobalConstitutive =
      holonomicP286GaugeConnectionCoordinate Current := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [globalConstitutive_gaugeConnection_eq]

private theorem globalConstitutive_gaugeConnection_contDiffAt_origin :
    ContDiffAt ℝ 0
      (holonomicP286GaugeConnectionCoordinate GlobalConstitutive) 0 := by
  rw [globalConstitutive_gaugeConnectionCoordinate_eq]
  exact current_gaugeConnectionCoordinate_contDiff.contDiffAt.of_le (by simp)

private theorem globalConstitutive_gaugeAuxiliary_eq :
    GlobalConstitutive.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source GlobalTemporal :=
  diracDualFormNativeConstitutiveWrittenCurrent_gaugeAuxiliary
    Source GlobalTemporal

private theorem globalConstitutive_auxiliaryCoordinate_eq :
    holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source) (Current.coframe point)
          (holonomicP286GaugeCurvatureCoordinate Current point) := by
  funext point pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [globalConstitutive_gaugeAuxiliary_eq]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [globalTemporal_coframe_eq,
    holonomicGaugeCurvature_eq_of_connection_eq
      GlobalTemporal Current globalTemporal_gaugeConnection_eq point]
  unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    holonomicP286GaugeCurvatureCoordinate
  rw [show
    (fun pair => p286CoordinateEquiv
      (holonomicGaugeCurvature Current point pair)) =
      formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature Current point) by rfl,
    formNativeP286GaugeActual_coordinate_actual,
    formNativeP286GaugeActualToCoordinateLinear_apply]

private theorem globalConstitutive_auxiliary_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive) 0 := by
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings Source) (Current.coframe 0)
      (current_nondegenerate 0)
      (holonomicP286GaugeCurvatureCoordinate Current 0)
  have inner : ContDiffAt ℝ ∞
      (fun point =>
        (Current.coframe point,
          holonomicP286GaugeCurvatureCoordinate Current point)) 0 :=
    current_coframe_contDiff.contDiffAt.prodMk
      current_gaugeCurvatureCoordinate_contDiff.contDiffAt
  have composed := outer.comp 0 inner
  rw [globalConstitutive_auxiliaryCoordinate_eq]
  exact composed

private theorem globalConstitutive_scalar_contDiffAt_origin :
    ContDiffAt ℝ 1 GlobalConstitutive.scalar 0 := by
  change ContDiffAt ℝ 1 GlobalTemporal.scalar 0
  exact globalTemporal_scalar_contDiffAt_origin

private theorem globalConstitutive_matterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (GlobalConstitutive.matter point))
      0 := by
  change ContDiffAt ℝ 1
    (fun point => matterCoordinateEquiv (GlobalTemporal.matter point)) 0
  exact globalTemporal_matterCoordinates_contDiffAt_origin

private theorem globalConstitutive_conjugateMatter_eq :
    GlobalConstitutive.conjugateMatter = GlobalTemporal.conjugateMatter := by
  rfl

private theorem
    globalConstitutive_conjugateMatterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates GlobalConstitutive) 0 := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates GlobalConstitutive =
        holonomicConjugateMatterCoordinates GlobalTemporal := by
    unfold holonomicConjugateMatterCoordinates
    rw [globalConstitutive_conjugateMatter_eq]
  rw [coordinatesEq]
  exact globalTemporal_conjugateMatterCoordinates_contDiffAt_origin

private theorem scalarP286Action_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun candidate =>
        scalarMotherLieAction
          (p286LieBlockEmbed
            (GlobalConstitutive.gaugeConnection candidate direction))
          (GlobalConstitutive.scalar candidate)) 0 := by
  have matrixRegular : ContDiffAt ℝ 0
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate GlobalConstitutive candidate
          direction) 0 :=
    contDiffAt_pi.mp
      globalConstitutive_gaugeConnection_contDiffAt_origin direction
  have actionRegular :=
    (scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.contDiffAt.comp
      0 matrixRegular).clm_apply
        (globalConstitutive_scalar_contDiffAt_origin.of_le (by simp))
  change ContDiffAt ℝ 0
    (fun candidate =>
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (holonomicP286GaugeConnectionCoordinate GlobalConstitutive
              candidate direction)))
        (GlobalConstitutive.scalar candidate)) 0 at actionRegular
  simpa only [holonomicP286GaugeConnectionCoordinate,
    p286CoordinateEquiv.symm_apply_apply] using actionRegular

private theorem globalConstitutive_scalarCovariant_contDiffAt_origin :
    ContDiffAt ℝ 0
      (holonomicScalarCovariantDerivative GlobalConstitutive) 0 := by
  apply contDiffAt_pi.mpr
  intro direction
  have fderivRegular : ContDiffAt ℝ 0
      (fderiv ℝ GlobalConstitutive.scalar) 0 :=
    globalConstitutive_scalar_contDiffAt_origin.fderiv_right (m := 0)
      (by norm_num)
  have derivativeRegular : ContDiffAt ℝ 0
      (fun candidate =>
        fieldDirectionalDerivative GlobalConstitutive.scalar candidate
          direction) 0 := by
    unfold fieldDirectionalDerivative
    exact fderivRegular.clm_apply contDiffAt_const
  unfold holonomicScalarCovariantDerivative
  exact derivativeRegular.add
    (scalarP286Action_contDiffAt_origin direction)

private theorem globalConstitutive_coframe_eq_globalTemporal :
    GlobalConstitutive.coframe = GlobalTemporal.coframe := by
  rfl

private theorem globalConstitutive_gaugeConnection_eq_globalTemporal :
    GlobalConstitutive.gaugeConnection = GlobalTemporal.gaugeConnection :=
  diracDualFormNativeConstitutiveWrittenCurrent_gaugeConnection
    Source GlobalTemporal

private theorem globalConstitutive_constitutiveAt (point : BasePoint) :
    diracDualFormNativeConstitutiveAuxiliaryField
        Source GlobalConstitutive point =
      GlobalConstitutive.gaugeAuxiliary point := by
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [globalConstitutive_coframe_eq_globalTemporal,
    holonomicGaugeCurvature_eq_of_connection_eq
      GlobalConstitutive GlobalTemporal
      globalConstitutive_gaugeConnection_eq_globalTemporal point,
    globalConstitutive_gaugeAuxiliary_eq]
  rfl

private theorem globalConstitutive_directRequiredExterior_contDiffAt_origin :
    ContDiffAt ℝ 0
      (pointwiseDirectP286RequiredExteriorDerivative
        Source GlobalConstitutive) 0 := by
  have auxiliaryRegular0 : ContDiffAt ℝ 0
      (holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive) 0 :=
    globalConstitutive_auxiliary_contDiffAt_origin.of_le (by simp)
  have scalarRegular0 : ContDiffAt ℝ 0 GlobalConstitutive.scalar 0 :=
    globalConstitutive_scalar_contDiffAt_origin.of_le (by simp)
  rw [contDiffAt_zero]
  let domain : Set BasePoint :=
    { point | ContinuousAt
        (pointwiseDirectP286RequiredExteriorDerivative
          Source GlobalConstitutive) point }
  refine ⟨domain, ?_, ?_⟩
  · change ∀ᶠ point in nhds 0, ContinuousAt
      (pointwiseDirectP286RequiredExteriorDerivative
        Source GlobalConstitutive) point
    filter_upwards
        [globalConstitutive_coframe_contDiffAt_origin.eventually (by simp),
          globalConstitutive_gaugeConnection_contDiffAt_origin.eventually
            (by simp),
          auxiliaryRegular0.eventually (by simp),
          scalarRegular0.eventually (by simp),
          globalConstitutive_scalarCovariant_contDiffAt_origin.eventually
            (by simp),
          globalConstitutive_matterCoordinates_contDiffAt_origin.eventually
            (by simp),
          globalConstitutive_conjugateMatterCoordinates_contDiffAt_origin.eventually
            (by simp)] with point coframeRegular connectionRegular
              auxiliaryRegular scalarRegular scalarCovariantRegular
              matterRegular conjugateRegular
    exact
      pointwiseDirectP286RequiredExteriorDerivative_continuousAt_of_actionData
        Source GlobalConstitutive point coframeRegular.continuousAt
        (globalConstitutive_nondegenerate point) connectionRegular.continuousAt
        auxiliaryRegular.continuousAt scalarRegular.continuousAt
        scalarCovariantRegular.continuousAt matterRegular.continuousAt
        conjugateRegular.continuousAt
  · intro point pointIn
    exact pointIn.continuousWithinAt

private theorem globalConstitutive_requiredExterior_contDiffAt_origin :
    ContDiffAt ℝ 0
      (completeJointP286RequiredExteriorProfile Source GlobalConstitutive) 0 := by
  exact
    globalConstitutive_directRequiredExterior_contDiffAt_origin.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun point =>
        completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
          Source GlobalConstitutive point
          (globalConstitutive_constitutiveAt point))


private theorem globalP286JetCLM_contDiffAt_origin :
    ContDiffAt ℝ 0
      (cauchySafeJointGlobalP286JetCLM Source GlobalConstitutive) 0 := by
  exact cauchySafeJointGlobalP286JetCLM_contDiffAt_of_required
    Source GlobalConstitutive 0
      globalConstitutive_requiredExterior_contDiffAt_origin

private theorem globalP286_exteriorDerivative_origin_eq_required :
    holonomicP286GaugeAuxiliaryExteriorDerivative GlobalP286 0 =
      completeJointP286RequiredExteriorProfile
        Source GlobalConstitutive 0 := by
  change
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source GlobalConstitutive) 0 =
      completeJointP286RequiredExteriorProfile
        Source GlobalConstitutive 0
  exact
    sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_exteriorDerivative_origin
      Source GlobalConstitutive globalP286JetCLM_contDiffAt_origin

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, Fin.sum_univ_three]

private theorem temporal_eq : GlobalTemporal = LocalTemporal := by
  unfold GlobalTemporal cauchySafeJointGlobalTemporalCurrent LocalTemporal
  rw [fullyRecenterHolonomicConfiguration_zero]

private theorem constitutive_eq : GlobalConstitutive = LocalConstitutive := by
  change
    diracDualFormNativeConstitutiveWrittenCurrent Source GlobalTemporal =
      diracDualFormNativeConstitutiveWrittenCurrent Source LocalTemporal
  exact congrArg (diracDualFormNativeConstitutiveWrittenCurrent Source)
    temporal_eq

private theorem localConstitutive_eq_readout :
    LocalConstitutive =
      formNativeP286GaugeConstitutiveReadout Source LocalTemporal := by
  rfl

private theorem localReadout_constitutiveAt :
    diracDualFormNativeConstitutiveAuxiliaryField Source
        (formNativeP286GaugeConstitutiveReadout Source LocalTemporal) 0 =
      (formNativeP286GaugeConstitutiveReadout Source LocalTemporal
        ).gaugeAuxiliary 0 := by
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [formNativeP286GaugeConstitutiveReadout_gaugeAuxiliary,
    holonomicGaugeCurvature_formNativeP286GaugeConstitutiveReadout]
  rfl

private theorem localP286_coordinate_origin_eq_localConstitutive :
    holonomicP286GaugeAuxiliaryCoordinate LocalP286 0 =
      holonomicP286GaugeAuxiliaryCoordinate LocalConstitutive 0 := by
  funext pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [formNativeCurrentP286CompleteActionResponseOperator_gaugeAuxiliary_origin]

private theorem globalP286_requiredExterior_origin_eq_localConstitutive :
    completeJointP286RequiredExteriorProfile Source GlobalConstitutive 0 =
      formNativeCurrentP286RequiredExteriorDerivative
        Source LocalConstitutive := by
  rw [constitutive_eq, localConstitutive_eq_readout]
  change
    completeJointP286RequiredExteriorProfile Source
        (formNativeP286GaugeConstitutiveReadout Source LocalTemporal) 0 =
      pointwiseDirectP286RequiredExteriorDerivative Source
        (formNativeP286GaugeConstitutiveReadout Source LocalTemporal) 0
  exact
    completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
      Source (formNativeP286GaugeConstitutiveReadout Source LocalTemporal) 0
      localReadout_constitutiveAt

private theorem globalP286_eq_localInputWrite :
    GlobalP286 =
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
        Source LocalConstitutive := by
  change
    sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
        Source GlobalConstitutive =
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
        Source LocalConstitutive
  exact congrArg
    (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite Source)
    constitutive_eq

private theorem globalP286_auxiliaryCoordinate_origin_eq_localP286 :
    holonomicP286GaugeAuxiliaryCoordinate GlobalP286 0 =
      holonomicP286GaugeAuxiliaryCoordinate LocalP286 0 := by
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source GlobalConstitutive) 0 =
      holonomicP286GaugeAuxiliaryCoordinate
        (formNativeCurrentP286CompleteActionResponseOperator
          Source LocalConstitutive) 0
  calc
    holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
            Source GlobalConstitutive) 0 =
        holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive 0 :=
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate_zero
        Source GlobalConstitutive
    _ = holonomicP286GaugeAuxiliaryCoordinate LocalConstitutive 0 :=
      congrArg (fun configuration =>
        holonomicP286GaugeAuxiliaryCoordinate configuration 0)
        constitutive_eq
    _ = holonomicP286GaugeAuxiliaryCoordinate LocalP286 0 :=
      localP286_coordinate_origin_eq_localConstitutive.symm

private theorem globalP286_exteriorDerivative_origin_eq_localP286 :
    holonomicP286GaugeAuxiliaryExteriorDerivative GlobalP286 0 =
      holonomicP286GaugeAuxiliaryExteriorDerivative LocalP286 0 := by
  calc
    holonomicP286GaugeAuxiliaryExteriorDerivative GlobalP286 0 =
        completeJointP286RequiredExteriorProfile
          Source GlobalConstitutive 0 :=
      globalP286_exteriorDerivative_origin_eq_required
    _ = formNativeCurrentP286RequiredExteriorDerivative
          Source LocalConstitutive :=
      globalP286_requiredExterior_origin_eq_localConstitutive
    _ = holonomicP286GaugeAuxiliaryExteriorDerivative LocalP286 0 :=
      (formNativeCurrentP286CompleteActionResponseOperator_exteriorDerivative_origin
        Source LocalConstitutive).symm

private theorem globalP286_exteriorCovariant_origin_eq_localP286 :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative GlobalP286 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative LocalP286 0 := by
  have connectionEq :
      holonomicP286GaugeConnectionCoordinate GlobalP286 0 =
        holonomicP286GaugeConnectionCoordinate LocalP286 0 := by
    rw [globalP286_eq_localInputWrite]
    rfl
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    globalP286_exteriorDerivative_origin_eq_localP286,
    connectionEq, globalP286_auxiliaryCoordinate_origin_eq_localP286]

private theorem globalP286_actionJet_origin_eq_localP286 :
    generatedDiracDualFormNativePointwiseActionJet Source GlobalP286 0 =
      generatedDiracDualFormNativePointwiseActionJet Source LocalP286 0 := by
  rw [globalP286_eq_localInputWrite]
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate
          (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
            Source LocalConstitutive) 0 =
        holonomicP286GaugeAuxiliaryCoordinate LocalP286 0 := by
    rw [← globalP286_eq_localInputWrite]
    exact globalP286_auxiliaryCoordinate_origin_eq_localP286
  have gaugeAuxiliaryEq :
      (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source LocalConstitutive).gaugeAuxiliary 0 =
        LocalP286.gaugeAuxiliary 0 := by
    funext pair
    exact p286CoordinateEquiv.injective (congrFun auxiliaryEq pair)
  have exteriorCovariantEq :
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
            Source LocalConstitutive) 0 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative LocalP286 0 := by
    rw [← globalP286_eq_localInputWrite]
    exact globalP286_exteriorCovariant_origin_eq_localP286
  have coframeEq :
      (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source LocalConstitutive).coframe = LocalP286.coframe :=
    rfl
  have conjugateMatterEq :
      (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source LocalConstitutive).conjugateMatter =
        LocalP286.conjugateMatter :=
    rfl
  have matterMomentumEq
      (direction : MatterCoordinateCarrier)
      (derivativeDirection : LorentzianIndex) :
      matterDifferentialMomentum Source
          (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
            Source LocalConstitutive) direction derivativeDirection =
        matterDifferentialMomentum Source LocalP286 direction
          derivativeDirection := by
    funext point
    unfold matterDifferentialMomentum matterDifferentialVariationVector
      generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [coframeEq, conjugateMatterEq]
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact gaugeAuxiliaryEq
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · exact exteriorCovariantEq
  · rfl
  · funext direction
    change matterDifferentialMomentumDivergence Source
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source LocalConstitutive) direction 0 =
      matterDifferentialMomentumDivergence Source LocalP286 direction 0
    unfold matterDifferentialMomentumDivergence
    simp_rw [matterMomentumEq direction]

private theorem globalP286_pointField_origin_eq_localP286 :
    toContinuumPointField GlobalP286 0 =
      toContinuumPointField LocalP286 0 :=
  congrArg DiracDualFormNativePointwiseActionJetCarrier.pointField
    globalP286_actionJet_origin_eq_localP286

private theorem globalP286_coframe_eq_localP286 :
    GlobalP286.coframe = LocalP286.coframe := by
  rw [globalP286_eq_localInputWrite]
  rfl

private theorem globalP286_gravityConnection_eq_localP286 :
    GlobalP286.gravityConnection = LocalP286.gravityConnection := by
  rw [globalP286_eq_localInputWrite]
  rfl

private theorem globalP286_contactField_origin_eq_localP286 :
    diracDualFormNativeCoframeECContactField GlobalP286 0 =
      diracDualFormNativeCoframeECContactField LocalP286 0 := by
  unfold diracDualFormNativeCoframeECContactField
    diracDualFormNativeCoframeECContactPreparedActual
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus,
    toContinuumPointField_restrictHolonomicConfigurationToIIPlus,
    globalP286_pointField_origin_eq_localP286]

private theorem globalP286_contactLoad_origin_eq_localP286 :
    diracDualFormNativeCoframeECContactLoad Source GlobalP286 0 =
      diracDualFormNativeCoframeECContactLoad Source LocalP286 0 := by
  unfold diracDualFormNativeCoframeECContactLoad
  rw [globalP286_coframe_eq_localP286,
    globalP286_contactField_origin_eq_localP286]

private theorem globalP286_preparedCurvature_origin_eq_localP286 :
    holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual GlobalP286) 0 =
      holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual LocalP286) 0 := by
  funext internalPair spacetimePair
  unfold diracDualFormNativeCoframeECContactPreparedActual
    restrictHolonomicConfigurationToIIPlus holonomicGravityCurvature
    gravityConnectionDerivative
  rw [globalP286_gravityConnection_eq_localP286]

private theorem globalP286_ECTarget_origin_eq_localP286 :
    diracDualFormNativeCoframeECContactCurvatureTarget
        Source GlobalP286 0 =
      diracDualFormNativeCoframeECContactCurvatureTarget
        Source LocalP286 0 := by
  unfold diracDualFormNativeCoframeECContactCurvatureTarget
  rw [globalP286_coframe_eq_localP286,
    globalP286_preparedCurvature_origin_eq_localP286,
    globalP286_contactLoad_origin_eq_localP286]

private theorem globalEC_gravityConnection_eq_localEC :
    GlobalEC.gravityConnection = LocalEC.gravityConnection := by
  change
    coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
        (GlobalP286.gravityConnection 0)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          Source GlobalP286 0) =
      coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
        (LocalP286.gravityConnection 0)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          Source LocalP286 0)
  rw [globalP286_gravityConnection_eq_localP286,
    globalP286_ECTarget_origin_eq_localP286]

private theorem globalEC_coframe_eq_localEC :
    GlobalEC.coframe = LocalEC.coframe := by
  calc
    GlobalEC.coframe = GlobalP286.coframe := rfl
    _ = LocalP286.coframe := globalP286_coframe_eq_localP286
    _ = LocalEC.coframe := rfl

private theorem globalEC_gravityAuxiliary_eq_localEC :
    GlobalEC.gravityAuxiliary = LocalEC.gravityAuxiliary := by
  funext point
  change physicalIIPlusBivector (GlobalP286.coframe point) =
    physicalIIPlusBivector (LocalP286.coframe point)
  rw [globalP286_coframe_eq_localP286]

private theorem globalEC_multiplier_eq_localEC :
    GlobalEC.gravitySimplicityMultiplier =
      LocalEC.gravitySimplicityMultiplier := by
  rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reactionSelfGenerated,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reactionSelfGenerated]
  funext point
  unfold formNativeGravityReactionField
    holonomicContravariantGravityCurvature holonomicGravityCurvature
    gravityConnectionDerivative
  rw [globalEC_gravityAuxiliary_eq_localEC,
    globalEC_gravityConnection_eq_localEC]

private theorem globalEC_gaugeConnection_eq_localEC :
    GlobalEC.gaugeConnection = LocalEC.gaugeConnection := by
  rw [show GlobalEC.gaugeConnection = GlobalP286.gaugeConnection by rfl,
    show LocalEC.gaugeConnection = LocalP286.gaugeConnection by rfl,
    globalP286_eq_localInputWrite]
  rfl

private theorem globalEC_gaugeAuxiliary_origin_eq_localEC :
    GlobalEC.gaugeAuxiliary 0 = LocalEC.gaugeAuxiliary 0 := by
  change GlobalP286.gaugeAuxiliary 0 = LocalP286.gaugeAuxiliary 0
  funext pair
  exact p286CoordinateEquiv.injective
    (congrFun globalP286_auxiliaryCoordinate_origin_eq_localP286 pair)

private theorem globalEC_scalar_eq_localEC :
    GlobalEC.scalar = LocalEC.scalar := by
  rw [show GlobalEC.scalar = GlobalP286.scalar by rfl,
    show LocalEC.scalar = LocalP286.scalar by rfl,
    globalP286_eq_localInputWrite]
  rfl

private theorem globalEC_matter_eq_localEC :
    GlobalEC.matter = LocalEC.matter := by
  rw [show GlobalEC.matter = GlobalP286.matter by rfl,
    show LocalEC.matter = LocalP286.matter by rfl,
    globalP286_eq_localInputWrite]
  rfl

private theorem globalEC_conjugateMatter_eq_localEC :
    GlobalEC.conjugateMatter = LocalEC.conjugateMatter := by
  rw [show GlobalEC.conjugateMatter = GlobalP286.conjugateMatter by rfl,
    show LocalEC.conjugateMatter = LocalP286.conjugateMatter by rfl,
    globalP286_eq_localInputWrite]
  rfl

private theorem globalEC_p286ExteriorCovariant_origin_eq_localEC :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative GlobalEC 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative LocalEC 0 := by
  change
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative GlobalP286 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative LocalP286 0
  exact globalP286_exteriorCovariant_origin_eq_localP286

private theorem globalEC_gravityExteriorCovariant_origin_eq_localEC :
    holonomicGravityAuxiliaryExteriorCovariantDerivative GlobalEC 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative LocalEC 0 := by
  have derivativeEq :
      ∀ direction,
        gravityAuxiliaryDirectionalDerivative GlobalEC 0 direction =
          gravityAuxiliaryDirectionalDerivative LocalEC 0 direction := by
    intro direction
    unfold gravityAuxiliaryDirectionalDerivative fieldDirectionalDerivative
    rw [globalEC_gravityAuxiliary_eq_localEC]
  have jetEq :
      holonomicGravityAuxiliaryJet GlobalEC 0 =
        holonomicGravityAuxiliaryJet LocalEC 0 := by
    unfold holonomicGravityAuxiliaryJet
    exact congrArg₂ PointwisePhysicalBivectorJet.mk
      (congrFun globalEC_gravityAuxiliary_eq_localEC 0)
      (funext derivativeEq)
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
  rw [congrFun globalEC_gravityConnection_eq_localEC 0, jetEq]

private theorem globalEC_actionJet_origin_eq_localEC :
    generatedDiracDualFormNativePointwiseActionJet Source GlobalEC 0 =
      generatedDiracDualFormNativePointwiseActionJet Source LocalEC 0 := by
  have scalarCovariantEq :
      holonomicScalarCovariantDerivative GlobalEC =
        holonomicScalarCovariantDerivative LocalEC := by
    funext point direction
    unfold holonomicScalarCovariantDerivative
    rw [globalEC_scalar_eq_localEC, globalEC_gaugeConnection_eq_localEC]
  have matterCovariantEq :
      holonomicMatterCovariantDerivative GlobalEC =
        holonomicMatterCovariantDerivative LocalEC := by
    funext point direction
    unfold holonomicMatterCovariantDerivative
    rw [globalEC_matter_eq_localEC, globalEC_gravityConnection_eq_localEC,
      globalEC_gaugeConnection_eq_localEC]
  have curvatureEq :
      holonomicGravityCurvature GlobalEC 0 =
        holonomicGravityCurvature LocalEC 0 := by
    calc
      holonomicGravityCurvature GlobalEC 0 =
          diracDualFormNativeCoframeECContactCurvatureTarget
            Source GlobalP286 0 :=
        sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact
          Source GlobalP286 0
      _ = diracDualFormNativeCoframeECContactCurvatureTarget
            Source LocalP286 0 :=
        globalP286_ECTarget_origin_eq_localP286
      _ = holonomicGravityCurvature LocalEC 0 :=
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact
          Source LocalP286 0).symm
  have scalarMomentumEq
      (direction : ScalarCoordinateCarrier)
      (derivativeDirection : LorentzianIndex) :
      scalarDifferentialMomentum Source GlobalEC direction
          derivativeDirection =
        scalarDifferentialMomentum Source LocalEC direction
          derivativeDirection := by
    funext point
    unfold scalarDifferentialMomentum
      scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [globalEC_coframe_eq_localEC, scalarCovariantEq]
  have matterMomentumEq
      (direction : MatterCoordinateCarrier)
      (derivativeDirection : LorentzianIndex) :
      matterDifferentialMomentum Source GlobalEC direction
          derivativeDirection =
        matterDifferentialMomentum Source LocalEC direction
          derivativeDirection := by
    funext point
    unfold matterDifferentialMomentum matterDifferentialVariationVector
      generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [globalEC_coframe_eq_localEC, globalEC_conjugateMatter_eq_localEC]
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · exact congrFun globalEC_coframe_eq_localEC 0
    · exact curvatureEq
    · exact congrFun globalEC_gravityAuxiliary_eq_localEC 0
    · exact congrFun globalEC_multiplier_eq_localEC 0
    · exact holonomicGaugeCurvature_eq_of_connection_eq
        GlobalEC LocalEC globalEC_gaugeConnection_eq_localEC 0
    · exact globalEC_gaugeAuxiliary_origin_eq_localEC
    · exact congrFun globalEC_scalar_eq_localEC 0
    · exact congrFun scalarCovariantEq 0
    · exact congrFun globalEC_matter_eq_localEC 0
    · exact congrFun matterCovariantEq 0
    · exact congrFun globalEC_conjugateMatter_eq_localEC 0
  · exact congrFun globalEC_gravityConnection_eq_localEC 0
  · exact congrFun globalEC_gaugeConnection_eq_localEC 0
  · exact globalEC_gravityExteriorCovariant_origin_eq_localEC
  · exact globalEC_p286ExteriorCovariant_origin_eq_localEC
  · funext direction
    change scalarDifferentialMomentumDivergence Source GlobalEC direction 0 =
      scalarDifferentialMomentumDivergence Source LocalEC direction 0
    unfold scalarDifferentialMomentumDivergence
    simp_rw [scalarMomentumEq direction]
  · funext direction
    change matterDifferentialMomentumDivergence Source GlobalEC direction 0 =
      matterDifferentialMomentumDivergence Source LocalEC direction 0
    unfold matterDifferentialMomentumDivergence
    simp_rw [matterMomentumEq direction]

private theorem globalEC_residual_origin_eq_localEC :
    diracDualFormNativePointwiseJointResidual Source GlobalEC 0 =
      diracDualFormNativePointwiseJointResidual Source LocalEC 0 := by
  exact
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      Source GlobalEC LocalEC 0 0 globalEC_actionJet_origin_eq_localEC

private theorem localEC_jointResidual_origin_eq_matterRead :
    diracDualFormNativePointwiseJointResidual Source LocalEC 0 =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        matter :=
          (diracDualFormNativePointwiseJointResidual Source LocalEC 0).matter } := by
  have accepted := contact_jointResidual_origin_eq_matterRead (0 : BasePoint)
  change
    diracDualFormNativePointwiseJointResidual Source LocalEC 0 =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        matter :=
          (diracDualFormNativePointwiseJointResidual Source LocalEC 0).matter }
    at accepted
  exact accepted

private theorem globalEC_jointResidual_origin_eq_matterRead :
    diracDualFormNativePointwiseJointResidual Source GlobalEC 0 =
      { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
        matter :=
          (diracDualFormNativePointwiseJointResidual Source GlobalEC 0).matter } := by
  rw [globalEC_residual_origin_eq_localEC]
  exact localEC_jointResidual_origin_eq_matterRead

private theorem globalECLoweredConnectionFirstJet_normalForm
    (contact : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    cauchySafeJointGlobalECLoweredConnectionFirstJet Source GlobalP286
        contact derivativeDirection formDirection internalPair =
      ∑ spacetimePair : Fin 6,
        normalizedDerivativeBivector
            (GlobalP286.gravityConnection contact)
            (diracDualFormNativeCoframeECContactCurvatureTarget
              Source GlobalP286 contact)
            internalPair spacetimePair *
          orientedLorentzBivectorBasisCoefficient spacetimePair
            derivativeDirection formDirection := by
  unfold cauchySafeJointGlobalECLoweredConnectionFirstJet
    cauchySafeJointGlobalECProfileContact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
    diracDualFormNativeCoframeECContactConnectedActual
    diracDualFormNativeCoframeECContactPreparedActual
  change
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (coframeECContactCenteredNormalizedAffineConfiguration contact
            (GlobalP286.gravityConnection contact)
            (diracDualFormNativeCoframeECContactCurvatureTarget
              Source GlobalP286 contact))
          contact derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) = _
  rw [gravityConnectionDerivative_coframeECContactCentered_contact,
    normalizedAffineLorentzConnectionField_loweredDerivative_zero]
  exact normalizedAffineBivectorOneForm_directionalDerivative_zero
    (GlobalP286.gravityConnection contact)
    (diracDualFormNativeCoframeECContactCurvatureTarget
      Source GlobalP286 contact)
    derivativeDirection formDirection internalPair

private theorem globalP286_coframe_eq_current :
    GlobalP286.coframe = Current.coframe := by
  rfl

private theorem globalP286_gravityConnection_eq_current :
    GlobalP286.gravityConnection = Current.gravityConnection := by
  rfl

private theorem globalP286_gaugeConnection_eq_current :
    GlobalP286.gaugeConnection = Current.gaugeConnection := by
  rfl

private theorem globalP286_scalar_eq_globalConstitutive :
    GlobalP286.scalar = GlobalConstitutive.scalar := by
  rfl

private theorem globalP286_matter_eq_globalConstitutive :
    GlobalP286.matter = GlobalConstitutive.matter := by
  rfl

private theorem globalP286_conjugateMatter_eq_globalConstitutive :
    GlobalP286.conjugateMatter = GlobalConstitutive.conjugateMatter := by
  rfl

private theorem globalP286_coframe_contDiffAt_origin :
    ContDiffAt ℝ 1 GlobalP286.coframe 0 := by
  rw [globalP286_coframe_eq_current]
  exact current_coframe_contDiff.contDiffAt.of_le (by simp)

private theorem globalP286_connection_component_contDiffAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun point => GlobalP286.gravityConnection point formDirection
        internalOut internalIn) 0 := by
  rw [globalP286_gravityConnection_eq_current]
  exact (current_smooth.2.1 formDirection internalOut internalIn
    ).contDiffAt.of_le (by simp)

private theorem globalP286_gaugeConnectionCoordinate_contDiffAt_origin :
    ContDiffAt ℝ 0
      (holonomicP286GaugeConnectionCoordinate GlobalP286) 0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [globalP286_gaugeConnection_eq_current]
  exact current_gaugeConnectionCoordinate_contDiff.contDiffAt.of_le (by simp)

private theorem globalP286_auxiliaryCoordinate_contDiffAt_origin :
    ContDiffAt ℝ 0
      (holonomicP286GaugeAuxiliaryCoordinate GlobalP286) 0 := by
  rw [show holonomicP286GaugeAuxiliaryCoordinate GlobalP286 =
      cauchySafeJointGlobalP286CoordinateField Source GlobalConstitutive by
    funext point
    exact
      sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate
        Source GlobalConstitutive point]
  unfold cauchySafeJointGlobalP286CoordinateField
    cauchySafeJointGlobalP286RadialIncrement
  exact contDiffAt_const.add
    (radialCurveIntegral_contDiffAt_zero_of_contDiffAt
      (cauchySafeJointGlobalP286JetCLM Source GlobalConstitutive)
      globalP286JetCLM_contDiffAt_origin)

private theorem globalP286_gaugeCurvatureCoordinate_contDiffAt_origin :
    ContDiffAt ℝ 0 (holonomicP286GaugeCurvatureCoordinate GlobalP286) 0 := by
  rw [show holonomicP286GaugeCurvatureCoordinate GlobalP286 =
      holonomicP286GaugeCurvatureCoordinate Current by
    funext point pair
    unfold holonomicP286GaugeCurvatureCoordinate
    rw [holonomicGaugeCurvature_eq_of_connection_eq
      GlobalP286 Current globalP286_gaugeConnection_eq_current point]]
  exact current_gaugeCurvatureCoordinate_contDiff.contDiffAt.of_le (by simp)

private theorem globalP286_scalar_contDiffAt_origin :
    ContDiffAt ℝ 1 GlobalP286.scalar 0 := by
  rw [globalP286_scalar_eq_globalConstitutive]
  exact globalConstitutive_scalar_contDiffAt_origin

private theorem globalP286_scalarCovariant_contDiffAt_origin :
    ContDiffAt ℝ 0 (holonomicScalarCovariantDerivative GlobalP286) 0 := by
  rw [show holonomicScalarCovariantDerivative GlobalP286 =
      holonomicScalarCovariantDerivative GlobalConstitutive by
    funext point direction
    unfold holonomicScalarCovariantDerivative
    rfl]
  exact globalConstitutive_scalarCovariant_contDiffAt_origin

private theorem globalP286_matterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (GlobalP286.matter point)) 0 := by
  rw [globalP286_matter_eq_globalConstitutive]
  exact globalConstitutive_matterCoordinates_contDiffAt_origin

private theorem globalP286_conjugateMatterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1 (holonomicConjugateMatterCoordinates GlobalP286) 0 := by
  rw [show holonomicConjugateMatterCoordinates GlobalP286 =
      holonomicConjugateMatterCoordinates GlobalConstitutive by
    unfold holonomicConjugateMatterCoordinates
    rw [globalP286_conjugateMatter_eq_globalConstitutive]]
  exact globalConstitutive_conjugateMatterCoordinates_contDiffAt_origin

private theorem globalP286_matterCovariantCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative GlobalP286 point direction)) 0 := by
  apply contDiffAt_pi'
  intro direction
  have derivativeRegular : ContDiffAt ℝ 0 (fun point =>
      fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (GlobalP286.matter candidate))
        point direction) 0 := by
    unfold fieldDirectionalDerivative
    exact
      (globalP286_matterCoordinates_contDiffAt_origin.fderiv_right
        (m := 0) (by norm_num)).clm_apply contDiffAt_const
  have matterRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (GlobalP286.matter point)) 0 :=
    globalP286_matterCoordinates_contDiffAt_origin.of_le (by norm_num)
  have gaugeRegular : ContDiffAt ℝ 0 (fun point =>
      p286CoordinateEquiv (GlobalP286.gaugeConnection point direction)) 0 :=
    contDiffAt_pi.mp
      globalP286_gaugeConnectionCoordinate_contDiffAt_origin direction
  have spinMatrixRegular : ContDiffAt ℝ 0 (fun point =>
      diracSpinConnectionLift
        (GlobalP286.gravityConnection point) direction) 0 := by
    apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro pair _
    have realCoefficientRegular : ContDiffAt ℝ 0 (fun point =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          GlobalP286.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair)) 0 :=
      contDiffAt_const.mul
        ((globalP286_connection_component_contDiffAt_origin direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair)).of_le
            (by norm_num))
    have complexCoefficientRegular : ContDiffAt ℝ 0 (fun point =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          GlobalP286.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ)) 0 :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realCoefficientRegular
    exact (contDiffAt_const.mul complexCoefficientRegular).mul contDiffAt_const
  have spinActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (GlobalP286.gravityConnection point) direction)
          (GlobalP286.matter point))) 0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 spinMatrixRegular).clm_apply matterRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (GlobalP286.gravityConnection point) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (GlobalP286.matter point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (GlobalP286.gaugeConnection point direction))
          (GlobalP286.matter point))) 0 := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 gaugeRegular).clm_apply matterRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (GlobalP286.gaugeConnection point direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (GlobalP286.matter point))))) 0 at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicMatterCovariantDerivative
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact derivativeRegular.add spinActionRegular |>.add gaugeActionRegular

private theorem globalP286_gaugeActionParameter_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point => coframeGaugeActionParameterOfField
        (diracDualFormNativeCoframeECContactField GlobalP286 point)) 0 := by
  change ContDiffAt ℝ 0 (fun point =>
    (holonomicP286GaugeAuxiliaryCoordinate GlobalP286 point,
      holonomicP286GaugeCurvatureCoordinate GlobalP286 point)) 0
  exact globalP286_auxiliaryCoordinate_contDiffAt_origin.prodMk
    globalP286_gaugeCurvatureCoordinate_contDiffAt_origin

private theorem globalP286_matterActionParameter_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point => coframeMatterActionParameterOfField
        (diracDualFormNativeCoframeECContactField GlobalP286 point)) 0 := by
  change ContDiffAt ℝ 0 (fun point =>
    (GlobalP286.scalar point,
      holonomicScalarCovariantDerivative GlobalP286 point,
      matterCoordinateEquiv (GlobalP286.matter point),
      fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative GlobalP286 point direction),
      holonomicConjugateMatterCoordinates GlobalP286 point)) 0
  exact
    (globalP286_scalar_contDiffAt_origin.of_le (by norm_num)).prodMk
      (globalP286_scalarCovariant_contDiffAt_origin.prodMk
        ((globalP286_matterCoordinates_contDiffAt_origin.of_le
          (by norm_num)).prodMk
          (globalP286_matterCovariantCoordinates_contDiffAt_origin.prodMk
            (globalP286_conjugateMatterCoordinates_contDiffAt_origin.of_le
              (by norm_num)))))

private theorem globalP286_gravityCurvature_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point => holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual GlobalP286) point)
      0 := by
  rw [show (fun point => holonomicGravityCurvature
      (diracDualFormNativeCoframeECContactPreparedActual GlobalP286) point) =
      holonomicGravityCurvature Current by
    funext point internalPair spacetimePair
    unfold diracDualFormNativeCoframeECContactPreparedActual
      restrictHolonomicConfigurationToIIPlus holonomicGravityCurvature
      gravityConnectionDerivative
    rw [globalP286_gravityConnection_eq_current]]
  apply contDiffAt_pi'
  intro internalPair
  apply contDiffAt_pi'
  intro spacetimePair
  exact (holonomicGravityCurvature_component_contDiff
    Current current_smooth internalPair spacetimePair).contDiffAt.of_le
      (by simp)

private theorem globalP286_contactField_coframe_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point =>
        (diracDualFormNativeCoframeECContactField GlobalP286 point).coframe)
      0 := by
  change ContDiffAt ℝ 0 GlobalP286.coframe 0
  exact globalP286_coframe_contDiffAt_origin.of_le (by norm_num)

private theorem globalP286_contactField_nondegenerate_origin :
    Matrix.det
      (diracDualFormNativeCoframeECContactField GlobalP286 0).coframe ≠ 0 := by
  change Matrix.det (Current.coframe 0) ≠ 0
  exact current_nondegenerate 0

private theorem globalP286_coframeScale_ne_zero_origin :
    coframeTwoFormWedgeScale (GlobalP286.coframe 0).transpose ≠ 0 := by
  apply coframeTwoFormWedgeScale_ne_zero
  rw [Matrix.det_transpose, globalP286_coframe_eq_current]
  exact current_nondegenerate 0

private theorem globalP286_ECTarget_contDiffAt_origin :
    ContDiffAt ℝ 0
      (diracDualFormNativeCoframeECContactCurvatureTarget
        Source GlobalP286) 0 := by
  apply contDiffAt_pi'
  intro internalPair
  apply contDiffAt_pi'
  intro spacetimePair
  unfold diracDualFormNativeCoframeECContactCurvatureTarget
  apply coframeDiracDualECCurvatureTarget_component_contDiffAt
  · exact globalP286_coframe_contDiffAt_origin.of_le (by norm_num)
  · exact globalP286_gravityCurvature_contDiffAt_origin
  · intro row column
    unfold diracDualFormNativeCoframeECContactLoad
    simp only [neg_apply, add_apply]
    apply ContDiffAt.neg
    apply ContDiffAt.add
    · apply ContDiffAt.add
      · apply coframeDiracDualECCurvatureObservation_coordinate_contDiffAt
          GlobalP286.coframe
          (fun point => gravityInternalPairVarianceNormalization
            (coframeWedge (GlobalP286.coframe point)))
          0 (globalP286_coframe_contDiffAt_origin.of_le (by norm_num))
        apply contDiffAt_pi'
        intro targetInternalPair
        apply contDiffAt_pi'
        intro targetSpacetimePair
        simp only [gravityInternalPairVarianceNormalization_apply]
        unfold coframeWedge
        have componentRegular (internal coordinate : LorentzianIndex) :
            ContDiffAt ℝ 0
              (fun point => GlobalP286.coframe point internal coordinate) 0 :=
          contDiffAt_pi.mp
            (contDiffAt_pi.mp
              (globalP286_coframe_contDiffAt_origin.of_le (by norm_num))
              internal)
            coordinate
        exact contDiffAt_const.mul
          (((componentRegular (pairFirst targetInternalPair)
              (pairFirst targetSpacetimePair)).mul
            (componentRegular (pairSecond targetInternalPair)
              (pairSecond targetSpacetimePair))).sub
            ((componentRegular (pairFirst targetInternalPair)
              (pairSecond targetSpacetimePair)).mul
            (componentRegular (pairSecond targetInternalPair)
              (pairFirst targetSpacetimePair))))
      · apply diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt
        · exact globalP286_gaugeActionParameter_contDiffAt_origin
        · exact globalP286_contactField_coframe_contDiffAt_origin
        · exact globalP286_contactField_nondegenerate_origin
    · rw [show
        (fun point =>
          diracDualFormNativeCoframeMatterEulerCovector Source point
            (diracDualFormNativeCoframeECContactField GlobalP286 point)
            (coframeCoordinateDirection row column)) =
          fun point =>
            diracDualFormNativeCoframeMatterEulerCovector Source 0
              (diracDualFormNativeCoframeECContactField GlobalP286 point)
              (coframeCoordinateDirection row column) by
        funext point
        rw [diracDualFormNativeCoframeMatterEulerCovector_point_independent
          Source point
          (diracDualFormNativeCoframeECContactField GlobalP286 point)]]
      exact diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt
        Source 0
        (fun point => diracDualFormNativeCoframeECContactField GlobalP286 point)
        0 globalP286_matterActionParameter_contDiffAt_origin
        globalP286_contactField_coframe_contDiffAt_origin
        globalP286_contactField_nondegenerate_origin row column
  · exact globalP286_coframeScale_ne_zero_origin

private theorem globalP286_normalizedDerivative_component_contDiffAt_origin
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ 0
      (fun contact =>
        normalizedDerivativeBivector
          (GlobalP286.gravityConnection contact)
          (diracDualFormNativeCoframeECContactCurvatureTarget
            Source GlobalP286 contact)
          internalPair spacetimePair) 0 := by
  unfold normalizedDerivativeBivector originLorentzBracketCurvature
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine contDiffAt_const.mul
    (((contDiffAt_pi.mp
        (contDiffAt_pi.mp globalP286_ECTarget_contDiffAt_origin internalPair)
        spacetimePair).sub
      (contDiffAt_const.mul ?_)))
  apply ContDiffAt.sum
  intro middle _
  exact
    (((globalP286_connection_component_contDiffAt_origin
        (pairFirst spacetimePair) (pairFirst internalPair) middle).of_le
      (by norm_num)).mul
      ((globalP286_connection_component_contDiffAt_origin
        (pairSecond spacetimePair) middle (pairSecond internalPair)).of_le
      (by norm_num))).sub
    (((globalP286_connection_component_contDiffAt_origin
        (pairSecond spacetimePair) (pairFirst internalPair) middle).of_le
      (by norm_num)).mul
      ((globalP286_connection_component_contDiffAt_origin
        (pairFirst spacetimePair) middle (pairSecond internalPair)).of_le
      (by norm_num)))

private theorem globalECLoweredConnectionFirstJet_contDiffAt_origin
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    ContDiffAt ℝ 0
      (fun contact =>
        cauchySafeJointGlobalECLoweredConnectionFirstJet
          Source GlobalP286 contact derivativeDirection formDirection
          internalPair) 0 := by
  rw [show
    (fun contact =>
      cauchySafeJointGlobalECLoweredConnectionFirstJet
        Source GlobalP286 contact derivativeDirection formDirection
        internalPair) =
      fun contact =>
        ∑ spacetimePair : Fin 6,
          normalizedDerivativeBivector
              (GlobalP286.gravityConnection contact)
              (diracDualFormNativeCoframeECContactCurvatureTarget
                Source GlobalP286 contact)
              internalPair spacetimePair *
            orientedLorentzBivectorBasisCoefficient spacetimePair
              derivativeDirection formDirection by
    funext contact
    exact globalECLoweredConnectionFirstJet_normalForm contact
      derivativeDirection formDirection internalPair]
  apply ContDiffAt.sum
  intro spacetimePair _
  exact
    (globalP286_normalizedDerivative_component_contDiffAt_origin
      internalPair spacetimePair).mul contDiffAt_const

@[fun_prop] private theorem globalECJetOneForm_contDiffAt_origin
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun contact =>
        cauchySafeJointGlobalECJetOneForm Source GlobalP286 contact
          derivativeDirection) 0 := by
  apply contDiffAt_pi'
  intro formDirection
  apply contDiffAt_pi'
  intro internalPair
  exact globalECLoweredConnectionFirstJet_contDiffAt_origin
    derivativeDirection formDirection internalPair

private theorem globalECJetCLM_contDiffAt_origin :
    ContDiffAt ℝ 0
      (cauchySafeJointGlobalECJetCLM Source GlobalP286) 0 := by
  unfold cauchySafeJointGlobalECJetCLM
  apply ContDiffAt.sum
  intro derivativeDirection _
  fun_prop

private theorem globalECPath_connection_origin_eq_globalEC :
    GlobalECPath.gravityConnection 0 = GlobalEC.gravityConnection 0 := by
  change
    cauchySafeJointGlobalECConnectionField Source GlobalP286 0 =
      (cauchySafeJointGlobalECProfileContact Source GlobalP286 0
        ).gravityConnection 0
  rw [cauchySafeJointGlobalECConnectionField_zero,
    cauchySafeJointGlobalECProfileContact_connection_contact]

private theorem globalECPath_loweredDerivative_eq_globalEC
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative GlobalECPath 0 derivativeDirection
          formDirection (pairFirst internalPair) (pairSecond internalPair) =
      minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative GlobalEC 0 derivativeDirection
          formDirection (pairFirst internalPair) (pairSecond internalPair) := by
  change
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite
            Source GlobalP286)
          0 derivativeDirection formDirection (pairFirst internalPair)
          (pairSecond internalPair) =
      cauchySafeJointGlobalECLoweredConnectionFirstJet Source GlobalP286 0
        derivativeDirection formDirection internalPair
  exact
    sourceActionGeneratedDiracDualCauchySafeGlobalECPathWrite_loweredConnectionFirstJet_eq_profile
      Source GlobalP286 globalECJetCLM_contDiffAt_origin derivativeDirection
      formDirection internalPair

/-- The emitted global EC-path leg realizes, at the canonical origin, the
same source/current/contact-owned normalized connection first jet as its
local profile.  The right-hand side exposes the generated curvature target
in the exact finite coordinate form consumed by changed-read calculations. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECPath_loweredConnectionFirstJet_origin_normalForm
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative GlobalECPath 0 derivativeDirection
          formDirection (pairFirst internalPair) (pairSecond internalPair) =
      ∑ spacetimePair : Fin 6,
        normalizedDerivativeBivector
            (GlobalP286.gravityConnection 0)
            (diracDualFormNativeCoframeECContactCurvatureTarget
              Source GlobalP286 0)
            internalPair spacetimePair *
          orientedLorentzBivectorBasisCoefficient spacetimePair
            derivativeDirection formDirection := by
  rw [globalECPath_loweredDerivative_eq_globalEC]
  exact globalECLoweredConnectionFirstJet_normalForm 0 derivativeDirection
    formDirection internalPair

private theorem globalECPath_curvature_origin_eq_globalEC :
    holonomicGravityCurvature GlobalECPath 0 =
      holonomicGravityCurvature GlobalEC 0 := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  rw [mul_add, mul_sub,
    globalECPath_loweredDerivative_eq_globalEC
      (pairFirst spacetimePair) (pairSecond spacetimePair) internalPair,
    globalECPath_loweredDerivative_eq_globalEC
      (pairSecond spacetimePair) (pairFirst spacetimePair) internalPair,
    globalECPath_connection_origin_eq_globalEC]
  ring

private theorem globalECPath_radialIncrement_contDiffAt_origin :
    ContDiffAt ℝ 0
      (cauchySafeJointGlobalECRadialIncrement Source GlobalP286) 0 :=
  radialCurveIntegral_contDiffAt_zero_of_contDiffAt
    (cauchySafeJointGlobalECJetCLM Source GlobalP286)
    globalECJetCLM_contDiffAt_origin

private theorem globalECPath_connection_component_contDiffAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun point => GlobalECPath.gravityConnection point formDirection
        internalOut internalIn) 0 := by
  change ContDiffAt ℝ 0 (fun point =>
    radialLorentzConnectionCoordinateCLM formDirection internalOut internalIn
      (GlobalP286.gravityConnection 0 +
        radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement
            Source GlobalP286 point))) 0
  exact
    (radialLorentzConnectionCoordinateCLM formDirection internalOut internalIn
      ).contDiff.contDiffAt.comp 0
      (contDiffAt_const.add
        (radialLorentzConnectionLiftCLM.contDiff.contDiffAt.comp 0
          globalECPath_radialIncrement_contDiffAt_origin))

private theorem globalECPath_coframe_eq_globalP286 :
    GlobalECPath.coframe = GlobalP286.coframe := by
  rfl

private theorem globalECPath_gaugeConnection_eq_globalP286 :
    GlobalECPath.gaugeConnection = GlobalP286.gaugeConnection := by
  rfl

private theorem globalECPath_scalar_eq_globalP286 :
    GlobalECPath.scalar = GlobalP286.scalar := by
  rfl

private theorem globalECPath_matter_eq_globalP286 :
    GlobalECPath.matter = GlobalP286.matter := by
  rfl

private theorem globalECPath_conjugateMatter_eq_globalP286 :
    GlobalECPath.conjugateMatter = GlobalP286.conjugateMatter := by
  rfl

private theorem globalECPath_coframe_contDiffAt_origin :
    ContDiffAt ℝ 1 GlobalECPath.coframe 0 := by
  rw [globalECPath_coframe_eq_globalP286]
  exact globalP286_coframe_contDiffAt_origin

private theorem globalECPath_gaugeCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point direction =>
        p286CoordinateEquiv (GlobalECPath.gaugeConnection point direction)) 0 := by
  rw [globalECPath_gaugeConnection_eq_globalP286]
  exact globalP286_gaugeConnectionCoordinate_contDiffAt_origin

private theorem globalECPath_scalar_contDiffAt_origin :
    ContDiffAt ℝ 0 GlobalECPath.scalar 0 := by
  rw [globalECPath_scalar_eq_globalP286]
  exact globalP286_scalar_contDiffAt_origin.of_le (by norm_num)

private theorem globalECPath_matterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (GlobalECPath.matter point)) 0 := by
  rw [globalECPath_matter_eq_globalP286]
  exact globalP286_matterCoordinates_contDiffAt_origin

private theorem globalECPath_conjugateMatterCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (holonomicConjugateMatterCoordinates GlobalECPath) 0 := by
  rw [show holonomicConjugateMatterCoordinates GlobalECPath =
      holonomicConjugateMatterCoordinates GlobalP286 by
    unfold holonomicConjugateMatterCoordinates
    rw [globalECPath_conjugateMatter_eq_globalP286]]
  exact globalP286_conjugateMatterCoordinates_contDiffAt_origin

private theorem globalECPath_matterCovariantCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative GlobalECPath point direction)) 0 := by
  apply contDiffAt_pi'
  intro direction
  have derivativeRegular : ContDiffAt ℝ 0 (fun point =>
      fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv (GlobalECPath.matter candidate))
        point direction) 0 := by
    unfold fieldDirectionalDerivative
    exact
      (globalECPath_matterCoordinates_contDiffAt_origin.fderiv_right
        (m := 0) (by norm_num)).clm_apply contDiffAt_const
  have matterRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (GlobalECPath.matter point)) 0 :=
    globalECPath_matterCoordinates_contDiffAt_origin.of_le (by norm_num)
  have gaugeRegular : ContDiffAt ℝ 0 (fun point =>
      p286CoordinateEquiv (GlobalECPath.gaugeConnection point direction)) 0 :=
    contDiffAt_pi.mp globalECPath_gaugeCoordinates_contDiffAt_origin direction
  have spinMatrixRegular : ContDiffAt ℝ 0 (fun point =>
      diracSpinConnectionLift
        (GlobalECPath.gravityConnection point) direction) 0 := by
    apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro pair _
    have realCoefficientRegular : ContDiffAt ℝ 0 (fun point =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          GlobalECPath.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair)) 0 :=
      contDiffAt_const.mul
        (globalECPath_connection_component_contDiffAt_origin direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair))
    have complexCoefficientRegular : ContDiffAt ℝ 0 (fun point =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          GlobalECPath.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ)) 0 :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realCoefficientRegular
    exact (contDiffAt_const.mul complexCoefficientRegular).mul contDiffAt_const
  have spinActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (GlobalECPath.gravityConnection point) direction)
          (GlobalECPath.matter point))) 0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 spinMatrixRegular).clm_apply matterRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (GlobalECPath.gravityConnection point) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (GlobalECPath.matter point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (GlobalECPath.gaugeConnection point direction))
          (GlobalECPath.matter point))) 0 := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 gaugeRegular).clm_apply matterRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (GlobalECPath.gaugeConnection point direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (GlobalECPath.matter point))))) 0 at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicMatterCovariantDerivative
  simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
  exact derivativeRegular.add spinActionRegular |>.add gaugeActionRegular

private theorem globalECPath_nondegenerate_origin :
    Matrix.det (GlobalECPath.coframe 0) ≠ 0 := by
  rw [globalECPath_coframe_eq_globalP286, globalP286_coframe_eq_current]
  exact current_nondegenerate 0

private theorem globalECPath_coframeInverse_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun point => (GlobalECPath.coframe point)⁻¹) 0 := by
  exact
    (coframe_inv_contDiffAt (GlobalECPath.coframe 0)
      globalECPath_nondegenerate_origin).of_le (by norm_num) |>.comp 0
      (globalECPath_coframe_contDiffAt_origin.of_le (by norm_num))

private theorem globalECPath_frameMatterDerivative_contDiffAt_origin
    (internal : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (frameMatterDerivative (GlobalECPath.coframe point)
        (holonomicMatterCovariantDerivative GlobalECPath point) internal)) 0 := by
  unfold frameMatterDerivative
  simp only [map_sum, map_smul]
  apply ContDiffAt.sum
  intro coordinate _
  have inverseEntryRegular : ContDiffAt ℝ 0 (fun point =>
      (GlobalECPath.coframe point)⁻¹ coordinate internal) 0 :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp globalECPath_coframeInverse_contDiffAt_origin
        coordinate) internal
  have inverseComplexRegular : ContDiffAt ℝ 0 (fun point =>
      ((GlobalECPath.coframe point)⁻¹ coordinate internal : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 inverseEntryRegular
  exact inverseComplexRegular.smul
    (contDiffAt_pi.mp globalECPath_matterCovariantCoordinates_contDiffAt_origin
      coordinate)

private theorem globalECPath_frameTimeKnownVector_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (frameTimeMatterKnownVector (GlobalECPath.coframe point)
        (holonomicMatterCovariantDerivative GlobalECPath point)
        (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
        (GlobalECPath.matter point))) 0 := by
  have kineticDirectionRegular : ∀ spatial : Fin 3,
      ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma spatial.succ)
          (frameMatterDerivative (GlobalECPath.coframe point)
            (holonomicMatterCovariantDerivative GlobalECPath point)
            spatial.succ))) 0 := by
    intro spatial
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0
          (contDiffAt_const : ContDiffAt ℝ 0
            (fun _ : BasePoint => diracGamma spatial.succ) 0)).clm_apply
        (globalECPath_frameMatterDerivative_contDiffAt_origin spatial.succ)
    change ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (diracMatrixMatterAction (diracGamma spatial.succ)
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv
            (frameMatterDerivative (GlobalECPath.coframe point)
              (holonomicMatterCovariantDerivative GlobalECPath point)
              spatial.succ))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumRegular : ContDiffAt ℝ 0 (fun point =>
      ∑ spatial : Fin 3, matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma spatial.succ)
          (frameMatterDerivative (GlobalECPath.coframe point)
            (holonomicMatterCovariantDerivative GlobalECPath point)
            spatial.succ))) 0 :=
    ContDiffAt.sum fun spatial _ => kineticDirectionRegular spatial
  have kineticRegular : ContDiffAt ℝ 0 (fun point =>
      Complex.I • ∑ spatial : Fin 3, matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma spatial.succ)
          (frameMatterDerivative (GlobalECPath.coframe point)
            (holonomicMatterCovariantDerivative GlobalECPath point)
            spatial.succ))) 0 :=
    (contDiffAt_const : ContDiffAt ℝ 0
      (fun _ : BasePoint => (Complex.I : ℂ)) 0).smul kineticSumRegular
  have matterRegular :=
    globalECPath_matterCoordinates_contDiffAt_origin.of_le
      (by norm_num : (0 : WithTop ℕ∞) ≤ 1)
  have yukawaRegular : ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
        (GlobalECPath.matter point))) 0 := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 globalECPath_scalar_contDiffAt_origin).clm_apply
          matterRegular
    change ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv (GlobalECPath.matter point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold frameTimeMatterKnownVector
  simp only [map_add, map_smul, map_sum]
  exact kineticRegular.add yukawaRegular

private theorem globalECPath_generatedFrameTimeDerivative_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (globalFrameTimeMatterGeneratedDerivativeAt GlobalECPath point)) 0 := by
  have gammaActionRegular : ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (diracMatrixMatterAction (diracGamma 0)
        (frameTimeMatterKnownVector (GlobalECPath.coframe point)
          (holonomicMatterCovariantDerivative GlobalECPath point)
          (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
          (GlobalECPath.matter point)))) 0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
      |>.contDiffAt.comp 0
        (contDiffAt_const : ContDiffAt ℝ 0
          (fun _ : BasePoint => diracGamma 0) 0)).clm_apply
        globalECPath_frameTimeKnownVector_contDiffAt_origin
    change ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (diracMatrixMatterAction (diracGamma 0)
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv
            (frameTimeMatterKnownVector (GlobalECPath.coframe point)
              (holonomicMatterCovariantDerivative GlobalECPath point)
              (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
              (GlobalECPath.matter point)))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold globalFrameTimeMatterGeneratedDerivativeAt
    actionGeneratedFrameTimeMatterDerivative identityCoframeMatterTimePrincipal
  simp only [map_neg, map_smul]
  exact ((contDiffAt_const : ContDiffAt ℝ 0
    (fun _ : BasePoint => (Complex.I : ℂ)) 0).smul gammaActionRegular).neg

private theorem globalECPath_frameTimeResponseCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun point => matterCoordinateEquiv
      (globalFrameTimeMatterResponseAt GlobalECPath point)) 0 := by
  unfold globalFrameTimeMatterResponseAt
  simp only [map_sub]
  exact globalECPath_generatedFrameTimeDerivative_contDiffAt_origin.sub
    (globalECPath_frameMatterDerivative_contDiffAt_origin 0)

private theorem globalECPath_matterResponseOneForm_contDiffAt_origin :
    ContDiffAt ℝ 0
      (coframeNativeGlobalMatterResponseOneForm GlobalECPath) 0 := by
  unfold coframeNativeGlobalMatterResponseOneForm
  apply ContDiffAt.smulRight
  · unfold coframeRowLinearFunctional
    apply ContDiffAt.sum
    intro coordinate _
    exact
      ((contDiffAt_pi.mp
          (contDiffAt_pi.mp
            (globalECPath_coframe_contDiffAt_origin.of_le (by norm_num)) 0)
          coordinate).smul contDiffAt_const)
  · exact globalECPath_frameTimeResponseCoordinates_contDiffAt_origin

private theorem globalEC_nondegenerate_origin :
    Matrix.det (GlobalEC.coframe 0) ≠ 0 := by
  change Matrix.det (GlobalP286.coframe 0) ≠ 0
  rw [globalP286_coframe_eq_current]
  exact current_nondegenerate 0

private theorem globalEC_generatedMatterVector_origin_zero :
    generatedContinuumDiracDualMatterVector Source 0 0
        (toContinuumPointField GlobalEC 0) = 0 := by
  apply generatedContinuumDiracDualMatterVector_eq_zero_of_conjugateCoefficients
  · exact globalEC_nondegenerate_origin
  · have projected := congrArg
      DiracDualFormNativePointwiseJointResidualCarrier.conjugateMatter
      globalEC_jointResidual_origin_eq_matterRead
    simpa [diracDualFormNativePointwiseJointResidual] using projected

private theorem globalEC_frameTimeMatterActionLaw_origin :
    FrameTimeMatterActionLaw (GlobalEC.coframe 0)
      (holonomicMatterCovariantDerivative GlobalEC 0)
      (scalarCoordinateEquiv.symm (GlobalEC.scalar 0))
      (GlobalEC.matter 0)
      (frameMatterDerivative (GlobalEC.coframe 0)
        (holonomicMatterCovariantDerivative GlobalEC 0) 0) :=
  (frameTimeMatterActionLaw_iff_generatedContinuumDiracDualMatterVector_zero
    Source GlobalEC 0).2 globalEC_generatedMatterVector_origin_zero

private theorem globalECPath_coframe_origin_eq_globalEC :
    GlobalECPath.coframe 0 = GlobalEC.coframe 0 := by
  rfl

private theorem globalECPath_scalar_origin_eq_globalEC :
    GlobalECPath.scalar 0 = GlobalEC.scalar 0 := by
  rfl

private theorem globalECPath_matter_origin_eq_globalEC :
    GlobalECPath.matter 0 = GlobalEC.matter 0 := by
  rfl

private theorem globalECPath_matterCovariantDerivative_origin_eq_globalEC :
    holonomicMatterCovariantDerivative GlobalECPath 0 =
      holonomicMatterCovariantDerivative GlobalEC 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [globalECPath_connection_origin_eq_globalEC]
  rfl

private theorem globalECPath_frameTimeMatterActionLaw_origin :
    FrameTimeMatterActionLaw (GlobalECPath.coframe 0)
      (holonomicMatterCovariantDerivative GlobalECPath 0)
      (scalarCoordinateEquiv.symm (GlobalECPath.scalar 0))
      (GlobalECPath.matter 0)
      (frameMatterDerivative (GlobalECPath.coframe 0)
        (holonomicMatterCovariantDerivative GlobalECPath 0) 0) := by
  simpa only [globalECPath_coframe_origin_eq_globalEC,
    globalECPath_matterCovariantDerivative_origin_eq_globalEC,
    globalECPath_scalar_origin_eq_globalEC,
    globalECPath_matter_origin_eq_globalEC] using
      globalEC_frameTimeMatterActionLaw_origin

private theorem globalECPath_originFrameTimeMatterResponse_zero :
    originFrameTimeMatterResponse GlobalECPath = 0 := by
  have generatedEq := originFrameTimeMatterActionLaw_unique GlobalECPath
    (originFrameTimeMatterGeneratedDerivative GlobalECPath)
    (frameMatterDerivative (GlobalECPath.coframe 0)
      (holonomicMatterCovariantDerivative GlobalECPath 0) 0)
    (originFrameTimeMatterGeneratedDerivative_satisfies_actionLaw GlobalECPath)
    globalECPath_frameTimeMatterActionLaw_origin
  unfold originFrameTimeMatterResponse
  rw [generatedEq]
  simp

private theorem globalPrimal_matterCoordinateDerivative_origin_eq_globalECPath
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (GlobalPrimal.matter point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (GlobalECPath.matter point))
        0 direction := by
  rw [actionGeneratedGlobalFrameTimeMatterActual_coordinateDerivative_origin
    GlobalECPath
    (globalECPath_matterCoordinates_contDiffAt_origin.differentiableAt
      (by norm_num))
    globalECPath_matterResponseOneForm_contDiffAt_origin direction,
    globalECPath_originFrameTimeMatterResponse_zero]
  simp

private theorem globalECPath_coframe_contDiffAt_two :
    ContDiffAt ℝ 2 GlobalECPath.coframe 0 := by
  rw [globalECPath_coframe_eq_globalP286, globalP286_coframe_eq_current]
  exact current_coframe_contDiff.contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top)

private def GlobalDriftRestart : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    Source GlobalConstitutive

private theorem globalConstitutive_coframe_contDiffAt_two :
    ContDiffAt ℝ 2 GlobalConstitutive.coframe 0 := by
  rw [globalConstitutive_coframe_eq_current]
  exact current_coframe_contDiff.contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top)

private theorem globalDriftRestart_principalDrift_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun point =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          GlobalDriftRestart point direction) 0 := by
  exact restart_liveCoframeDensitizedPrincipalDrift_contDiffAt_of_local
    Source GlobalConstitutive 0 (globalConstitutive_nondegenerate 0)
    globalConstitutive_coframe_contDiffAt_two
    globalConstitutive_conjugateMatterCoordinates_contDiffAt_origin direction

private theorem globalECPath_coframe_eq_globalDriftRestart :
    GlobalECPath.coframe = GlobalDriftRestart.coframe := by
  rfl

private theorem globalECPath_conjugateMatter_eq_globalDriftRestart :
    GlobalECPath.conjugateMatter = GlobalDriftRestart.conjugateMatter := by
  rfl

private theorem principalDrift_eq_of_coframe_conjugateMatter
    (left right : StageNineHolonomicConfiguration)
    (coframeEq : left.coframe = right.coframe)
    (conjugateMatterEq : left.conjugateMatter = right.conjugateMatter)
    (direction : LorentzianIndex) :
    (fun point =>
      holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
        left point direction) =
      fun point =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          right point direction := by
  funext point
  unfold holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm holonomicConjugateMatterCoordinates
  rw [coframeEq, conjugateMatterEq]

private theorem globalECPath_principalDrift_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0
      (fun point =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          GlobalECPath point direction) 0 := by
  apply (congrArg (fun field => ContDiffAt ℝ 0 field 0)
    (principalDrift_eq_of_coframe_conjugateMatter GlobalECPath
      GlobalDriftRestart globalECPath_coframe_eq_globalDriftRestart
      globalECPath_conjugateMatter_eq_globalDriftRestart direction)).symm.mp
  exact globalDriftRestart_principalDrift_contDiffAt_origin direction

private theorem globalECPath_spatialPrincipalDrift_contDiffAt_origin :
    ContDiffAt ℝ 0
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates GlobalECPath) 0 := by
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  exact ContDiffAt.sum fun direction _ =>
    globalECPath_principalDrift_contDiffAt_origin direction.succ

private theorem globalECPath_temporalPrincipalDrift_contDiffAt_origin :
    ContDiffAt ℝ 0
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates GlobalECPath) 0 := by
  change ContDiffAt ℝ 0
    (fun point =>
      holonomicLiveCoframeDensitizedPrincipalDriftCoordinates GlobalECPath
        point canonicalLorentzianTimeDirection) 0
  exact globalECPath_principalDrift_contDiffAt_origin
    canonicalLorentzianTimeDirection

private theorem globalECPath_volumeComplex_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point =>
        ((generatedVolumeDensity
          (toContinuumPointField GlobalECPath point) : ℝ) : ℂ)) 0 := by
  have volumeReal : ContDiffAt ℝ 0
      (fun point =>
        generatedVolumeDensity (toContinuumPointField GlobalECPath point)) 0 := by
    change ContDiffAt ℝ 0
      (fun point => abs (Matrix.det (GlobalECPath.coframe point))) 0
    exact
      (StageNineCoframeVariation.coframe_volume_contDiffAt
        (GlobalECPath.coframe 0) globalECPath_nondegenerate_origin).of_le
          (by norm_num) |>.comp 0
            (globalECPath_coframe_contDiffAt_two.of_le (by norm_num))
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 volumeReal

private theorem globalECPath_inverseVolumeComplex_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point =>
        (((generatedVolumeDensity
          (toContinuumPointField GlobalECPath point) : ℝ) : ℂ)⁻¹)) 0 := by
  exact globalECPath_volumeComplex_contDiffAt_origin.inv (by
    have realNe :
        generatedVolumeDensity (toContinuumPointField GlobalECPath 0) ≠ 0 := by
      change abs (Matrix.det (GlobalECPath.coframe 0)) ≠ 0
      exact abs_ne_zero.mpr globalECPath_nondegenerate_origin
    exact_mod_cast realNe)

private theorem globalECPath_spinLift_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun point =>
      diracSpinConnectionLift
        (GlobalECPath.gravityConnection point) direction) 0 := by
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro pair _
  have realRegular : ContDiffAt ℝ 0 (fun point =>
      minkowskiInternalSign (lorentzBivectorFirst pair) *
        GlobalECPath.gravityConnection point direction
          (lorentzBivectorFirst pair) (lorentzBivectorSecond pair)) 0 :=
    contDiffAt_const.mul
      (globalECPath_connection_component_contDiffAt_origin direction
        (lorentzBivectorFirst pair) (lorentzBivectorSecond pair))
  have complexRegular : ContDiffAt ℝ 0 (fun point =>
      ((minkowskiInternalSign (lorentzBivectorFirst pair) *
        GlobalECPath.gravityConnection point direction
          (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realRegular
  exact (contDiffAt_const.mul complexRegular).mul contDiffAt_const

private theorem matterCoordinateDualPairing_contDiffAt_origin
    {coordinates : BasePoint → MatterCoordinateCarrier}
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (coordinatesRegular : ContDiffAt ℝ 0 coordinates 0)
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0 (fun point =>
      matterDualOfCoordinates (coordinates point) (vector point)) 0 := by
  rw [show
    (fun point =>
      matterDualOfCoordinates (coordinates point) (vector point)) =
    fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          coordinates point index by
    funext point
    exact matterDualOfCoordinates_apply _ _]
  apply ContDiffAt.sum
  intro index _
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  exact
    ((projection.restrictScalars ℝ).contDiff.contDiffAt.comp
      0 vectorRegular).mul
    ((projection.restrictScalars ℝ).contDiff.contDiffAt.comp
      0 coordinatesRegular)

private theorem globalECPath_conjugateApply_contDiffAt_origin
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0
      (fun point => GlobalECPath.conjugateMatter point (vector point)) 0 := by
  rw [show
    (fun point => GlobalECPath.conjugateMatter point (vector point)) =
    fun point =>
      matterDualOfCoordinates
        (holonomicConjugateMatterCoordinates GlobalECPath point)
        (vector point) by
    funext point
    exact congrArg
      (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier =>
        dual (vector point))
      (matterDualOfCoordinates_surjective
        (GlobalECPath.conjugateMatter point)).symm]
  exact matterCoordinateDualPairing_contDiffAt_origin
    (globalECPath_conjugateMatterCoordinates_contDiffAt_origin.of_le
      (by norm_num)) vectorRegular

private theorem globalECPath_livePrincipal_coordinate_contDiffAt_origin
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        ((liveCoframeMatterPrincipal (GlobalECPath.coframe point) direction)
          (vector point))) 0 := by
  have gammaRegular : ContDiffAt ℝ 0 (fun point =>
      inverseCoframeDiracGamma
        { coframe := GlobalECPath.coframe point, derivative := 0 }
        direction) 0 :=
    (inverseCoframeDiracGamma_contDiffAt
      (GlobalECPath.coframe 0) globalECPath_nondegenerate_origin
      direction).of_le (by norm_num) |>.comp 0
        (globalECPath_coframe_contDiffAt_two.of_le (by norm_num))
  have actual :=
    (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
      |>.contDiffAt.comp 0 gammaRegular).clm_apply vectorRegular
  have gammaActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := GlobalECPath.coframe point, derivative := 0 }
            direction)
          (vector point))) 0 := by
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := GlobalECPath.coframe point, derivative := 0 }
            direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold liveCoframeMatterPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    (contDiffAt_const :
      ContDiffAt ℝ 0 (fun _ : BasePoint => (Complex.I : ℂ)) 0).smul
        gammaActionRegular

private theorem globalECPath_connectionOperator_coordinate_contDiffAt_origin
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        ((holonomicIdentityCoframeMatterConnectionOperator
          GlobalECPath point direction) (vector point))) 0 := by
  have spinActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (GlobalECPath.gravityConnection point) direction)
          (vector point))) 0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0
          (globalECPath_spinLift_contDiffAt_origin direction)).clm_apply
            vectorRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (GlobalECPath.gravityConnection point) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeActionRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed (GlobalECPath.gaugeConnection point direction))
          (vector point))) 0 := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0
          (contDiffAt_pi.mp globalECPath_gaugeCoordinates_contDiffAt_origin
            direction)).clm_apply vectorRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (GlobalECPath.gaugeConnection point direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector point))))) 0 at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterConnectionOperator
  simp only [LinearMap.add_apply, map_add]
  exact spinActionRegular.add gaugeActionRegular

private theorem globalECPath_algebraicOperator_coordinate_contDiffAt_origin
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
          GlobalECPath point) (vector point))) 0 := by
  have directionRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun point =>
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
              (GlobalECPath.coframe point) direction)
            ((holonomicIdentityCoframeMatterConnectionOperator
              GlobalECPath point direction) (vector point)))) 0 := by
    intro direction
    exact globalECPath_livePrincipal_coordinate_contDiffAt_origin direction
      (globalECPath_connectionOperator_coordinate_contDiffAt_origin direction
        vectorRegular)
  have sumRegular : ContDiffAt ℝ 0 (fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
              (GlobalECPath.coframe point) direction)
            ((holonomicIdentityCoframeMatterConnectionOperator
              GlobalECPath point direction) (vector point)))) 0 :=
    ContDiffAt.sum fun direction _ => directionRegular direction
  have yukawaRegular : ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
          (vector point))) 0 := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 globalECPath_scalar_contDiffAt_origin).clm_apply
          vectorRegular
    change ContDiffAt ℝ 0 (fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (GlobalECPath.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (vector point))))) 0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_add, map_sum]
  exact sumRegular.add yukawaRegular

private theorem globalECPath_algebraicDual_apply_contDiffAt_origin
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0 (fun point =>
      holonomicDiracDualLiveCoframeAlgebraicDual GlobalECPath point
        (vector point)) 0 := by
  unfold holonomicDiracDualLiveCoframeAlgebraicDual
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  exact globalECPath_volumeComplex_contDiffAt_origin.smul
    (globalECPath_conjugateApply_contDiffAt_origin
      (globalECPath_algebraicOperator_coordinate_contDiffAt_origin
        vectorRegular))

private theorem globalECPath_conjugateDerivativeCoordinates_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun point =>
      holonomicConjugateMatterDerivativeCoordinates GlobalECPath point
        direction) 0 := by
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  exact
    (globalECPath_conjugateMatterCoordinates_contDiffAt_origin.fderiv_right
      (m := 0) (by norm_num)).clm_apply contDiffAt_const

private theorem globalECPath_frameConjugateDerivative_basis_contDiffAt_origin
    (internal : LorentzianIndex)
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ 0 (fun point =>
      (holonomicFrameConjugateMatterDerivative GlobalECPath point internal)
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) 0 := by
  unfold holonomicFrameConjugateMatterDerivative
    frameConjugateMatterDerivative
    holonomicConjugateMatterDerivativeDual
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    matterDualOfCoordinates_basis_apply]
  apply ContDiffAt.sum
  intro coordinate _
  have inverseEntryRegular : ContDiffAt ℝ 0 (fun point =>
      (GlobalECPath.coframe point)⁻¹ coordinate internal) 0 :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp globalECPath_coframeInverse_contDiffAt_origin
        coordinate) internal
  have inverseComplexRegular : ContDiffAt ℝ 0 (fun point =>
      ((GlobalECPath.coframe point)⁻¹ coordinate internal : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 inverseEntryRegular
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have derivativeCoordinateRegular : ContDiffAt ℝ 0 (fun point =>
      holonomicConjugateMatterDerivativeCoordinates GlobalECPath point
        coordinate index) 0 :=
    (projection.restrictScalars ℝ).contDiff.contDiffAt.comp 0
      (globalECPath_conjugateDerivativeCoordinates_contDiffAt_origin
        coordinate)
  exact inverseComplexRegular.smul derivativeCoordinateRegular

private theorem globalECPath_frameConjugateDerivative_apply_contDiffAt_origin
    (internal : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorRegular : ContDiffAt ℝ 0
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 0 (fun point =>
      (holonomicFrameConjugateMatterDerivative GlobalECPath point internal)
        (vector point)) 0 := by
  unfold holonomicFrameConjugateMatterDerivative
    frameConjugateMatterDerivative
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply ContDiffAt.sum
  intro coordinate _
  have inverseEntryRegular : ContDiffAt ℝ 0 (fun point =>
      (GlobalECPath.coframe point)⁻¹ coordinate internal) 0 :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp globalECPath_coframeInverse_contDiffAt_origin
        coordinate) internal
  have inverseComplexRegular : ContDiffAt ℝ 0 (fun point =>
      ((GlobalECPath.coframe point)⁻¹ coordinate internal : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 inverseEntryRegular
  unfold holonomicConjugateMatterDerivativeDual
  exact inverseComplexRegular.smul
    (matterCoordinateDualPairing_contDiffAt_origin
      (globalECPath_conjugateDerivativeCoordinates_contDiffAt_origin
        coordinate) vectorRegular)

private theorem globalECPath_spatialFrameTransport_apply_contDiffAt_origin
    (vector : DiracExteriorMatterCarrier) :
    ContDiffAt ℝ 0 (fun point =>
      ∑ spatial : Fin 3,
        (holonomicFrameConjugateMatterDerivative GlobalECPath point
          spatial.succ).comp
          (identityCoframeMatterPrincipal spatial.succ) vector) 0 := by
  apply ContDiffAt.sum
  intro spatial _
  simp only [LinearMap.comp_apply]
  exact globalECPath_frameConjugateDerivative_apply_contDiffAt_origin
    spatial.succ
    (vector := fun _ => identityCoframeMatterPrincipal spatial.succ vector)
    contDiffAt_const

private theorem globalECPath_totalPrincipalDrift_apply_contDiffAt_origin
    (vector : DiracExteriorMatterCarrier) :
    ContDiffAt ℝ 0 (fun point =>
      holonomicLiveCoframeTotalDensitizedPrincipalDriftDual GlobalECPath point
        vector) 0 := by
  unfold holonomicLiveCoframeTotalDensitizedPrincipalDriftDual
  simp only [LinearMap.add_apply]
  exact
    (matterCoordinateDualPairing_contDiffAt_origin
      globalECPath_spatialPrincipalDrift_contDiffAt_origin
      contDiffAt_const).add
    (matterCoordinateDualPairing_contDiffAt_origin
      globalECPath_temporalPrincipalDrift_contDiffAt_origin
      contDiffAt_const)

private theorem globalECPath_frameKnownDual_apply_contDiffAt_origin
    (vector : DiracExteriorMatterCarrier) :
    ContDiffAt ℝ 0 (fun point =>
      holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
        GlobalECPath point vector) 0 := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]
  exact
    (globalECPath_algebraicDual_apply_contDiffAt_origin
      (vector := fun _ => vector) contDiffAt_const).sub
      (globalECPath_volumeComplex_contDiffAt_origin.smul
        (globalECPath_spatialFrameTransport_apply_contDiffAt_origin vector))
      |>.sub (globalECPath_totalPrincipalDrift_apply_contDiffAt_origin vector)

private theorem matterDualCoordinates_contDiffAt_of_basis
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (dualField : E → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : E)
    (basisSmooth : ∀ index : MatterCoordinateIndex,
      ContDiffAt ℝ n
        (fun candidate =>
          dualField candidate
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    ContDiffAt ℝ n (fun candidate =>
      matterDualCoordinates (dualField candidate)) point := by
  apply contDiffAt_piLp'
  intro index
  exact basisSmooth index

private theorem frameActionVelocity_apply_contDiffAt_of_regular
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier)
    (inverseVolumeRegular : ContDiffAt ℝ 0
      (fun candidate =>
        (((generatedVolumeDensity
          (toContinuumPointField configuration candidate) : ℝ) : ℂ)⁻¹)) point)
    (knownRegular : ContDiffAt ℝ 0
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterFrameKnownDensitizedDual
          configuration candidate
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            vector)) point) :
    ContDiffAt ℝ 0
      (fun candidate =>
        holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
          configuration candidate vector) point := by
  unfold holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  exact inverseVolumeRegular.mul knownRegular

private theorem globalECPath_frameActionVelocity_basis_contDiffAt_origin
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ 0
      (fun point =>
        holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity
          GlobalECPath point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) 0 :=
  frameActionVelocity_apply_contDiffAt_of_regular GlobalECPath 0
    (matterCoordinateEquiv.symm (EuclideanSpace.single index (1 : ℂ)))
    globalECPath_inverseVolumeComplex_contDiffAt_origin
    (globalECPath_frameKnownDual_apply_contDiffAt_origin
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))))

private theorem globalECPath_conjugateResponseCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun point =>
      matterDualCoordinates
        (globalFrameTimeConjugateMatterResponseAt GlobalECPath point)) 0 := by
  apply matterDualCoordinates_contDiffAt_of_basis
  intro index
  unfold globalFrameTimeConjugateMatterResponseAt
    globalFrameTimeConjugateMatterGeneratedDerivativeAt
  simp only [LinearMap.sub_apply]
  apply ContDiffAt.sub
  · exact globalECPath_frameActionVelocity_basis_contDiffAt_origin index
  · exact globalECPath_frameConjugateDerivative_basis_contDiffAt_origin 0 index

private theorem globalECPath_coframeRowLinearFunctional_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun point => coframeRowLinearFunctional (GlobalECPath.coframe point)) 0 := by
  unfold coframeRowLinearFunctional
  apply ContDiffAt.sum
  intro coordinate _
  exact
    ((contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (globalECPath_coframe_contDiffAt_two.of_le (by norm_num)) 0)
        coordinate).smul contDiffAt_const)

private theorem globalECPath_conjugateResponseOneForm_contDiffAt_origin :
    ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm GlobalECPath) 0 := by
  unfold coframeNativeGlobalConjugateMatterResponseOneForm
  apply ContDiffAt.smulRight
  · exact globalECPath_coframeRowLinearFunctional_contDiffAt_origin
  · exact globalECPath_conjugateResponseCoordinates_contDiffAt_origin

private theorem conjugateResponseOneForm_matterWrite_eq
    (current : StageNineHolonomicConfiguration) :
    coframeNativeGlobalConjugateMatterResponseOneForm
        (actionGeneratedGlobalFrameTimeMatterActual current) =
      coframeNativeGlobalConjugateMatterResponseOneForm current := by
  rfl

private theorem globalPrimal_conjugateResponseOneForm_eq_globalECPath :
    coframeNativeGlobalConjugateMatterResponseOneForm
        (actionGeneratedGlobalFrameTimeMatterActual GlobalECPath) =
      coframeNativeGlobalConjugateMatterResponseOneForm GlobalECPath :=
  conjugateResponseOneForm_matterWrite_eq GlobalECPath

private theorem globalPrimal_conjugateResponseOneForm_contDiffAt_origin :
    ContDiffAt ℝ 0
      (coframeNativeGlobalConjugateMatterResponseOneForm GlobalPrimal) 0 := by
  change ContDiffAt ℝ 0
    (coframeNativeGlobalConjugateMatterResponseOneForm
      (actionGeneratedGlobalFrameTimeMatterActual GlobalECPath)) 0
  exact (congrArg (fun field => ContDiffAt ℝ 0 field 0)
    globalPrimal_conjugateResponseOneForm_eq_globalECPath).symm.mp
      globalECPath_conjugateResponseOneForm_contDiffAt_origin

private theorem globalPrimal_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates GlobalPrimal) 0 := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates GlobalPrimal =
        holonomicConjugateMatterCoordinates GlobalECPath := by
    funext point
    unfold holonomicConjugateMatterCoordinates
    rw [actionGeneratedGlobalFrameTimeMatterActual_conjugateMatter]
  exact (congrArg (fun field => DifferentiableAt ℝ field 0)
    coordinatesEq).symm.mp
      (globalECPath_conjugateMatterCoordinates_contDiffAt_origin.differentiableAt
        (by norm_num))

private theorem globalMatterDual_adjointActionLaw_origin :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      GlobalMatterDual 0
      (holonomicFrameConjugateMatterDerivative GlobalMatterDual 0 0) := by
  change HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    (actionGeneratedGlobalFrameMatterDualActual GlobalECPath) 0
    (holonomicFrameConjugateMatterDerivative
      (actionGeneratedGlobalFrameMatterDualActual GlobalECPath) 0 0)
  exact actionGeneratedGlobalFrameMatterDualActual_adjointActionLaw_origin
    GlobalECPath globalPrimal_conjugateMatterCoordinates_differentiableAt_origin
    globalPrimal_conjugateResponseOneForm_contDiffAt_origin
    globalECPath_nondegenerate_origin

private theorem installReaction_frameAdjointActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (law : HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      configuration 0
      (holonomicFrameConjugateMatterDerivative configuration 0 0)) :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      (installFormNativeGravityReaction configuration) 0
      (holonomicFrameConjugateMatterDerivative
        (installFormNativeGravityReaction configuration) 0 0) := by
  exact law

private theorem globalFinal_frameAdjointActionLaw_origin :
    HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
      GlobalFinal 0
      (holonomicFrameConjugateMatterDerivative GlobalFinal 0 0) := by
  change HolonomicDiracDualLiveCoframeConjugateMatterFrameTimeActionLaw
    (installFormNativeGravityReaction GlobalMatterDual) 0
    (holonomicFrameConjugateMatterDerivative
      (installFormNativeGravityReaction GlobalMatterDual) 0 0)
  exact installReaction_frameAdjointActionLaw GlobalMatterDual
    globalMatterDual_adjointActionLaw_origin

private theorem globalFinal_liveAdjointActionLaw_origin :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw GlobalFinal 0
      (holonomicConjugateMatterDerivativeDual GlobalFinal 0 0) :=
  (frameTimeActionLaw_iff_liveCoframeTimeActionLaw GlobalFinal 0).1
    globalFinal_frameAdjointActionLaw_origin

private theorem globalFinal_coframe_eq_current :
    GlobalFinal.coframe = Current.coframe := by
  exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe

private theorem current_coframe_eq_prepared :
    Current.coframe = Prepared.coframe := by
  exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
    Source Prepared

private theorem globalFinal_coframe_eq_prepared :
    GlobalFinal.coframe = Prepared.coframe :=
  globalFinal_coframe_eq_current.trans current_coframe_eq_prepared

private theorem globalFinal_coframe_differentiableAt_origin :
    DifferentiableAt ℝ GlobalFinal.coframe 0 := by
  rw [globalFinal_coframe_eq_prepared]
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_hasFDerivAt_origin.differentiableAt

private theorem globalMatterDual_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates GlobalMatterDual) 0 := by
  have radialDifferentiable : DifferentiableAt ℝ
      (coframeNativeGlobalConjugateMatterRadialIncrement GlobalPrimal) 0 :=
    (coframeNativeGlobalConjugateMatterRadialIncrement_hasFDerivAt_origin
      GlobalPrimal globalPrimal_conjugateResponseOneForm_contDiffAt_origin
      ).differentiableAt
  have coordinatesEq :
      holonomicConjugateMatterCoordinates GlobalMatterDual =
        fun point => holonomicConjugateMatterCoordinates GlobalPrimal point +
          coframeNativeGlobalConjugateMatterRadialIncrement GlobalPrimal point := by
    funext point
    change holonomicConjugateMatterCoordinates
        (actionGeneratedGlobalFrameTimeConjugateMatterActual GlobalPrimal)
        point = _
    exact actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinates
      GlobalPrimal point
  rw [coordinatesEq]
  exact globalPrimal_conjugateMatterCoordinates_differentiableAt_origin.add
    radialDifferentiable

private theorem globalFinal_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates GlobalFinal) 0 := by
  change DifferentiableAt ℝ
    (holonomicConjugateMatterCoordinates
      (installFormNativeGravityReaction GlobalMatterDual)) 0
  exact globalMatterDual_conjugateMatterCoordinates_differentiableAt_origin

private theorem globalFinal_matterResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source GlobalFinal 0).matter =
      0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient Source GlobalFinal
        direction 0 = 0
  exact
    holonomicDiracDualMatterEulerLagrange_eq_zero_of_liveCoframeActionLaw
      Source GlobalFinal 0 globalFinal_coframe_differentiableAt_origin
      globalFinal_conjugateMatterCoordinates_differentiableAt_origin
      (fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nondegenerate 0)
      globalFinal_liveAdjointActionLaw_origin direction

private theorem globalFinal_coframe_eq_globalEC :
    GlobalFinal.coframe = GlobalEC.coframe := by
  calc
    GlobalFinal.coframe = Current.coframe := globalFinal_coframe_eq_current
    _ = GlobalEC.coframe := by rfl

private theorem globalFinal_gravityConnection_eq_globalECPath :
    GlobalFinal.gravityConnection = GlobalECPath.gravityConnection := by
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_fieldInventory.2.1

private theorem globalFinal_gravityConnection_origin_eq_globalEC :
    GlobalFinal.gravityConnection 0 = GlobalEC.gravityConnection 0 := by
  rw [globalFinal_gravityConnection_eq_globalECPath]
  exact globalECPath_connection_origin_eq_globalEC

private theorem globalFinal_gravityCurvature_origin_eq_globalEC :
    holonomicGravityCurvature GlobalFinal 0 =
      holonomicGravityCurvature GlobalEC 0 := by
  rw [show holonomicGravityCurvature GlobalFinal 0 =
      holonomicGravityCurvature GlobalECPath 0 by
    funext internalPair spacetimePair
    unfold holonomicGravityCurvature gravityConnectionDerivative
    rw [globalFinal_gravityConnection_eq_globalECPath]]
  exact globalECPath_curvature_origin_eq_globalEC

private theorem globalFinal_gravityAuxiliary_eq_globalEC :
    GlobalFinal.gravityAuxiliary = GlobalEC.gravityAuxiliary := by
  funext point internalPair spacetimePair
  change physicalIIPlusBivector (Current.coframe point)
      internalPair spacetimePair =
    physicalIIPlusBivector (GlobalP286.coframe point)
      internalPair spacetimePair
  rw [globalP286_coframe_eq_current]

private theorem globalFinal_multiplier_origin_eq_globalEC :
    GlobalFinal.gravitySimplicityMultiplier 0 =
      GlobalEC.gravitySimplicityMultiplier 0 := by
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_reactionSelfGenerated,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reactionSelfGenerated]
  unfold formNativeGravityReactionField holonomicContravariantGravityCurvature
  rw [globalFinal_gravityAuxiliary_eq_globalEC,
    globalFinal_gravityCurvature_origin_eq_globalEC]

private theorem globalFinal_gaugeConnection_eq_globalEC :
    GlobalFinal.gaugeConnection = GlobalEC.gaugeConnection := by
  rfl

private theorem globalFinal_gaugeAuxiliary_eq_globalEC :
    GlobalFinal.gaugeAuxiliary = GlobalEC.gaugeAuxiliary := by
  rfl

private theorem globalFinal_scalar_eq_globalEC :
    GlobalFinal.scalar = GlobalEC.scalar := by
  rfl

private theorem globalFinal_gaugeCurvature_origin_eq_globalEC :
    holonomicGaugeCurvature GlobalFinal 0 =
      holonomicGaugeCurvature GlobalEC 0 :=
  holonomicGaugeCurvature_eq_of_connection_eq GlobalFinal GlobalEC
    globalFinal_gaugeConnection_eq_globalEC 0

private theorem globalFinal_scalarCovariantDerivative_eq_globalEC :
    holonomicScalarCovariantDerivative GlobalFinal =
      holonomicScalarCovariantDerivative GlobalEC := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [globalFinal_scalar_eq_globalEC,
    globalFinal_gaugeConnection_eq_globalEC]

private theorem globalFinal_matter_origin_eq_globalEC :
    GlobalFinal.matter 0 = GlobalEC.matter 0 := by
  change
    (actionGeneratedGlobalFrameMatterDualActual GlobalECPath).matter 0 =
      GlobalEC.matter 0
  rw [(actionGeneratedGlobalFrameMatterDualActual_fieldInventory
    GlobalECPath).2.2.2.2.2.2.2.1,
    actionGeneratedGlobalFrameTimeMatterActual_matter_origin]
  rfl

private theorem globalPrimal_matterCovariantDerivative_origin_eq_globalECPath :
    holonomicMatterCovariantDerivative GlobalPrimal 0 =
      holonomicMatterCovariantDerivative GlobalECPath 0 := by
  funext direction
  apply matterCoordinateEquiv.injective
  unfold holonomicMatterCovariantDerivative
  rw [globalPrimal_matterCoordinateDerivative_origin_eq_globalECPath,
    actionGeneratedGlobalFrameTimeMatterActual_gravityConnection,
    actionGeneratedGlobalFrameTimeMatterActual_gaugeConnection,
    actionGeneratedGlobalFrameTimeMatterActual_matter_origin]

private theorem globalFinal_matter_eq_globalPrimal :
    GlobalFinal.matter = GlobalPrimal.matter := by
  change
    (actionGeneratedGlobalFrameMatterDualActual GlobalECPath).matter =
      GlobalPrimal.matter
  exact
    (actionGeneratedGlobalFrameMatterDualActual_fieldInventory
      GlobalECPath).2.2.2.2.2.2.2.1

private theorem globalFinal_matterCovariantDerivative_origin_eq_globalEC :
    holonomicMatterCovariantDerivative GlobalFinal 0 =
      holonomicMatterCovariantDerivative GlobalEC 0 := by
  calc
    holonomicMatterCovariantDerivative GlobalFinal 0 =
        holonomicMatterCovariantDerivative GlobalPrimal 0 := by
      funext direction
      unfold holonomicMatterCovariantDerivative
      rw [globalFinal_matter_eq_globalPrimal,
        show GlobalFinal.gravityConnection = GlobalPrimal.gravityConnection by
          exact globalFinal_gravityConnection_eq_globalECPath.trans
            (actionGeneratedGlobalFrameTimeMatterActual_gravityConnection
              GlobalECPath).symm,
        show GlobalFinal.gaugeConnection = GlobalPrimal.gaugeConnection by
          rw [globalFinal_gaugeConnection_eq_globalEC]
          rfl]
    _ = holonomicMatterCovariantDerivative GlobalECPath 0 :=
      globalPrimal_matterCovariantDerivative_origin_eq_globalECPath
    _ = holonomicMatterCovariantDerivative GlobalEC 0 :=
      globalECPath_matterCovariantDerivative_origin_eq_globalEC

private theorem globalFinal_conjugateMatter_origin_eq_globalEC :
    GlobalFinal.conjugateMatter 0 = GlobalEC.conjugateMatter 0 := by
  change
    (actionGeneratedGlobalFrameMatterDualActual GlobalECPath).conjugateMatter
        0 = GlobalEC.conjugateMatter 0
  rw [(actionGeneratedGlobalFrameMatterDualActual_fieldInventory
    GlobalECPath).2.2.2.2.2.2.2.2]
  rfl

private theorem globalFinal_pointField_origin_eq_globalEC :
    toContinuumPointField GlobalFinal 0 =
      toContinuumPointField GlobalEC 0 := by
  apply StageNineContinuumPointField.ext
  · exact congrFun globalFinal_coframe_eq_globalEC 0
  · exact globalFinal_gravityCurvature_origin_eq_globalEC
  · exact congrFun globalFinal_gravityAuxiliary_eq_globalEC 0
  · exact globalFinal_multiplier_origin_eq_globalEC
  · exact globalFinal_gaugeCurvature_origin_eq_globalEC
  · exact congrFun globalFinal_gaugeAuxiliary_eq_globalEC 0
  · exact congrFun globalFinal_scalar_eq_globalEC 0
  · exact congrFun globalFinal_scalarCovariantDerivative_eq_globalEC 0
  · exact globalFinal_matter_origin_eq_globalEC
  · exact globalFinal_matterCovariantDerivative_origin_eq_globalEC
  · exact globalFinal_conjugateMatter_origin_eq_globalEC

private theorem globalFinal_gravityAuxiliaryExterior_origin_eq_globalEC :
    holonomicGravityAuxiliaryExteriorCovariantDerivative GlobalFinal 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative GlobalEC 0 := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [globalFinal_gravityConnection_origin_eq_globalEC,
    globalFinal_gravityAuxiliary_eq_globalEC]

private theorem globalFinal_p286GaugeAuxiliaryExterior_eq_globalEC :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative GlobalFinal =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative GlobalEC := by
  funext point
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [globalFinal_gaugeConnection_eq_globalEC,
    globalFinal_gaugeAuxiliary_eq_globalEC]

private theorem globalFinal_scalarDifferentialMomentum_eq_globalEC
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum Source GlobalFinal direction
        derivativeDirection =
      scalarDifferentialMomentum Source GlobalEC direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [globalFinal_coframe_eq_globalEC,
    globalFinal_scalarCovariantDerivative_eq_globalEC]

private theorem globalFinal_scalarDifferentialMomentumDivergence_eq_globalEC
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence Source GlobalFinal direction =
      scalarDifferentialMomentumDivergence Source GlobalEC direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [globalFinal_scalarDifferentialMomentum_eq_globalEC]

private theorem globalFinal_actionJet_origin_normalForm :
    generatedDiracDualFormNativePointwiseActionJet Source GlobalFinal 0 =
      { generatedDiracDualFormNativePointwiseActionJet Source GlobalEC 0 with
        matterDifferentialMomentumDivergence :=
          (generatedDiracDualFormNativePointwiseActionJet Source GlobalFinal 0
            ).matterDifferentialMomentumDivergence } := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · exact globalFinal_pointField_origin_eq_globalEC
  · exact globalFinal_gravityConnection_origin_eq_globalEC
  · exact congrFun globalFinal_gaugeConnection_eq_globalEC 0
  · exact globalFinal_gravityAuxiliaryExterior_origin_eq_globalEC
  · exact congrFun globalFinal_p286GaugeAuxiliaryExterior_eq_globalEC 0
  · funext direction
    exact congrFun
      (globalFinal_scalarDifferentialMomentumDivergence_eq_globalEC direction) 0
  · rfl

private theorem jointResidualReadout_update_matterDivergence
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (jet : DiracDualFormNativePointwiseActionJetCarrier)
    (divergence : MatterCoordinateCarrier → ℝ) :
    diracDualFormNativeJointResidualOfActionJet source point
        { jet with matterDifferentialMomentumDivergence := divergence } =
      { diracDualFormNativeJointResidualOfActionJet source point jet with
        matter :=
          (diracDualFormNativeJointResidualOfActionJet source point
            { jet with matterDifferentialMomentumDivergence := divergence }
            ).matter } := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext <;> rfl

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_residual_origin_zero :
    diracDualFormNativePointwiseJointResidual Source GlobalFinal 0 = 0 := by
  rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
    globalFinal_actionJet_origin_normalForm,
    jointResidualReadout_update_matterDivergence]
  have globalECReadoutShape :
      diracDualFormNativeJointResidualOfActionJet Source 0
          (generatedDiracDualFormNativePointwiseActionJet Source GlobalEC 0) =
        { (0 : DiracDualFormNativePointwiseJointResidualCarrier) with
          matter :=
            (diracDualFormNativePointwiseJointResidual Source GlobalEC 0
              ).matter } := by
    rw [← diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
    exact globalEC_jointResidual_origin_eq_matterRead
  have updatedMatterZero :
      (diracDualFormNativeJointResidualOfActionJet Source 0
        { generatedDiracDualFormNativePointwiseActionJet Source GlobalEC 0 with
          matterDifferentialMomentumDivergence :=
            (generatedDiracDualFormNativePointwiseActionJet Source GlobalFinal 0
              ).matterDifferentialMomentumDivergence }).matter = 0 := by
    have finalMatterZero := globalFinal_matterResidual_origin_zero
    rw [diracDualFormNativePointwiseJointResidual_eq_actionJetReadout,
      globalFinal_actionJet_origin_normalForm] at finalMatterZero
    exact finalMatterZero
  rw [globalECReadoutShape, updatedMatterZero]
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext <;> simp

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_zeroFiber_origin :
    OnDiracDualFormNativePointwiseJointZeroFiber Source GlobalFinal 0 := by
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_residual_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalOriginResidualClosure
