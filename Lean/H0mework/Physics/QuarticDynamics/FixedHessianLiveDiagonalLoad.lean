import H0mework.Physics.QuarticDynamics.FixedHessianPrefixedJointGlobalActual
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyLiveStressSpatialRegularity
import H0mework.Physics.FinalJoint.FixedTimeAxisP286ResidualNormalForm
import H0mework.Physics.IdentityHessian.CartanECNormalFixedContactRegularity
import H0mework.Physics.DualVariation.ECCauchyConnectionLocalActualLift

/-!
# Fixed P506/L0 Hessian live spatial-diagonal load

This module computes the `(1,1)`, `(2,2)`, and `(3,3)` live identity-EC
action loads consumed by the fixed source/current-generated Hessian carrier.
The relatively long explicit calculation is kept together because all three
coordinates share the same coframe-path differentiability, inverse-frame,
gauge-density, and repaired-matter-density mechanism.  Every value is read
forward from the same generated pre-EC actual.  No determinant, target
coframe, residual, or repair coordinate is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianLiveDiagonalLoad

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionLocalActualLiftRegression
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECCauchyConstraintObstructionRegression
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGravityCurvatureTargetCoordinate
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure
open StageNineDiracDualFormNativeFixedP506CartanRestartCurvatureSpatialRegularity
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286ResidualNormalForm
open StageNineDiracDualFormNativeFixedP506FinalCommonPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSixSectorClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalFourFormPairing
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineIIPlusRestriction
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineScalarLocalSpinDensity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open PointwiseDiracSpinConnectionLift
open SU7ExteriorMatterRepresentation
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

local instance liveStressP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  constitutiveRegularityP286ModuleFinite

local instance liveStressP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  constitutiveRegularityP286CoordinateIndexFintype

local instance liveStressP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  constitutiveRegularityP286CoordinateIsTopologicalAddGroup

local instance liveStressMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev HessianRows : IdentityECEtaCompatibleRows :=
  sourceActionGeneratedIdentityECCoframeAccelerationRows Source Current

private abbrev LowerOrderRows : LorentzianCoframe :=
  sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates Source Current

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- The fixed P506/L0 live identity-EC point field consumed by the Hessian
load.  This is a readout carrier from the source/current-generated pre-EC
actual; no coframe variation or target load is stored in it. -/
abbrev fixedP506L0HessianLiveContact : StageNineContinuumPointField :=
  diracDualFormNativeECNormalContactField
    (fixedP506L0FinalCommonPreECActionActual 0)

private abbrev LiveContact : StageNineContinuumPointField :=
  fixedP506L0HessianLiveContact

private abbrev SmoothComparison : StageNineHolonomicConfiguration :=
  fixedP506FormNativeRepairedSpatialMatterSmoothComparison

private def MatterBaseComparison : StageNineHolonomicConfiguration :=
  { InputActual with
    gravityConnection := fun _ =>
      (fixedP506L0CartanRestartActual 0).gravityConnection 0 }

private theorem canonicalCauchySlicePoint_zero_zero_live :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem fixedP506L0FinalCommonPreEC_pointField_origin :
    toContinuumPointField (fixedP506L0FinalCommonPreECActionActual 0) 0 =
      toContinuumPointField
        (recenteredCartanRepairedConstitutiveCurrent 0) 0 := by
  calc
    toContinuumPointField (fixedP506L0FinalCommonPreECActionActual 0) 0 =
        toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual 0) 0 :=
      formNativeCurrentP286CompleteActionResponseOperator_pointField_origin
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual 0)
    _ = toContinuumPointField
          (recenteredCartanRepairedConstitutiveCurrent 0) 0 :=
      recenteredCartanRepairedScalarSecondJetActual_pointField_origin 0

@[simp] private theorem liveContact_coframe : LiveContact.coframe = 1 := by
  unfold LiveContact fixedP506L0HessianLiveContact
    diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  change
    (restrictContinuumPointFieldToIIPlus
        (toContinuumPointField (fixedP506L0FinalCommonPreECActionActual 0) 0)
      ).coframe = 1
  rw [fixedP506L0FinalCommonPreEC_pointField_origin]
  exact recenteredCartanRepairedConstitutiveCurrent_coframe_origin 0

private theorem liveContact_scalar_eq_comparison :
    LiveContact.scalar =
      (toContinuumPointField SmoothComparison 0).scalar := by
  change
    (fixedP506L0FinalCommonPreECActionActual 0).scalar 0 =
      SmoothComparison.scalar 0
  calc
    (fixedP506L0FinalCommonPreECActionActual 0).scalar 0 =
        (recenteredCartanRepairedConstitutiveCurrent 0).scalar 0 := by
      exact congrArg StageNineContinuumPointField.scalar
        fixedP506L0FinalCommonPreEC_pointField_origin
    _ = (fixedP506L0CartanRestartActual 0).scalar 0 := rfl
    _ = (fixedP506L0RecenteredInput 0).scalar 0 := by
      simp [fixedP506L0CartanRestartActual]
    _ = InputActual.scalar 0 := by
      simp [fixedP506L0RecenteredInput,
        spatiallyRecenterHolonomicConfiguration,
        canonicalSpatialContactTranslation,
        canonicalCauchySlicePoint_zero_zero_live]
    _ = SmoothComparison.scalar 0 := rfl

private theorem liveContact_matter_eq_comparison :
    LiveContact.matter =
      (toContinuumPointField SmoothComparison 0).matter := by
  change
    (fixedP506L0FinalCommonPreECActionActual 0).matter 0 =
      SmoothComparison.matter 0
  calc
    (fixedP506L0FinalCommonPreECActionActual 0).matter 0 =
        (recenteredCartanRepairedConstitutiveCurrent 0).matter 0 := by
      exact congrArg StageNineContinuumPointField.matter
        fixedP506L0FinalCommonPreEC_pointField_origin
    _ = (fixedP506L0CartanRestartActual 0).matter 0 :=
      recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan 0
    _ = (fixedP506L0RecenteredInput 0).matter 0 := by
      simp [fixedP506L0CartanRestartActual]
    _ = InputActual.matter 0 := by
      simp [fixedP506L0RecenteredInput,
        spatiallyRecenterHolonomicConfiguration,
        canonicalSpatialContactTranslation,
        canonicalCauchySlicePoint_zero_zero_live]
    _ = SmoothComparison.matter 0 := by
      rw [repairedMatterComparison_matter_eq_repaired]
      simpa only [canonicalCauchySlicePoint_zero_zero_live] using
        (fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matter_zeroSlice
          0).symm

private theorem liveContact_conjugateMatter_eq_comparison :
    LiveContact.conjugateMatter =
      (toContinuumPointField SmoothComparison 0).conjugateMatter := by
  change
    (fixedP506L0FinalCommonPreECActionActual 0).conjugateMatter 0 =
      SmoothComparison.conjugateMatter 0
  calc
    (fixedP506L0FinalCommonPreECActionActual 0).conjugateMatter 0 =
        (recenteredCartanRepairedConstitutiveCurrent 0).conjugateMatter 0 := by
      exact congrArg StageNineContinuumPointField.conjugateMatter
        fixedP506L0FinalCommonPreEC_pointField_origin
    _ = (fixedP506L0CartanRestartActual 0).conjugateMatter 0 :=
      recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan
        0
    _ = (fixedP506L0RecenteredInput 0).conjugateMatter 0 := by
      simp [fixedP506L0CartanRestartActual]
    _ = InputActual.conjugateMatter 0 := by
      simp [fixedP506L0RecenteredInput,
        spatiallyRecenterHolonomicConfiguration,
        canonicalSpatialContactTranslation,
        canonicalCauchySlicePoint_zero_zero_live]
    _ = SmoothComparison.conjugateMatter 0 := by
      rw [repairedMatterComparison_conjugateMatter_eq_repaired]
      change
        InputActual.conjugateMatter 0 =
          (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
            positiveSmoothUnifiedSource InputActual).conjugateMatter 0
      simpa only [canonicalCauchySlicePoint_zero_zero_live] using
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
          positiveSmoothUnifiedSource InputActual 0).symm

private theorem liveContact_matterCovariantDerivative_eq_installed
    (direction : LorentzianIndex) :
    LiveContact.matterCovariantDerivative direction =
      holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual 0)) 0 direction := by
  unfold LiveContact fixedP506L0HessianLiveContact
  change
    holonomicMatterCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual 0) 0 direction =
      holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual 0)) 0 direction
  have derivativeEq := congrArg
    StageNineContinuumPointField.matterCovariantDerivative
    fixedP506L0FinalCommonPreEC_pointField_origin
  change
    holonomicMatterCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual 0) 0 =
      holonomicMatterCovariantDerivative
        (recenteredCartanRepairedConstitutiveCurrent 0) 0 at derivativeEq
  rw [congrFun derivativeEq direction]
  unfold recenteredCartanRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rfl

private theorem liveContact_scalarCovariantDerivative_eq_input :
    LiveContact.scalarCovariantDerivative =
      (toContinuumPointField InputActual 0).scalarCovariantDerivative := by
  unfold LiveContact fixedP506L0HessianLiveContact
  change
    holonomicScalarCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual 0) 0 =
      holonomicScalarCovariantDerivative InputActual 0
  have derivativeEq := congrArg
    StageNineContinuumPointField.scalarCovariantDerivative
    fixedP506L0FinalCommonPreEC_pointField_origin
  change
    holonomicScalarCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual 0) 0 =
      holonomicScalarCovariantDerivative
        (recenteredCartanRepairedConstitutiveCurrent 0) 0 at derivativeEq
  rw [derivativeEq]
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [recenteredCartanRepairedConstitutiveCurrent_scalar,
    recenteredCartanRepairedConstitutiveCurrent_gaugeConnection]
  unfold recenteredContactActual
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]
  simp [spatiallyRecenterHolonomicConfiguration,
    canonicalSpatialContactTranslation,
    canonicalCauchySlicePoint_zero_zero_live]

private theorem
    inputActual_gravityConnection_origin_eq_fixedP506JointActual :
    InputActual.gravityConnection 0 =
      FixedP506JointActual.gravityConnection 0 := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_gravityConnection_origin,
    fixedP506JointActionSuccessor_gravityConnection]

private theorem
    cartanRestart_zero_gravityConnection_origin_eq_fixedP506JointActual :
    (fixedP506L0CartanRestartActual 0).gravityConnection 0 =
      FixedP506JointActual.gravityConnection 0 := by
  calc
    _ = sourceActionGeneratedDiracDualCartanConnectionField
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedCauchyState 0 0 :=
      fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan
        0
    _ = FixedP506JointActionSuccessor.gravityConnection 0 :=
      fixedJointCartanConnection_zero_eq_jointActionSuccessor_origin
    _ = FixedP506JointActual.gravityConnection 0 := by
      rw [fixedP506JointActionSuccessor_gravityConnection]

private theorem inputActual_gaugeConnection_origin_eq_fixedP506JointActual :
    InputActual.gaugeConnection 0 =
      FixedP506JointActual.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  change holonomicP286GaugeConnectionCoordinate InputActual 0 direction =
    holonomicP286GaugeConnectionCoordinate FixedP506JointActual 0 direction
  rw [congrFun
      fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_origin_zero
      direction,
    congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
      direction]

private theorem liveContact_scalar_eq_fixedP506JointActual :
    LiveContact.scalar =
      (toContinuumPointField FixedP506JointActual 0).scalar := by
  rw [liveContact_scalar_eq_comparison]
  change InputActual.scalar 0 = FixedP506JointActual.scalar 0
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar]

private theorem liveContact_matter_eq_fixedP506JointActual :
    LiveContact.matter =
      (toContinuumPointField FixedP506JointActual 0).matter := by
  rw [liveContact_matter_eq_comparison]
  change SmoothComparison.matter 0 = FixedP506JointActual.matter 0
  rw [repairedMatterComparison_matter_eq_repaired]
  change
    FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.matter
        0 = FixedP506JointActual.matter 0
  calc
    _ = InputActual.matter 0 := by
      simpa only [canonicalCauchySlicePoint_zero_zero_live] using
        fixedP506FormNativeRepairedConstitutiveJointActionSpatialSection_matter_zeroSlice
          0
    _ = FixedP506JointActual.matter 0 := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
        fixedP506JointActionSuccessor_matter]

private theorem liveContact_conjugateMatter_eq_fixedP506JointActual :
    LiveContact.conjugateMatter =
      (toContinuumPointField FixedP506JointActual 0).conjugateMatter := by
  rw [liveContact_conjugateMatter_eq_comparison]
  change SmoothComparison.conjugateMatter 0 =
    FixedP506JointActual.conjugateMatter 0
  rw [repairedMatterComparison_conjugateMatter_eq_repaired]
  change
    FixedP506FormNativeRepairedConstitutiveJointActionSpatialSectionSuccessor.conjugateMatter
        0 = FixedP506JointActual.conjugateMatter 0
  calc
    _ = InputActual.conjugateMatter 0 := by
      change
        (diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
          positiveSmoothUnifiedSource InputActual).conjugateMatter 0 =
          InputActual.conjugateMatter 0
      simpa only [canonicalCauchySlicePoint_zero_zero_live] using
        diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_conjugateMatter_zeroSlice
          positiveSmoothUnifiedSource InputActual 0
    _ = FixedP506JointActual.conjugateMatter 0 := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
        fixedP506JointActionSuccessor_conjugateMatter]

private theorem cartanRestart_zero_matter_field_eq_input :
    (fixedP506L0CartanRestartActual 0).matter = InputActual.matter := by
  unfold fixedP506L0CartanRestartActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  unfold fixedP506L0RecenteredInput
    spatiallyRecenterHolonomicConfiguration
  funext point
  simp [canonicalSpatialContactTranslation,
    canonicalCauchySlicePoint_zero_zero_live]

private theorem cartanRestart_zero_gaugeConnection_field_eq_input :
    (fixedP506L0CartanRestartActual 0).gaugeConnection =
      InputActual.gaugeConnection := by
  unfold fixedP506L0CartanRestartActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  unfold fixedP506L0RecenteredInput
    spatiallyRecenterHolonomicConfiguration
  funext point direction
  simp [canonicalSpatialContactTranslation,
    canonicalCauchySlicePoint_zero_zero_live]

private theorem
    cartanRestart_zero_matterCovariantDerivative_eq_fixedP506JointActual
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (fixedP506L0CartanRestartActual 0) 0 direction =
      holonomicMatterCovariantDerivative
        FixedP506JointActual 0 direction := by
  unfold holonomicMatterCovariantDerivative
  rw [cartanRestart_zero_matter_field_eq_input,
    cartanRestart_zero_gravityConnection_origin_eq_fixedP506JointActual,
    cartanRestart_zero_gaugeConnection_field_eq_input,
    inputActual_gaugeConnection_origin_eq_fixedP506JointActual]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]

private theorem cartanRestart_zero_coframe_origin_eq_fixedP506JointActual :
    (fixedP506L0CartanRestartActual 0).coframe 0 =
      FixedP506JointActual.coframe 0 := by
  unfold fixedP506L0CartanRestartActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  unfold fixedP506L0RecenteredInput
  change InputActual.coframe (canonicalSpatialContactTranslation 0 0) =
    FixedP506JointActual.coframe 0
  rw [show canonicalSpatialContactTranslation 0 0 = 0 by
      simp [canonicalSpatialContactTranslation,
        canonicalCauchySlicePoint_zero_zero_live]]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]

private theorem cartanRestart_zero_scalar_origin_eq_fixedP506JointActual :
    (fixedP506L0CartanRestartActual 0).scalar 0 =
      FixedP506JointActual.scalar 0 := by
  unfold fixedP506L0CartanRestartActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]
  unfold fixedP506L0RecenteredInput
  change InputActual.scalar (canonicalSpatialContactTranslation 0 0) =
    FixedP506JointActual.scalar 0
  rw [show canonicalSpatialContactTranslation 0 0 = 0 by
      simp [canonicalSpatialContactTranslation,
        canonicalCauchySlicePoint_zero_zero_live]]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar]

private theorem cartanRestart_zero_matter_origin_eq_fixedP506JointActual :
    (fixedP506L0CartanRestartActual 0).matter 0 =
      FixedP506JointActual.matter 0 := by
  rw [cartanRestart_zero_matter_field_eq_input]
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]

private theorem
    cartanRestart_zero_repairedKnownVector_eq_fixedP506JointActual :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (fixedP506L0CartanRestartActual 0) 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        FixedP506JointActual 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [cartanRestart_zero_coframe_origin_eq_fixedP506JointActual,
    cartanRestart_zero_scalar_origin_eq_fixedP506JointActual,
    cartanRestart_zero_matter_origin_eq_fixedP506JointActual]
  simp_rw [cartanRestart_zero_matterCovariantDerivative_eq_fixedP506JointActual]

private theorem
    cartanRestart_zero_generatedMatterTimeCovariantDerivative_eq_fixed :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        (fixedP506L0CartanRestartActual 0) 0 =
      holonomicMatterCovariantDerivative FixedP506JointActual 0
        canonicalLorentzianTimeDirection := by
  have noncharacteristic :
      coframeTemporalPrincipalScalar
          ((fixedP506L0CartanRestartActual 0).coframe 0) ≠ 0 := by
    rw [cartanRestart_zero_coframe_origin_eq_fixedP506JointActual,
      fixedP506JointActual_coframe_origin_one]
    simp
  have generatedLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      (fixedP506L0CartanRestartActual 0) 0 noncharacteristic
  have fixedLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        (fixedP506L0CartanRestartActual 0) 0
        (holonomicMatterCovariantDerivative FixedP506JointActual 0
          canonicalLorentzianTimeDirection) := by
    have fixedLawBase :=
      fixedP506JointActual_repairedMatterActionLaw_origin_live
    unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      CurrentCoframeMatterTemporalActionLaw at fixedLawBase ⊢
    rw [cartanRestart_zero_coframe_origin_eq_fixedP506JointActual,
      cartanRestart_zero_repairedKnownVector_eq_fixedP506JointActual]
    exact fixedLawBase
  exact
    holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique
      (fixedP506L0CartanRestartActual 0) 0 noncharacteristic _ _
      generatedLaw fixedLaw

private theorem fixedP506L0CartanRestartActual_matter_contDiff_local :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        ((fixedP506L0CartanRestartActual 0).matter point) := by
  rw [cartanRestart_zero_matter_field_eq_input]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1

private theorem
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin_local
    (configuration : StageNineHolonomicConfiguration)
    (matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point))
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((installMatterLinearTimeResponse configuration response).matter
              point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (configuration.matter point))
          0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterCoordinateEquiv response
        else
          0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0 :=
    (matterSmooth.differentiable (by simp)).differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (matterLinearTimeCoordinateWrite response) 0 :=
    ((matterLinearTimeCoordinateWrite_contDiff response).differentiable
      (by simp)).differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((installMatterLinearTimeResponse configuration response).matter
          point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterLinearTimeCoordinateWrite response by
    funext point
    exact installMatterLinearTimeResponse_matter_coordinate
      configuration response point]
  rw [fderiv_add backgroundDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (matterLinearTimeCoordinateWrite response) 0 direction = _
  rw [matterLinearTimeCoordinateWrite_directionalDerivative]

private theorem
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_local
    (configuration : StageNineHolonomicConfiguration)
    (matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point))
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installMatterLinearTimeResponse configuration response) 0 direction =
      holonomicMatterCovariantDerivative configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then response else 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin_local
      configuration matterSmooth response direction]
  split_ifs <;>
    simp only [map_add, matterCoordinateEquiv.symm_apply_apply, map_zero,
      installMatterLinearTimeResponse_gravityConnection,
      installMatterLinearTimeResponse_gaugeConnection,
      installMatterLinearTimeResponse_matter_origin] <;>
    module

private theorem
    liveInstalledMatterCovariantDerivative_coordinate_eq
    (direction : LorentzianIndex) :
    matterCoordinateEquiv
        (holonomicMatterCovariantDerivative
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            (fixedP506L0CartanRestartActual 0)) 0 direction) =
      matterCoordinateEquiv
          (holonomicMatterCovariantDerivative
            (fixedP506L0CartanRestartActual 0) 0 direction) +
        if direction = canonicalLorentzianTimeDirection then
          matterCoordinateEquiv
            (diracDualCurrentCoframeMatterTimeResponseWrite
              (fixedP506L0CartanRestartActual 0))
        else
          0 := by
  unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_local
      (fixedP506L0CartanRestartActual 0)
      fixedP506L0CartanRestartActual_matter_contDiff_local
      (diracDualCurrentCoframeMatterTimeResponseWrite
        (fixedP506L0CartanRestartActual 0))
      direction]
  split_ifs <;> simp

private theorem
    liveContact_matterCovariantDerivative_eq_fixedP506JointActual :
    LiveContact.matterCovariantDerivative =
      (toContinuumPointField
        FixedP506JointActual 0).matterCovariantDerivative := by
  funext direction
  apply matterCoordinateEquiv.injective
  rw [liveContact_matterCovariantDerivative_eq_installed,
    liveInstalledMatterCovariantDerivative_coordinate_eq]
  by_cases temporal : direction = canonicalLorentzianTimeDirection
  · subst direction
    rw [if_pos rfl]
    unfold diracDualCurrentCoframeMatterTimeResponseWrite
    rw [cartanRestart_zero_generatedMatterTimeCovariantDerivative_eq_fixed]
    simp
    rfl
  · rw [if_neg temporal, add_zero]
    exact congrArg matterCoordinateEquiv
      (cartanRestart_zero_matterCovariantDerivative_eq_fixedP506JointActual
        direction)

private theorem
    liveContact_scalarCovariantDerivative_eq_fixedP506JointActual :
    LiveContact.scalarCovariantDerivative =
      (toContinuumPointField
        FixedP506JointActual 0).scalarCovariantDerivative := by
  rw [liveContact_scalarCovariantDerivative_eq_input]
  change holonomicScalarCovariantDerivative InputActual 0 =
    holonomicScalarCovariantDerivative FixedP506JointActual 0
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    inputActual_gaugeConnection_origin_eq_fixedP506JointActual]

/-! ## Public fixed-contact field seams -/

@[simp] theorem fixedP506L0HessianLiveContact_coframe :
    fixedP506L0HessianLiveContact.coframe = 1 :=
  liveContact_coframe

theorem fixedP506L0HessianLiveContact_scalar_eq_fixedP506JointActual :
    fixedP506L0HessianLiveContact.scalar =
      (toContinuumPointField FixedP506JointActual 0).scalar :=
  liveContact_scalar_eq_fixedP506JointActual

theorem fixedP506L0HessianLiveContact_matter_eq_fixedP506JointActual :
    fixedP506L0HessianLiveContact.matter =
      (toContinuumPointField FixedP506JointActual 0).matter :=
  liveContact_matter_eq_fixedP506JointActual

theorem fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual :
    fixedP506L0HessianLiveContact.conjugateMatter =
      (toContinuumPointField FixedP506JointActual 0).conjugateMatter :=
  liveContact_conjugateMatter_eq_fixedP506JointActual

theorem
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual :
    fixedP506L0HessianLiveContact.matterCovariantDerivative =
      (toContinuumPointField
        FixedP506JointActual 0).matterCovariantDerivative :=
  liveContact_matterCovariantDerivative_eq_fixedP506JointActual

theorem
    fixedP506L0HessianLiveContact_scalarCovariantDerivative_eq_fixedP506JointActual :
    fixedP506L0HessianLiveContact.scalarCovariantDerivative =
      (toContinuumPointField
        FixedP506JointActual 0).scalarCovariantDerivative :=
  liveContact_scalarCovariantDerivative_eq_fixedP506JointActual

private def liveGaugeAuxiliaryCoordinates : FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear LiveContact.gaugeAuxiliary

private def liveGaugeCurvatureCoordinates : FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear LiveContact.gaugeCurvature

private theorem liveGaugeAuxiliaryCoordinates_eq_origin :
    liveGaugeAuxiliaryCoordinates =
      currentP286OriginAuxiliaryCoordinate
        (recenteredCartanRepairedScalarSecondJetActual 0) := by
  funext pair
  unfold liveGaugeAuxiliaryCoordinates LiveContact
    fixedP506L0HessianLiveContact
    diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  change
    p286CoordinateEquiv
        ((fixedP506L0FinalCommonPreECActionActual 0).gaugeAuxiliary 0 pair) = _
  have pointField :=
    formNativeCurrentP286CompleteActionResponseOperator_pointField_origin
      positiveSmoothUnifiedSource
      (recenteredCartanRepairedScalarSecondJetActual 0)
  have auxiliaryEq :=
    congrArg StageNineContinuumPointField.gaugeAuxiliary pointField
  change
    (fixedP506L0FinalCommonPreECActionActual 0).gaugeAuxiliary 0 =
      (recenteredCartanRepairedScalarSecondJetActual 0).gaugeAuxiliary 0
    at auxiliaryEq
  rw [auxiliaryEq]
  rfl

private theorem
    recenteredCartanRepairedConstitutiveCurrent_gaugeConnection_eq_input :
    (recenteredCartanRepairedConstitutiveCurrent 0).gaugeConnection =
      (spatiallyRecenterHolonomicConfiguration InputActual 0).gaugeConnection := by
  rw [recenteredCartanRepairedConstitutiveCurrent_gaugeConnection]
  unfold recenteredContactActual
  rw [
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection]

private theorem
    recenteredCartanRepairedConstitutiveCurrent_gaugeCurvature_origin :
    holonomicGaugeCurvature
        (recenteredCartanRepairedConstitutiveCurrent 0) 0 =
      holonomicGaugeCurvature InputActual 0 := by
  calc
    holonomicGaugeCurvature
          (recenteredCartanRepairedConstitutiveCurrent 0) 0 =
        holonomicGaugeCurvature
          (spatiallyRecenterHolonomicConfiguration InputActual 0) 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq_current _ _
        recenteredCartanRepairedConstitutiveCurrent_gaugeConnection_eq_input 0
    _ = holonomicGaugeCurvature InputActual
          (canonicalSpatialContactTranslation 0 0) :=
      holonomicGaugeCurvature_spatiallyRecenter InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth 0 0
    _ = holonomicGaugeCurvature InputActual 0 := by
      congr 1
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalSpatialContactTranslation,
          canonicalCauchySlicePoint,
          canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem liveGaugeCurvatureCoordinates_eq_input :
    liveGaugeCurvatureCoordinates =
      holonomicP286GaugeCurvatureCoordinate InputActual 0 := by
  unfold liveGaugeCurvatureCoordinates LiveContact
    fixedP506L0HessianLiveContact
    diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  change
    formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature
          (fixedP506L0FinalCommonPreECActionActual 0) 0) = _
  have pointField := fixedP506L0FinalCommonPreEC_pointField_origin
  have curvatureEq :=
    congrArg StageNineContinuumPointField.gaugeCurvature pointField
  change
    holonomicGaugeCurvature (fixedP506L0FinalCommonPreECActionActual 0) 0 =
      holonomicGaugeCurvature
        (recenteredCartanRepairedConstitutiveCurrent 0) 0
    at curvatureEq
  rw [curvatureEq,
    recenteredCartanRepairedConstitutiveCurrent_gaugeCurvature_origin]
  rfl

private theorem liveP506BlockwiseCoupling_same
    (parameter : ℝ) (coordinate : P286CoordinateCarrier) :
    formNativeP286BlockwiseCouplingCoordinateLinear
        parameter parameter parameter coordinate =
      parameter • coordinate := by
  apply p286CoordinateEquiv.symm.injective
  simp [formNativeP286BlockwiseCouplingCoordinateLinear,
    formNativeP286BlockwiseCouplingActualLinear]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

private theorem liveP506CoordinateBlockwiseConstitutive_eq_unified
    (coframe : LorentzianCoframe)
    (form : FormNativeP286GaugeCoordinateTwoForm) :
    formNativeP286CoordinateBlockwiseConstitutive coframe
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        form =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear coframe)
        form := by
  have weakEq :
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).weakCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  have hyperchargeEq :
      ((sourceGeneratedUnifiedCouplings
        positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ) =
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) := by
    rfl
  rw [weakEq, hyperchargeEq,
    formNativeP286CoordinateBlockwiseConstitutive_eq_sum,
    liftGaugeTwoFormOperator_smul_operator_p286]
  funext output
  unfold liftGaugeTwoFormOperator
  simp only [Pi.smul_apply]
  simp_rw [liveP506BlockwiseCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

private theorem liveGaugeCurvatureCoordinates_normalForm :
    liveGaugeCurvatureCoordinates =
      matterResponseOriginCurvatureNormalForm := by
  rw [liveGaugeCurvatureCoordinates_eq_input,
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm]
  funext pair
  fin_cases pair <;>
    simp [matterResponseOriginCurvatureNormalForm,
      c3h181FullCurvatureCoordinateNormalForm,
      c3h181StrongCouplingSquared,
      StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half];
    module

private theorem liveGaugeAuxiliaryCoordinates_normalForm :
    liveGaugeAuxiliaryCoordinates =
      matterResponseOriginAuxiliaryNormalForm := by
  rw [liveGaugeAuxiliaryCoordinates_eq_origin,
    fixedP506L0CompleteJointP286OriginAuxiliary_normalForm,
    canonicalCauchySlicePoint_zero_zero_live,
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm]
  simp only [neg_zero]
  have recovered :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_constitutive
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      1 (by norm_num) (c3h181FullAuxiliaryCoordinateNormalForm 0)
  rw [liveP506CoordinateBlockwiseConstitutive_eq_unified] at recovered
  rw [c3h181FullAuxiliary_hodge_eq_curvature] at recovered
  calc
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 1
          (c3h181FullCurvatureCoordinateNormalForm 0) =
        c3h181FullAuxiliaryCoordinateNormalForm 0 := recovered
    _ = matterResponseOriginAuxiliaryNormalForm := by
      funext pair
      fin_cases pair <;>
        simp [matterResponseOriginAuxiliaryNormalForm,
          c3h181FullAuxiliaryCoordinateNormalForm]

private theorem liveP506Gauss_formNativePairing_self :
    formNativeP286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
      (5 / 3 : ℝ) := by
  change
    p286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge =
      (5 / 3 : ℝ)
  exact currentGaussCharge_pairing_self

private theorem liveP506_formNativePairing_zero_left
    (coordinate : P286CoordinateCarrier) :
    formNativeP286CoordinateLiePairing 0 coordinate = 0 := by
  unfold formNativeP286CoordinateLiePairing formNativeP286LiePairing
  simp [specialUnitaryLiePairing, hyperchargeLiePairing]

private theorem live_gaugeDensity_coordinate
    (coframe : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        LiveContact coframe =
      formNativeP286GaugeCoordinateWedgeCoefficient
          liveGaugeAuxiliaryCoordinates liveGaugeCurvatureCoordinates -
        (1 / 2 : ℝ) *
          formNativeP286GaugeCoordinateWedgeCoefficient
            liveGaugeAuxiliaryCoordinates
            (formNativeP286CoordinateBlockwiseConstitutive coframe
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
              liveGaugeAuxiliaryCoordinates) := by
  unfold diracDualFormNativeCoframeGaugeDensity
  rw [generatedFormNativeGaugeDensityAtBoundary_eq_p286,
    formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual,
    formNativeP286GaugeCoordinateWedgeCoefficient_eq_actual]
  simp [liveGaugeAuxiliaryCoordinates, liveGaugeCurvatureCoordinates,
    formNativeP286CoordinateBlockwiseConstitutive, withCoframe]

/-- Arbitrary-coframe gauge-density normal form for the public fixed live
contact.  The private coordinate helpers are eliminated in favor of the
authoritative fixed P506/L0 auxiliary and curvature normal forms. -/
theorem fixedP506L0HessianLiveContact_gaugeDensity_normalForm
    (coframe : LorentzianCoframe) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        fixedP506L0HessianLiveContact coframe =
      formNativeP286GaugeCoordinateWedgeCoefficient
          matterResponseOriginAuxiliaryNormalForm
          matterResponseOriginCurvatureNormalForm -
        (1 / 2 : ℝ) *
          formNativeP286GaugeCoordinateWedgeCoefficient
            matterResponseOriginAuxiliaryNormalForm
            (formNativeP286CoordinateBlockwiseConstitutive coframe
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
              ((sourceGeneratedUnifiedCouplings
                positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
              matterResponseOriginAuxiliaryNormalForm) := by
  rw [live_gaugeDensity_coordinate,
    liveGaugeAuxiliaryCoordinates_normalForm,
    liveGaugeCurvatureCoordinates_normalForm]

private def spatialDiagonal11CoframeVariation : LorentzianCoframe :=
  coframeCoordinateDirection 1 1

private def spatialDiagonal11CoframePath
    (parameter : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![(1 : ℝ), 1 + parameter, 1, 1]

@[simp] private theorem spatialDiagonal11CoframePath_det
    (parameter : ℝ) :
    Matrix.det (spatialDiagonal11CoframePath parameter) = 1 + parameter := by
  rw [spatialDiagonal11CoframePath, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

private theorem spatialDiagonal11CoframePath_inverse
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    (spatialDiagonal11CoframePath parameter)⁻¹ =
      Matrix.diagonal ![(1 : ℝ), (1 + parameter)⁻¹, 1, 1] := by
  apply Matrix.inv_eq_left_inv
  unfold spatialDiagonal11CoframePath
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      nonzero]

private theorem spatialDiagonal11CoframePath_eq_identity_add
    (parameter : ℝ) :
    spatialDiagonal11CoframePath parameter =
      (1 : LorentzianCoframe) +
        parameter • spatialDiagonal11CoframeVariation := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spatialDiagonal11CoframePath,
      spatialDiagonal11CoframeVariation,
      Matrix.diagonal_apply, Matrix.one_apply,
      coframeCoordinateDirection]

private theorem live_gaugeDensity_spatialDiagonal11
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        LiveContact (spatialDiagonal11CoframePath parameter) =
      (5 / 54 : ℝ) - (5 / 108 : ℝ) / (1 + parameter) := by
  rw [live_gaugeDensity_coordinate,
    liveGaugeAuxiliaryCoordinates_normalForm,
    liveGaugeCurvatureCoordinates_normalForm,
    liveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [spatialDiagonal11CoframePath_inverse parameter nonzero]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    spatialDiagonal11CoframePath, Matrix.diagonal_apply,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    liveP506_formNativePairing_zero_left,
    liveP506Gauss_formNativePairing_self,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul, nonzero]
  field_simp [nonzero]
  ring

private def spatialDiagonal22CoframeVariation : LorentzianCoframe :=
  coframeCoordinateDirection 2 2

private def spatialDiagonal22CoframePath
    (parameter : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![(1 : ℝ), 1, 1 + parameter, 1]

@[simp] private theorem spatialDiagonal22CoframePath_det
    (parameter : ℝ) :
    Matrix.det (spatialDiagonal22CoframePath parameter) = 1 + parameter := by
  rw [spatialDiagonal22CoframePath, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

private theorem spatialDiagonal22CoframePath_inverse
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    (spatialDiagonal22CoframePath parameter)⁻¹ =
      Matrix.diagonal ![(1 : ℝ), 1, (1 + parameter)⁻¹, 1] := by
  apply Matrix.inv_eq_left_inv
  unfold spatialDiagonal22CoframePath
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      nonzero]

private theorem spatialDiagonal22CoframePath_eq_identity_add
    (parameter : ℝ) :
    spatialDiagonal22CoframePath parameter =
      (1 : LorentzianCoframe) +
        parameter • spatialDiagonal22CoframeVariation := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spatialDiagonal22CoframePath,
      spatialDiagonal22CoframeVariation,
      Matrix.diagonal_apply, Matrix.one_apply,
      coframeCoordinateDirection]

private theorem live_gaugeDensity_spatialDiagonal22
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        LiveContact (spatialDiagonal22CoframePath parameter) =
      (5 / 54 : ℝ) - (5 / 108 : ℝ) * (1 + parameter) := by
  rw [live_gaugeDensity_coordinate,
    liveGaugeAuxiliaryCoordinates_normalForm,
    liveGaugeCurvatureCoordinates_normalForm,
    liveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [spatialDiagonal22CoframePath_inverse parameter nonzero]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    spatialDiagonal22CoframePath, Matrix.diagonal_apply,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    liveP506_formNativePairing_zero_left,
    liveP506Gauss_formNativePairing_self,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul, nonzero]
  field_simp [nonzero]
  ring

private def spatialDiagonal33CoframeVariation : LorentzianCoframe :=
  coframeCoordinateDirection 3 3

private def spatialDiagonal33CoframePath
    (parameter : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![(1 : ℝ), 1, 1, 1 + parameter]

@[simp] private theorem spatialDiagonal33CoframePath_det
    (parameter : ℝ) :
    Matrix.det (spatialDiagonal33CoframePath parameter) = 1 + parameter := by
  rw [spatialDiagonal33CoframePath, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

private theorem spatialDiagonal33CoframePath_inverse
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    (spatialDiagonal33CoframePath parameter)⁻¹ =
      Matrix.diagonal ![(1 : ℝ), 1, 1, (1 + parameter)⁻¹] := by
  apply Matrix.inv_eq_left_inv
  unfold spatialDiagonal33CoframePath
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      nonzero]

private theorem spatialDiagonal33CoframePath_eq_identity_add
    (parameter : ℝ) :
    spatialDiagonal33CoframePath parameter =
      (1 : LorentzianCoframe) +
        parameter • spatialDiagonal33CoframeVariation := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spatialDiagonal33CoframePath,
      spatialDiagonal33CoframeVariation,
      Matrix.diagonal_apply, Matrix.one_apply,
      coframeCoordinateDirection]

private theorem live_gaugeDensity_spatialDiagonal33
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
        LiveContact (spatialDiagonal33CoframePath parameter) =
      (5 / 54 : ℝ) - (5 / 108 : ℝ) * (1 + parameter) := by
  rw [live_gaugeDensity_coordinate,
    liveGaugeAuxiliaryCoordinates_normalForm,
    liveGaugeCurvatureCoordinates_normalForm,
    liveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [spatialDiagonal33CoframePath_inverse parameter nonzero]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    spatialDiagonal33CoframePath, Matrix.diagonal_apply,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    liveP506_formNativePairing_zero_left,
    liveP506Gauss_formNativePairing_self,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul, nonzero]
  field_simp [nonzero]
  ring

private theorem diagonalPath_regular_eventually :
    ∀ᶠ parameter : ℝ in nhds 0, 1 + parameter ≠ 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show (0 : ℝ) < 1 by norm_num)] with parameter inBall
  have absLt : |parameter| < 1 := by
    simpa [Real.dist_eq] using inBall
  rcases abs_lt.mp absLt with ⟨lower, _upper⟩
  linarith

private theorem live_gaugeDensity_spatialDiagonal11_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
          LiveContact (spatialDiagonal11CoframePath parameter))
      (5 / 108 : ℝ) 0 := by
  have denominator : HasDerivAt (fun parameter : ℝ => 1 + parameter) 1 0 := by
    simpa [add_comm] using
      (hasDerivAt_id (x := (0 : ℝ))).const_add 1
  have inverse := denominator.inv (show 1 + (0 : ℝ) ≠ 0 by norm_num)
  have quotient := inverse.const_mul (5 / 108 : ℝ)
  have rationalDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          (5 / 54 : ℝ) - (5 / 108 : ℝ) / (1 + parameter))
        (5 / 108 : ℝ) 0 := by
    simpa [div_eq_mul_inv] using quotient.const_sub (5 / 54 : ℝ)
  apply rationalDerivative.congr_of_eventuallyEq
  filter_upwards [diagonalPath_regular_eventually] with parameter nonzero
  exact live_gaugeDensity_spatialDiagonal11 parameter nonzero

private theorem live_gaugeDensity_spatialDiagonal22_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
          LiveContact (spatialDiagonal22CoframePath parameter))
      (-(5 / 108 : ℝ)) 0 := by
  have affineDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          (5 / 54 : ℝ) - (5 / 108 : ℝ) * (1 + parameter))
        (-(5 / 108 : ℝ)) 0 := by
    have affine : HasDerivAt (fun parameter : ℝ => 1 + parameter) 1 0 := by
      simpa [add_comm] using
        (hasDerivAt_id (x := (0 : ℝ))).const_add 1
    have scaled := affine.const_mul (5 / 108 : ℝ)
    have assembled := scaled.const_sub (5 / 54 : ℝ)
    norm_num at assembled ⊢
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using assembled
  apply affineDerivative.congr_of_eventuallyEq
  filter_upwards [diagonalPath_regular_eventually] with parameter nonzero
  exact live_gaugeDensity_spatialDiagonal22 parameter nonzero

private theorem live_gaugeDensity_spatialDiagonal33_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity positiveSmoothUnifiedSource
          LiveContact (spatialDiagonal33CoframePath parameter))
      (-(5 / 108 : ℝ)) 0 := by
  have affineDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          (5 / 54 : ℝ) - (5 / 108 : ℝ) * (1 + parameter))
        (-(5 / 108 : ℝ)) 0 := by
    have affine : HasDerivAt (fun parameter : ℝ => 1 + parameter) 1 0 := by
      simpa [add_comm] using
        (hasDerivAt_id (x := (0 : ℝ))).const_add 1
    have scaled := affine.const_mul (5 / 108 : ℝ)
    have assembled := scaled.const_sub (5 / 54 : ℝ)
    norm_num at assembled ⊢
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using assembled
  apply affineDerivative.congr_of_eventuallyEq
  filter_upwards [diagonalPath_regular_eventually] with parameter nonzero
  exact live_gaugeDensity_spatialDiagonal33 parameter nonzero

private theorem live_stress_apply_of_spatialDiagonal11Path_hasDerivAt
    (density : LorentzianCoframe → ℝ)
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (outer : HasFDerivAt density stress (1 : LorentzianCoframe))
    (value : ℝ)
    (pathDerivative :
      HasDerivAt (fun parameter : ℝ =>
        density (spatialDiagonal11CoframePath parameter)) value 0) :
    stress spatialDiagonal11CoframeVariation = value := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const spatialDiagonal11CoframeVariation
  have variationDerivativeValue :
      (1 : ℝ) • spatialDiagonal11CoframeVariation =
        spatialDiagonal11CoframeVariation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have affineDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • spatialDiagonal11CoframeVariation := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 affineDerivative baseEquality
  have derivativeEquality := composed.unique (by
    simpa [spatialDiagonal11CoframePath_eq_identity_add,
      Function.comp_def] using pathDerivative)
  exact derivativeEquality

private theorem live_stress_apply_of_spatialDiagonal22Path_hasDerivAt
    (density : LorentzianCoframe → ℝ)
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (outer : HasFDerivAt density stress (1 : LorentzianCoframe))
    (value : ℝ)
    (pathDerivative :
      HasDerivAt (fun parameter : ℝ =>
        density (spatialDiagonal22CoframePath parameter)) value 0) :
    stress spatialDiagonal22CoframeVariation = value := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const spatialDiagonal22CoframeVariation
  have variationDerivativeValue :
      (1 : ℝ) • spatialDiagonal22CoframeVariation =
        spatialDiagonal22CoframeVariation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have affineDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • spatialDiagonal22CoframeVariation := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 affineDerivative baseEquality
  have derivativeEquality := composed.unique (by
    simpa [spatialDiagonal22CoframePath_eq_identity_add,
      Function.comp_def] using pathDerivative)
  exact derivativeEquality

private theorem live_stress_apply_of_spatialDiagonal33Path_hasDerivAt
    (density : LorentzianCoframe → ℝ)
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (outer : HasFDerivAt density stress (1 : LorentzianCoframe))
    (value : ℝ)
    (pathDerivative :
      HasDerivAt (fun parameter : ℝ =>
        density (spatialDiagonal33CoframePath parameter)) value 0) :
    stress spatialDiagonal33CoframeVariation = value := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const spatialDiagonal33CoframeVariation
  have variationDerivativeValue :
      (1 : ℝ) • spatialDiagonal33CoframeVariation =
        spatialDiagonal33CoframeVariation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have affineDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • spatialDiagonal33CoframeVariation := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 affineDerivative baseEquality
  have derivativeEquality := composed.unique (by
    simpa [spatialDiagonal33CoframePath_eq_identity_add,
      Function.comp_def] using pathDerivative)
  exact derivativeEquality

theorem live_gaugeEuler_spatialDiagonal11 :
    diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource LiveContact
        spatialDiagonal11CoframeVariation = (5 / 108 : ℝ) := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_spatialDiagonal11Path_hasDerivAt
    (diracDualFormNativeCoframeGaugeDensity
      positiveSmoothUnifiedSource LiveContact)
    (diracDualFormNativeCoframeGaugeEulerCovector
      positiveSmoothUnifiedSource LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
          positiveSmoothUnifiedSource LiveContact nondegenerate)
    (5 / 108 : ℝ) live_gaugeDensity_spatialDiagonal11_hasDerivAt

theorem live_gaugeEuler_spatialDiagonal22 :
    diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource LiveContact
        spatialDiagonal22CoframeVariation = -(5 / 108 : ℝ) := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_spatialDiagonal22Path_hasDerivAt
    (diracDualFormNativeCoframeGaugeDensity
      positiveSmoothUnifiedSource LiveContact)
    (diracDualFormNativeCoframeGaugeEulerCovector
      positiveSmoothUnifiedSource LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
          positiveSmoothUnifiedSource LiveContact nondegenerate)
    (-(5 / 108 : ℝ)) live_gaugeDensity_spatialDiagonal22_hasDerivAt

theorem live_gaugeEuler_spatialDiagonal33 :
    diracDualFormNativeCoframeGaugeEulerCovector
        positiveSmoothUnifiedSource LiveContact
        spatialDiagonal33CoframeVariation = -(5 / 108 : ℝ) := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_spatialDiagonal33Path_hasDerivAt
    (diracDualFormNativeCoframeGaugeDensity
      positiveSmoothUnifiedSource LiveContact)
    (diracDualFormNativeCoframeGaugeEulerCovector
      positiveSmoothUnifiedSource LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
          positiveSmoothUnifiedSource LiveContact nondegenerate)
    (-(5 / 108 : ℝ)) live_gaugeDensity_spatialDiagonal33_hasDerivAt

theorem current_identityECLoad_spatialDiagonal22_reduction :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 2 2) =
      -(329 / 108 : ℝ) +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 2 2) := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 2 2) +
        diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource LiveContact
          (coframeCoordinateDirection 2 2) +
      diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 2 2) = _
  have intrinsic :
      identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 2 2) = -(3 : ℝ) := by
    simp +decide [identityDiracDualECIntrinsicIIPlusObservation,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, coframeWedge,
      internalBivectorDual, lorentzianCoframeHodge,
      gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond, Matrix.one_apply,
      Fin.sum_univ_six]
    ring
  rw [intrinsic,
    show coframeCoordinateDirection 2 2 =
        spatialDiagonal22CoframeVariation by rfl,
    live_gaugeEuler_spatialDiagonal22]
  ring

theorem fixedMatterSpatialKinetic_one :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 1)
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm
                positiveDiracDualCartanContorsionNormalForm) 1)
            diracSpinTwoMatterProbe))).re = 0 := by
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

theorem fixedMatterSpatialKinetic_two :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 2)
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm
                positiveDiracDualCartanContorsionNormalForm) 2)
            diracSpinTwoMatterProbe))).re = 0 := by
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

theorem fixedMatterSpatialKinetic_three :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 3)
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm
                positiveDiracDualCartanContorsionNormalForm) 3)
            diracSpinTwoMatterProbe))).re = -(1 / 8 : ℝ) := by
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  norm_num

theorem fixedMatterTemporalConnectionKinetic :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 0)
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm
                positiveDiracDualCartanContorsionNormalForm) 0)
            diracSpinTwoMatterProbe))).re = (1 / 8 : ℝ) := by
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  norm_num

private def liveSpatialKineticOneVector : DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 1)
      (LiveContact.matterCovariantDerivative 1)

private def liveSpatialKineticTwoVector : DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 2)
      (LiveContact.matterCovariantDerivative 2)

private def liveSpatialKineticThreeVector : DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 3)
      (LiveContact.matterCovariantDerivative 3)

private def liveSpatialKineticOne : ℝ :=
  (LiveContact.conjugateMatter liveSpatialKineticOneVector).re

private def liveSpatialKineticTwo : ℝ :=
  (LiveContact.conjugateMatter liveSpatialKineticTwoVector).re

private def liveSpatialKineticThree : ℝ :=
  (LiveContact.conjugateMatter liveSpatialKineticThreeVector).re

private theorem liveSpatialKineticOne_eq_zero :
    liveSpatialKineticOne = 0 := by
  unfold liveSpatialKineticOne liveSpatialKineticOneVector
  rw [liveContact_conjugateMatter_eq_fixedP506JointActual,
    liveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin,
    show holonomicMatterCovariantDerivative FixedP506JointActual 0 1 =
        diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              positiveDiracDualCartanContorsionNormalForm) 1)
          diracSpinTwoMatterProbe by
      simpa using
        fixedP506JointActual_spatialCovariantDerivative_normalForm
          (0 : Fin 3)]
  exact fixedMatterSpatialKinetic_one

private theorem liveSpatialKineticTwo_eq_zero :
    liveSpatialKineticTwo = 0 := by
  unfold liveSpatialKineticTwo liveSpatialKineticTwoVector
  rw [liveContact_conjugateMatter_eq_fixedP506JointActual,
    liveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin,
    show holonomicMatterCovariantDerivative FixedP506JointActual 0 2 =
        diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              positiveDiracDualCartanContorsionNormalForm) 2)
          diracSpinTwoMatterProbe by
      simpa using
        fixedP506JointActual_spatialCovariantDerivative_normalForm
          (1 : Fin 3)]
  exact fixedMatterSpatialKinetic_two

private theorem liveSpatialKineticThree_eq :
    liveSpatialKineticThree = -(1 / 8 : ℝ) := by
  unfold liveSpatialKineticThree liveSpatialKineticThreeVector
  rw [liveContact_conjugateMatter_eq_fixedP506JointActual,
    liveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin,
    show holonomicMatterCovariantDerivative FixedP506JointActual 0 3 =
        diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm
              positiveDiracDualCartanContorsionNormalForm) 3)
          diracSpinTwoMatterProbe by
      simpa using
        fixedP506JointActual_spatialCovariantDerivative_normalForm
          (2 : Fin 3)]
  exact fixedMatterSpatialKinetic_three

private theorem inverseCoframeDiracGamma_spatialDiagonal11CoframePath
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := spatialDiagonal11CoframePath parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0,
        (((1 + parameter)⁻¹ : ℝ) : ℂ) • diracGamma 1,
        diracGamma 2, diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [spatialDiagonal11CoframePath_inverse parameter nonzero]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.diagonal_apply, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four]

private theorem inverseCoframeDiracGamma_spatialDiagonal22CoframePath
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := spatialDiagonal22CoframePath parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0, diracGamma 1,
        (((1 + parameter)⁻¹ : ℝ) : ℂ) • diracGamma 2,
        diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [spatialDiagonal22CoframePath_inverse parameter nonzero]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.diagonal_apply, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four]

private theorem inverseCoframeDiracGamma_spatialDiagonal33CoframePath
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := spatialDiagonal33CoframePath parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0, diracGamma 1, diracGamma 2,
        (((1 + parameter)⁻¹ : ℝ) : ℂ) • diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [spatialDiagonal33CoframePath_inverse parameter nonzero]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.diagonal_apply, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four]

private theorem live_repairedMatterVector_base_zero :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact 1) = 0 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    generatedContinuumDiracDualYukawaVector
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart]
  rw [liveContact_matterCovariantDerivative_eq_fixedP506JointActual,
    liveContact_scalar_eq_fixedP506JointActual,
    liveContact_matter_eq_fixedP506JointActual]
  have actual := fixedP506JointActual_repairedMatterVector_origin_zero
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    generatedContinuumDiracDualYukawaVector at actual
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart] at actual
  rw [fixedP506JointActual_coframe_origin_one] at actual
  exact actual

private theorem live_repairedMatterVector_spatialDiagonal11
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal11CoframePath parameter)) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe LiveContact 1) +
        (((((1 + parameter)⁻¹ : ℝ) : ℂ) - 1) •
          liveSpatialKineticOneVector) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_spatialDiagonal11CoframePath
    parameter nonzero]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveSpatialKineticOneVector
    generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four]
  simp [Matrix.cons_val]
  rw [diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_smul]
  module

private theorem live_repairedMatterVector_spatialDiagonal22
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal22CoframePath parameter)) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe LiveContact 1) +
        (((((1 + parameter)⁻¹ : ℝ) : ℂ) - 1) •
          liveSpatialKineticTwoVector) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_spatialDiagonal22CoframePath
    parameter nonzero]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveSpatialKineticTwoVector
    generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four]
  simp [Matrix.cons_val]
  rw [diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_smul]
  module

private theorem live_repairedMatterVector_spatialDiagonal33
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal33CoframePath parameter)) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe LiveContact 1) +
        (((((1 + parameter)⁻¹ : ℝ) : ℂ) - 1) •
          liveSpatialKineticThreeVector) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_spatialDiagonal33CoframePath
    parameter nonzero]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveSpatialKineticThreeVector
    generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four]
  simp [Matrix.cons_val]
  rw [diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_smul]
  module

private theorem live_scalarDensity_spatialDiagonal11_zero
    (parameter : ℝ) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal11CoframePath parameter)) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity
  simp only [withCoframe]
  rw [liveContact_scalarCovariantDerivative_eq_fixedP506JointActual,
    liveContact_scalar_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  have derivativeZero :
      holonomicScalarCovariantDerivative FixedP506JointActual 0 = 0 := by
    funext direction
    exact fixedP506JointActual_scalarCovariantDerivative_origin_zero direction
  rw [derivativeZero, fixedP506JointActual_scalar_origin]
  simp [generatedScalarKineticDensity,
    scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe,
    generatedScalarPotential, scalarCoordinateSquaredNorm]

private theorem live_scalarDensity_spatialDiagonal22_zero
    (parameter : ℝ) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal22CoframePath parameter)) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity
  simp only [withCoframe]
  rw [liveContact_scalarCovariantDerivative_eq_fixedP506JointActual,
    liveContact_scalar_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  have derivativeZero :
      holonomicScalarCovariantDerivative FixedP506JointActual 0 = 0 := by
    funext direction
    exact fixedP506JointActual_scalarCovariantDerivative_origin_zero direction
  rw [derivativeZero, fixedP506JointActual_scalar_origin]
  simp [generatedScalarKineticDensity,
    scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe,
    generatedScalarPotential, scalarCoordinateSquaredNorm]

private theorem live_scalarDensity_spatialDiagonal33_zero
    (parameter : ℝ) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal33CoframePath parameter)) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity
  simp only [withCoframe]
  rw [liveContact_scalarCovariantDerivative_eq_fixedP506JointActual,
    liveContact_scalar_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  have derivativeZero :
      holonomicScalarCovariantDerivative FixedP506JointActual 0 = 0 := by
    funext direction
    exact fixedP506JointActual_scalarCovariantDerivative_origin_zero direction
  rw [derivativeZero, fixedP506JointActual_scalar_origin]
  simp [generatedScalarKineticDensity,
    scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe,
    generatedScalarPotential, scalarCoordinateSquaredNorm]

private theorem live_repairedMatterDensity_spatialDiagonal11
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (positive : 0 < 1 + parameter) :
    generatedDensitizedContinuumDiracDualMatterDensity
        positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal11CoframePath parameter)) = 0 := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    live_repairedMatterVector_spatialDiagonal11 parameter nonzero,
    live_repairedMatterVector_base_zero]
  simp only [withCoframe, matterDualFrameRelative_zeroChart,
    map_add, map_smul, map_zero, Complex.zero_re, Complex.add_re,
    Complex.smul_re, zero_add]
  unfold generatedVolumeDensity
  rw [spatialDiagonal11CoframePath_det, abs_of_pos positive]
  have correction :
      ((((((1 + parameter)⁻¹ : ℝ) : ℂ) - 1) •
          LiveContact.conjugateMatter liveSpatialKineticOneVector)).re =
        ((1 + parameter)⁻¹ - 1) * liveSpatialKineticOne := by
    unfold liveSpatialKineticOne
    rw [smul_eq_mul, Complex.mul_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul, sub_zero]
  rw [correction]
  change
    (1 + parameter) *
      ((((1 + parameter)⁻¹ - 1) * liveSpatialKineticOne)) = 0
  rw [liveSpatialKineticOne_eq_zero]
  ring

private theorem live_repairedMatterDensity_spatialDiagonal22
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (positive : 0 < 1 + parameter) :
    generatedDensitizedContinuumDiracDualMatterDensity
        positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal22CoframePath parameter)) = 0 := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    live_repairedMatterVector_spatialDiagonal22 parameter nonzero,
    live_repairedMatterVector_base_zero]
  simp only [withCoframe, matterDualFrameRelative_zeroChart,
    map_add, map_smul, map_zero, Complex.zero_re, Complex.add_re,
    Complex.smul_re, zero_add]
  unfold generatedVolumeDensity
  rw [spatialDiagonal22CoframePath_det, abs_of_pos positive]
  have correction :
      ((((((1 + parameter)⁻¹ : ℝ) : ℂ) - 1) •
          LiveContact.conjugateMatter liveSpatialKineticTwoVector)).re =
        ((1 + parameter)⁻¹ - 1) * liveSpatialKineticTwo := by
    unfold liveSpatialKineticTwo
    rw [smul_eq_mul, Complex.mul_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul, sub_zero]
  rw [correction]
  change
    (1 + parameter) *
      ((((1 + parameter)⁻¹ - 1) * liveSpatialKineticTwo)) = 0
  rw [liveSpatialKineticTwo_eq_zero]
  ring

private theorem live_repairedMatterDensity_spatialDiagonal33
    (parameter : ℝ) (nonzero : 1 + parameter ≠ 0)
    (positive : 0 < 1 + parameter) :
    generatedDensitizedContinuumDiracDualMatterDensity
        positiveSmoothUnifiedSource 0 0
        (withCoframe LiveContact
          (spatialDiagonal33CoframePath parameter)) =
      parameter / 8 := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    live_repairedMatterVector_spatialDiagonal33 parameter nonzero,
    live_repairedMatterVector_base_zero]
  simp only [withCoframe, matterDualFrameRelative_zeroChart,
    map_add, map_smul, map_zero, Complex.zero_re, Complex.add_re,
    Complex.smul_re, zero_add]
  unfold generatedVolumeDensity
  rw [spatialDiagonal33CoframePath_det, abs_of_pos positive]
  have correction :
      ((((((1 + parameter)⁻¹ : ℝ) : ℂ) - 1) •
          LiveContact.conjugateMatter liveSpatialKineticThreeVector)).re =
        ((1 + parameter)⁻¹ - 1) * liveSpatialKineticThree := by
    unfold liveSpatialKineticThree
    rw [smul_eq_mul, Complex.mul_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul, sub_zero]
  rw [correction]
  change
    (1 + parameter) *
      ((((1 + parameter)⁻¹ - 1) * liveSpatialKineticThree)) =
        parameter / 8
  rw [liveSpatialKineticThree_eq]
  field_simp [nonzero]
  ring

private theorem diagonalPath_regular_positive_eventually :
    ∀ᶠ parameter : ℝ in nhds 0,
      1 + parameter ≠ 0 ∧ 0 < 1 + parameter := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show (0 : ℝ) < 1 by norm_num)] with parameter inBall
  have absLt : |parameter| < 1 := by
    simpa [Real.dist_eq] using inBall
  have positive : 0 < 1 + parameter := by
    rcases abs_lt.mp absLt with ⟨lower, _upper⟩
    linarith
  exact ⟨positive.ne', positive⟩

private theorem live_matterDensity_spatialDiagonal11_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 LiveContact
          (spatialDiagonal11CoframePath parameter))
      0 0 := by
  have zeroDerivative : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 :=
    hasDerivAt_const 0 0
  apply zeroDerivative.congr_of_eventuallyEq
  filter_upwards [diagonalPath_regular_positive_eventually] with
      parameter regular
  rcases regular with ⟨nonzero, positive⟩
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_spatialDiagonal11_zero,
    live_repairedMatterDensity_spatialDiagonal11 parameter nonzero positive]
  ring

private theorem live_matterDensity_spatialDiagonal22_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 LiveContact
          (spatialDiagonal22CoframePath parameter))
      0 0 := by
  have zeroDerivative : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 :=
    hasDerivAt_const 0 0
  apply zeroDerivative.congr_of_eventuallyEq
  filter_upwards [diagonalPath_regular_positive_eventually] with
      parameter regular
  rcases regular with ⟨nonzero, positive⟩
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_spatialDiagonal22_zero,
    live_repairedMatterDensity_spatialDiagonal22 parameter nonzero positive]
  ring

private theorem live_matterDensity_spatialDiagonal33_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeMatterDensity
          positiveSmoothUnifiedSource 0 LiveContact
          (spatialDiagonal33CoframePath parameter))
      (1 / 8 : ℝ) 0 := by
  have affineDerivative :
      HasDerivAt (fun parameter : ℝ => parameter / 8)
        (1 / 8 : ℝ) 0 := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id (x := (0 : ℝ))).mul_const (8 : ℝ)⁻¹
  apply affineDerivative.congr_of_eventuallyEq
  filter_upwards [diagonalPath_regular_positive_eventually] with
      parameter regular
  rcases regular with ⟨nonzero, positive⟩
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_spatialDiagonal33_zero,
    live_repairedMatterDensity_spatialDiagonal33 parameter nonzero positive]
  ring

theorem live_matterEuler_spatialDiagonal11 :
    diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0 LiveContact
        spatialDiagonal11CoframeVariation = 0 := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_spatialDiagonal11Path_hasDerivAt
    (diracDualFormNativeCoframeMatterDensity
      positiveSmoothUnifiedSource 0 LiveContact)
    (diracDualFormNativeCoframeMatterEulerCovector
      positiveSmoothUnifiedSource 0 LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeMatterDensity_hasFDerivAt
          positiveSmoothUnifiedSource 0 LiveContact nondegenerate)
    0 live_matterDensity_spatialDiagonal11_hasDerivAt

theorem current_identityECLoad_spatialDiagonal11 :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 1 1) = -(319 / 108 : ℝ) := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 1 1) +
        diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource LiveContact
          (coframeCoordinateDirection 1 1) +
      diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 1 1) = _
  have intrinsic :
      identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 1 1) = -(3 : ℝ) := by
    simp +decide [identityDiracDualECIntrinsicIIPlusObservation,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, coframeWedge,
      internalBivectorDual, lorentzianCoframeHodge,
      gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond, Matrix.one_apply,
      Fin.sum_univ_six]
    ring
  rw [intrinsic,
    show coframeCoordinateDirection 1 1 =
        spatialDiagonal11CoframeVariation by rfl,
    live_gaugeEuler_spatialDiagonal11,
    live_matterEuler_spatialDiagonal11]
  norm_num

theorem live_matterEuler_spatialDiagonal22 :
    diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0 LiveContact
        spatialDiagonal22CoframeVariation = 0 := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_spatialDiagonal22Path_hasDerivAt
    (diracDualFormNativeCoframeMatterDensity
      positiveSmoothUnifiedSource 0 LiveContact)
    (diracDualFormNativeCoframeMatterEulerCovector
      positiveSmoothUnifiedSource 0 LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeMatterDensity_hasFDerivAt
          positiveSmoothUnifiedSource 0 LiveContact nondegenerate)
    0 live_matterDensity_spatialDiagonal22_hasDerivAt

theorem live_matterEuler_spatialDiagonal33 :
    diracDualFormNativeCoframeMatterEulerCovector
        positiveSmoothUnifiedSource 0 LiveContact
        spatialDiagonal33CoframeVariation = (1 / 8 : ℝ) := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_spatialDiagonal33Path_hasDerivAt
    (diracDualFormNativeCoframeMatterDensity
      positiveSmoothUnifiedSource 0 LiveContact)
    (diracDualFormNativeCoframeMatterEulerCovector
      positiveSmoothUnifiedSource 0 LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeMatterDensity_hasFDerivAt
          positiveSmoothUnifiedSource 0 LiveContact nondegenerate)
    (1 / 8 : ℝ) live_matterDensity_spatialDiagonal33_hasDerivAt

theorem current_identityECLoad_spatialDiagonal22 :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 2 2) = -(329 / 108 : ℝ) := by
  rw [current_identityECLoad_spatialDiagonal22_reduction,
    show coframeCoordinateDirection 2 2 =
        spatialDiagonal22CoframeVariation by rfl,
    live_matterEuler_spatialDiagonal22]
  ring

theorem current_identityECLoad_spatialDiagonal33_reduction :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 3 3) =
      -(329 / 108 : ℝ) +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 3 3) := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 3 3) +
        diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource LiveContact
          (coframeCoordinateDirection 3 3) +
      diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 3 3) = _
  have intrinsic :
      identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 3 3) = -(3 : ℝ) := by
    simp +decide [identityDiracDualECIntrinsicIIPlusObservation,
      identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, coframeWedge,
      internalBivectorDual, lorentzianCoframeHodge,
      gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond, Matrix.one_apply,
      Fin.sum_univ_six]
    ring
  rw [intrinsic,
    show coframeCoordinateDirection 3 3 =
        spatialDiagonal33CoframeVariation by rfl,
    live_gaugeEuler_spatialDiagonal33]
  ring

theorem current_identityECLoad_spatialDiagonal33 :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 3 3) = -(631 / 216 : ℝ) := by
  rw [current_identityECLoad_spatialDiagonal33_reduction,
    show coframeCoordinateDirection 3 3 =
        spatialDiagonal33CoframeVariation by rfl,
    live_matterEuler_spatialDiagonal33]
  ring

theorem hessianRows_spatialDiagonal22_reduction :
    HessianRows.1 2 2 =
      -(identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0)
          (coframeCoordinateDirection 2 2) - (329 / 108 : ℝ) +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 2 2)) := by
  have sign : minkowskiInternalSign (2 : LorentzianIndex) *
      minkowskiInternalSign (2 : LorentzianIndex) = 1 := by
    simp [minkowskiInternalSign]
  change
    (1 / 2 : ℝ) *
      (-LowerOrderRows 2 2 +
        minkowskiInternalSign 2 * minkowskiInternalSign 2 *
          (-LowerOrderRows 2 2)) = _
  rw [sign]
  have lower : LowerOrderRows 2 2 =
      identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0)
          (coframeCoordinateDirection 2 2) +
        diracDualFormNativeIdentityECLoad Source Current
          (coframeCoordinateDirection 2 2) := by
    rfl
  rw [lower, current_identityECLoad_spatialDiagonal22_reduction]
  ring

theorem hessianRows_spatialDiagonal33_reduction :
    HessianRows.1 3 3 =
      -(identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0)
          (coframeCoordinateDirection 3 3) - (329 / 108 : ℝ) +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          (coframeCoordinateDirection 3 3)) := by
  have sign : minkowskiInternalSign (3 : LorentzianIndex) *
      minkowskiInternalSign (3 : LorentzianIndex) = 1 := by
    simp [minkowskiInternalSign]
  change
    (1 / 2 : ℝ) *
      (-LowerOrderRows 3 3 +
        minkowskiInternalSign 3 * minkowskiInternalSign 3 *
          (-LowerOrderRows 3 3)) = _
  rw [sign]
  have lower : LowerOrderRows 3 3 =
      identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0)
          (coframeCoordinateDirection 3 3) +
        diracDualFormNativeIdentityECLoad Source Current
          (coframeCoordinateDirection 3 3) := by
    rfl
  rw [lower, current_identityECLoad_spatialDiagonal33_reduction]
  ring

private theorem current_gravityConnection_eq_globalPreEC :
    Current.gravityConnection =
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection := by
  change
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityConnection =
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gravityConnection
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC

private theorem current_gravityCurvature_origin_eq_globalPreEC :
    holonomicGravityCurvature Current 0 =
      holonomicGravityCurvature
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 := by
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [current_gravityConnection_eq_globalPreEC]

private theorem globalDevelopment_connection_spatialDerivative_origin_zero
    (axis : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        axis.succ formDirection internalOut internalIn = 0 := by
  by_cases differentiable : DifferentiableAt ℝ
      (fun point =>
        fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection
          point formDirection internalOut internalIn) 0
  · exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_connection_spatialDerivative_origin_zero
        axis formDirection internalOut internalIn differentiable
  · unfold gravityConnectionDerivative
    rw [fderiv_zero_of_not_differentiableAt differentiable]
    rfl

private theorem globalDevelopment_gravityConnection_origin_eq_fixedAction :
    fixedP506L0CompleteJointGlobalDevelopmentActual.gravityConnection 0 =
      fixedActionCartanConnection := by
  calc
    _ = (fixedP506L0FinalCommonActionActual 0).gravityConnection 0 :=
      fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection_origin_eq_accepted
    _ = FixedP506JointActionSuccessor.gravityConnection 0 :=
      fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_jointAction
    _ = fixedActionCartanConnection := by
      rw [fixedP506JointActionSuccessor_gravityConnection]
      exact fixedP506JointActual_connection_origin_eq_fixedAction

/-! ## Public target-free diagonal action reads -/

/-- Canonical first spatial diagonal of the generated non-gravity action
read.  The public variation is the raw coframe coordinate, not a residual or
load target. -/
theorem fixedP506CanonicalNonGravityEuler_spatialDiagonal11 :
    (diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource fixedP506L0HessianLiveContact +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 fixedP506L0HessianLiveContact)
      (coframeCoordinateDirection 1 1) = (5 / 108 : ℝ) := by
  change
    diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource LiveContact
          spatialDiagonal11CoframeVariation +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          spatialDiagonal11CoframeVariation = _
  rw [live_gaugeEuler_spatialDiagonal11,
    live_matterEuler_spatialDiagonal11]
  norm_num

theorem fixedP506CanonicalNonGravityEuler_spatialDiagonal22 :
    (diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource fixedP506L0HessianLiveContact +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 fixedP506L0HessianLiveContact)
      (coframeCoordinateDirection 2 2) = -(5 / 108 : ℝ) := by
  change
    diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource LiveContact
          spatialDiagonal22CoframeVariation +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          spatialDiagonal22CoframeVariation = _
  rw [live_gaugeEuler_spatialDiagonal22,
    live_matterEuler_spatialDiagonal22]
  norm_num

theorem fixedP506CanonicalNonGravityEuler_spatialDiagonal33 :
    (diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource fixedP506L0HessianLiveContact +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 fixedP506L0HessianLiveContact)
      (coframeCoordinateDirection 3 3) = (17 / 216 : ℝ) := by
  change
    diracDualFormNativeCoframeGaugeEulerCovector
          positiveSmoothUnifiedSource LiveContact
          spatialDiagonal33CoframeVariation +
        diracDualFormNativeCoframeMatterEulerCovector
          positiveSmoothUnifiedSource 0 LiveContact
          spatialDiagonal33CoframeVariation = _
  rw [live_gaugeEuler_spatialDiagonal33,
    live_matterEuler_spatialDiagonal33]
  norm_num

theorem intrinsic_spatialDiagonal22 :
    identityDiracDualECIntrinsicIIPlusObservation
      (coframeCoordinateDirection 2 2) = -(3 : ℝ) := by
  simp +decide [identityDiracDualECIntrinsicIIPlusObservation,
    identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, coframeWedge,
    internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
  ring

theorem intrinsic_spatialDiagonal33 :
    identityDiracDualECIntrinsicIIPlusObservation
      (coframeCoordinateDirection 3 3) = -(3 : ℝ) := by
  simp +decide [identityDiracDualECIntrinsicIIPlusObservation,
    identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, coframeWedge,
    internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianLiveDiagonalLoad
