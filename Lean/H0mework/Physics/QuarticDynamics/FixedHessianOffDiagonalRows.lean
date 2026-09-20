import H0mework.Physics.QuarticDynamics.FixedHessianPrefixedJointGlobalActual
import H0mework.Physics.QuarticDynamics.FixedHessianLiveDiagonalLoad
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyLiveStressSpatialRegularity
import H0mework.Physics.FinalJoint.FixedTimeAxisP286ResidualNormalForm

/-!
# Fixed-current off-diagonal Hessian rows

This module computes the two determinant-support coordinates `H02` and `H23`
from the fixed source/current action.  It keeps the live-contact gauge and
matter variation chain together with the public Hessian-row readout: no
determinant target or residual value is supplied to a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianOffDiagonalRows

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECGravityCurvatureTargetCoordinate
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPhysicalClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506JointActionSixSectorClosure
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisP286ResidualNormalForm
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianPrefixedCompleteJointGlobalActual
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianLiveDiagonalLoad
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineTopologicalFourFormPairing
open StageNineIIPlusRestriction
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeVariation
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfilesFixedP506Regularity
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeFixedP506CartanRestartCurvatureSpatialRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalJointLocalActualLift
open StageNineCoframeFirstJet
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeGaugeWedge
open StageNineHolonomicGaugeCurvatureTransport
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineScalarLocalSpinDensity
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open SU7ExteriorMatterRepresentation
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

local instance liveStressP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  constitutiveRegularityP286ModuleFinite

local instance liveStressP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  constitutiveRegularityP286CoordinateIndexFintype

local instance liveStressP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  constitutiveRegularityP286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev Accepted : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

private abbrev LocalPreEC : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonPreECActionActual 0

private abbrev HessianRows : IdentityECEtaCompatibleRows :=
  sourceActionGeneratedIdentityECCoframeAccelerationRows Source Current

private abbrev LowerOrderRows : LorentzianCoframe :=
  sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates Source Current

private abbrev OldContact : StageNineHolonomicConfiguration :=
  fixedCartanReactionContact 0

private abbrev OldHessian : CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement Source OldContact

theorem hessianRows_zero_two_eq_lowerOrderRows :
    HessianRows.1 0 2 =
      (LowerOrderRows 2 0 - LowerOrderRows 0 2) / 2 := by
  rw [hessianRows_coordinate_normalForm]
  have two_ne_zero : (2 : LorentzianIndex) ≠ 0 := by decide
  simp [minkowskiInternalSign, two_ne_zero]
  ring

theorem hessianRows_two_three_eq_lowerOrderRows :
    HessianRows.1 2 3 =
      -(LowerOrderRows 2 3 + LowerOrderRows 3 2) / 2 := by
  rw [hessianRows_coordinate_normalForm]
  simp [minkowskiInternalSign]

private def EtaSymmetric02Variation : LorentzianCoframe :=
  coframeCoordinateDirection 2 0 - coframeCoordinateDirection 0 2

private def SpatialSymmetric23Variation : LorentzianCoframe :=
  coframeCoordinateDirection 2 3 + coframeCoordinateDirection 3 2

private abbrev LiveContact : StageNineContinuumPointField :=
  fixedP506L0HessianLiveContact

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev SmoothComparison : StageNineHolonomicConfiguration :=
  fixedP506FormNativeRepairedSpatialMatterSmoothComparison

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem finalPreEC_pointField_origin :
    toContinuumPointField (fixedP506L0FinalCommonPreECActionActual 0) 0 =
      toContinuumPointField
        (recenteredCartanRepairedConstitutiveCurrent 0) 0 := by
  calc
    _ = toContinuumPointField
          (recenteredCartanRepairedScalarSecondJetActual 0) 0 :=
      formNativeCurrentP286CompleteActionResponseOperator_pointField_origin
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual 0)
    _ = _ := recenteredCartanRepairedScalarSecondJetActual_pointField_origin 0

@[simp] private theorem liveContact_coframe : LiveContact.coframe = 1 := by
  exact fixedP506L0HessianLiveContact_coframe

private theorem identityECLoad_eq_rawPointField
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeIdentityECLoad Source current =
      identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        diracDualFormNativeCoframeGaugeEulerCovector
          Source (toContinuumPointField current 0) +
        diracDualFormNativeCoframeMatterEulerCovector
          Source 0 (toContinuumPointField current 0) := by
  rfl

private theorem commonCoframeLoad_eq_of_nonGravityProjection_eq
    (first second : StageNineContinuumPointField)
    (projected :
      identityECNonGravityContactProjection first =
        identityECNonGravityContactProjection second) :
    diracDualFormNativeCoframeGaugeEulerCovector Source first +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 first =
      diracDualFormNativeCoframeGaugeEulerCovector Source second +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 second := by
  have gaugeDensityEquality :
      diracDualFormNativeCoframeGaugeDensity Source first =
        diracDualFormNativeCoframeGaugeDensity Source second := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        Source first,
      projected,
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection]
  have matterDensityEquality :
      diracDualFormNativeCoframeMatterDensity Source 0 first =
        diracDualFormNativeCoframeMatterDensity Source 0 second := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        Source 0 first,
      projected,
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection]
  have coframeEquality : first.coframe = second.coframe := by
    simpa [identityECNonGravityContactProjection] using
      congrArg (fun field : StageNineContinuumPointField => field.coframe)
        projected
  unfold diracDualFormNativeCoframeGaugeEulerCovector
    diracDualFormNativeCoframeMatterEulerCovector
  rw [gaugeDensityEquality, matterDensityEquality, coframeEquality]

private theorem accepted_preEC_nonGravityProjection_eq :
    identityECNonGravityContactProjection
        (toContinuumPointField Accepted 0) =
      identityECNonGravityContactProjection
        (toContinuumPointField LocalPreEC 0) := by
  apply StageNineContinuumPointField.ext <;>
    simp only [identityECNonGravityContactProjection,
      toContinuumPointField]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_coframe_eq_preEC 0) 0
  · exact holonomicGaugeCurvature_eq_of_connection_eq
      Accepted LocalPreEC
      (fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC 0) 0
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_gaugeAuxiliary 0) 0
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_scalar_eq_preEC 0) 0
  · funext direction
    unfold holonomicScalarCovariantDerivative
    rw [fixedP506L0FinalCommonActionActual_scalar_eq_preEC,
      fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_matter_eq_preEC 0) 0
  · funext direction
    unfold holonomicMatterCovariantDerivative
    rw [fixedP506L0FinalCommonActionActual_matter_eq_preEC,
      fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC,
      fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]
  · exact congrFun
      (fixedP506L0FinalCommonActionActual_conjugateMatter_eq_preEC 0) 0

private theorem accepted_identityECLoad_eq_localPreEC :
    diracDualFormNativeIdentityECLoad Source Accepted =
      diracDualFormNativeIdentityECLoad Source LocalPreEC := by
  have nonGravity :=
    commonCoframeLoad_eq_of_nonGravityProjection_eq
      (toContinuumPointField Accepted 0)
      (toContinuumPointField LocalPreEC 0)
      accepted_preEC_nonGravityProjection_eq
  calc
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector Source
            (toContinuumPointField Accepted 0) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (toContinuumPointField Accepted 0)) := by
      rw [identityECLoad_eq_rawPointField, ← add_assoc]
    _ = identityDiracDualECCurvatureObservation
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe))) +
        (diracDualFormNativeCoframeGaugeEulerCovector Source
            (toContinuumPointField LocalPreEC 0) +
          diracDualFormNativeCoframeMatterEulerCovector Source 0
            (toContinuumPointField LocalPreEC 0)) := by
      rw [nonGravity]
    _ = _ := by
      rw [identityECLoad_eq_rawPointField, ← add_assoc]

theorem current_identityECLoad_eq_accepted :
    diracDualFormNativeIdentityECLoad Source Current =
      diracDualFormNativeIdentityECLoad Source Accepted := by
  rw [current_identityECLoad_eq_localPreEC,
    accepted_identityECLoad_eq_localPreEC]

/-- A determinant-one, source-independent probe path whose tangent is the
eta-symmetric `02` variation.  It is used only to read the existing action. -/
private def EtaSymmetric02Path (parameter : ℝ) : LorentzianCoframe :=
  (1 : LorentzianCoframe) + parameter • EtaSymmetric02Variation -
    parameter ^ 2 • coframeCoordinateDirection 2 2

/-- A determinant-one probe path tangent to the spatial-symmetric `23`
variation. -/
private def SpatialSymmetric23Path (parameter : ℝ) : LorentzianCoframe :=
  (1 : LorentzianCoframe) + parameter • SpatialSymmetric23Variation +
    parameter ^ 2 • coframeCoordinateDirection 2 2

private theorem etaSymmetric02Path_eq_transvections (parameter : ℝ) :
    EtaSymmetric02Path parameter =
      Matrix.transvection (2 : Fin 4) (0 : Fin 4) parameter *
        Matrix.transvection (0 : Fin 4) (2 : Fin 4) (-parameter) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [EtaSymmetric02Path, EtaSymmetric02Variation,
      Matrix.transvection, Matrix.mul_apply, coframeCoordinateDirection,
      Fin.sum_univ_four] <;> ring

private theorem spatialSymmetric23Path_eq_transvections (parameter : ℝ) :
    SpatialSymmetric23Path parameter =
      Matrix.transvection (2 : Fin 4) (3 : Fin 4) parameter *
        Matrix.transvection (3 : Fin 4) (2 : Fin 4) parameter := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [SpatialSymmetric23Path, SpatialSymmetric23Variation,
      Matrix.transvection, Matrix.mul_apply, coframeCoordinateDirection,
      Fin.sum_univ_four] <;> ring

@[simp] private theorem etaSymmetric02Path_zero :
    EtaSymmetric02Path 0 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [EtaSymmetric02Path, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four]

@[simp] private theorem spatialSymmetric23Path_zero :
    SpatialSymmetric23Path 0 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [SpatialSymmetric23Path, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four]

@[simp] private theorem etaSymmetric02Path_det (parameter : ℝ) :
    Matrix.det (EtaSymmetric02Path parameter) = 1 := by
  rw [etaSymmetric02Path_eq_transvections, Matrix.det_mul,
    Matrix.det_transvection_of_ne (R := ℝ) (i := (2 : Fin 4))
      (j := (0 : Fin 4)) (by decide),
    Matrix.det_transvection_of_ne (R := ℝ) (i := (0 : Fin 4))
      (j := (2 : Fin 4)) (by decide)]
  norm_num

@[simp] private theorem spatialSymmetric23Path_det (parameter : ℝ) :
    Matrix.det (SpatialSymmetric23Path parameter) = 1 := by
  rw [spatialSymmetric23Path_eq_transvections, Matrix.det_mul,
    Matrix.det_transvection_of_ne (R := ℝ) (i := (2 : Fin 4))
      (j := (3 : Fin 4)) (by decide),
    Matrix.det_transvection_of_ne (R := ℝ) (i := (3 : Fin 4))
      (j := (2 : Fin 4)) (by decide)]
  norm_num

private theorem etaSymmetric02Path_inverse (parameter : ℝ) :
    (EtaSymmetric02Path parameter)⁻¹ =
      Matrix.transvection (0 : Fin 4) (2 : Fin 4) parameter *
        Matrix.transvection (2 : Fin 4) (0 : Fin 4) (-parameter) := by
  rw [etaSymmetric02Path_eq_transvections]
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [EtaSymmetric02Path, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

private theorem spatialSymmetric23Path_inverse (parameter : ℝ) :
    (SpatialSymmetric23Path parameter)⁻¹ =
      Matrix.transvection (3 : Fin 4) (2 : Fin 4) (-parameter) *
        Matrix.transvection (2 : Fin 4) (3 : Fin 4) (-parameter) := by
  rw [spatialSymmetric23Path_eq_transvections]
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [SpatialSymmetric23Path, Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

private theorem offdiagLiveP506BlockwiseCoupling_same
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

private theorem offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified
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
  simp_rw [offdiagLiveP506BlockwiseCoupling_same]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _
  module

private theorem etaSymmetric02Path_eq_polynomial (parameter : ℝ) :
    EtaSymmetric02Path parameter =
      (1 : LorentzianCoframe) + parameter • EtaSymmetric02Variation -
        parameter ^ 2 • coframeCoordinateDirection 2 2 := by
  rfl

private theorem spatialSymmetric23Path_eq_polynomial (parameter : ℝ) :
    SpatialSymmetric23Path parameter =
      (1 : LorentzianCoframe) + parameter • SpatialSymmetric23Variation +
        parameter ^ 2 • coframeCoordinateDirection 2 2 := by
  rfl

private def offDiagonalTransvectionPath
    (row column : LorentzianIndex) (parameter : ℝ) : LorentzianCoframe :=
  Matrix.transvection row column parameter

private theorem offDiagonalTransvectionPath_eq_identity_add
    (row column : LorentzianIndex) (parameter : ℝ) :
    offDiagonalTransvectionPath row column parameter =
      (1 : LorentzianCoframe) +
        parameter • coframeCoordinateDirection row column := by
  ext output input
  simp [offDiagonalTransvectionPath, Matrix.transvection,
    coframeCoordinateDirection, Matrix.one_apply]

@[simp] private theorem offDiagonalTransvectionPath_det
    (row column : LorentzianIndex) (distinct : row ≠ column)
    (parameter : ℝ) :
    Matrix.det (offDiagonalTransvectionPath row column parameter) = 1 := by
  exact Matrix.det_transvection_of_ne row column distinct parameter

private theorem offDiagonalTransvectionPath_inverse
    (row column : LorentzianIndex) (distinct : row ≠ column)
    (parameter : ℝ) :
    (offDiagonalTransvectionPath row column parameter)⁻¹ =
      Matrix.transvection row column (-parameter) := by
  apply Matrix.inv_eq_left_inv
  rw [offDiagonalTransvectionPath,
    Matrix.transvection_mul_transvection_same
      (R := ℝ) (i := row) (j := column) distinct]
  simp

private theorem live_stress_apply_of_offDiagonalTransvectionPath_hasDerivAt
    (row column : LorentzianIndex)
    (density : LorentzianCoframe → ℝ)
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (outer : HasFDerivAt density stress (1 : LorentzianCoframe))
    (value : ℝ)
    (pathDerivative :
      HasDerivAt (fun parameter : ℝ =>
        density (offDiagonalTransvectionPath row column parameter)) value 0) :
    stress (coframeCoordinateDirection row column) = value := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const (coframeCoordinateDirection row column)
  have variationDerivativeValue :
      (1 : ℝ) • coframeCoordinateDirection row column =
        coframeCoordinateDirection row column := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have affineDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • coframeCoordinateDirection row column := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 affineDerivative baseEquality
  have derivativeEquality := composed.unique (by
    simpa [offDiagonalTransvectionPath_eq_identity_add,
      Function.comp_def] using pathDerivative)
  exact derivativeEquality

/-- The `02` determinant row consumes one eta-symmetric action variation,
not two independently selected coordinates. -/
theorem lowerOrderRows_zero_two_combination_eq_actionResidual :
    LowerOrderRows 2 0 - LowerOrderRows 0 2 =
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
        EtaSymmetric02Variation := by
  change
    (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
          (coframeCoordinateDirection 2 0) -
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
          (coframeCoordinateDirection 0 2) = _
  simpa [EtaSymmetric02Variation] using
    (map_sub
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
      (coframeCoordinateDirection 2 0)
      (coframeCoordinateDirection 0 2)).symm

/-- The `23` determinant row likewise consumes one spatial-symmetric action
variation on the same source/current occurrence. -/
theorem lowerOrderRows_two_three_combination_eq_actionResidual :
    LowerOrderRows 2 3 + LowerOrderRows 3 2 =
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
        SpatialSymmetric23Variation := by
  change
    (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
          (coframeCoordinateDirection 2 3) +
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
          (coframeCoordinateDirection 3 2) = _
  simpa [SpatialSymmetric23Variation] using
    (map_add
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
      (coframeCoordinateDirection 2 3)
      (coframeCoordinateDirection 3 2)).symm

theorem hessianRows_zero_two_eq_actionResidual :
    HessianRows.1 0 2 =
      (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
        EtaSymmetric02Variation / 2 := by
  rw [hessianRows_zero_two_eq_lowerOrderRows,
    lowerOrderRows_zero_two_combination_eq_actionResidual]

theorem hessianRows_two_three_eq_actionResidual :
    HessianRows.1 2 3 =
      -(identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current)
        SpatialSymmetric23Variation / 2 := by
  rw [hessianRows_two_three_eq_lowerOrderRows,
    lowerOrderRows_two_three_combination_eq_actionResidual]

theorem current_actionResidual_eq_curvatureDifference
    (variation : LorentzianCoframe) :
    (identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) +
        diracDualFormNativeIdentityECLoad Source Current) variation =
      identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Current 0) variation -
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Accepted 0) variation := by
  have acceptedZero :=
    congrArg (fun covector : LorentzianCoframe →L[ℝ] ℝ =>
      covector variation)
      (fixedP506L0FinalCommonActionActual_ECCovector_zero 0)
  simp only [add_apply, zero_apply] at acceptedZero ⊢
  rw [current_identityECLoad_eq_accepted]
  linarith

theorem hessianRows_zero_two_eq_curvatureDifference :
    HessianRows.1 0 2 =
      (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Current 0) EtaSymmetric02Variation -
        identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Accepted 0)
            EtaSymmetric02Variation) / 2 := by
  rw [hessianRows_zero_two_eq_actionResidual,
    current_actionResidual_eq_curvatureDifference]

theorem hessianRows_two_three_eq_curvatureDifference :
    HessianRows.1 2 3 =
      -(identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Current 0)
            SpatialSymmetric23Variation -
        identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Accepted 0)
            SpatialSymmetric23Variation) / 2 := by
  rw [hessianRows_two_three_eq_actionResidual,
    current_actionResidual_eq_curvatureDifference]

private theorem curvatureObservation_temporalSpatial02_probe
    (rawCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation rawCurvature
        (coframeCoordinateDirection 0 2) =
      rawCurvature 3 2 - rawCurvature 5 0 := by
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
  ring

private theorem curvatureObservation_spatialTemporal20_probe
    (rawCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation rawCurvature
        (coframeCoordinateDirection 2 0) =
      rawCurvature 0 5 - rawCurvature 2 3 := by
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
  ring

private theorem curvatureObservation_spatialSpatial23_probe
    (rawCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation rawCurvature
        (coframeCoordinateDirection 2 3) =
      -rawCurvature 2 1 - rawCurvature 4 5 := by
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
  ring

private theorem curvatureObservation_spatialSpatial32_probe
    (rawCurvature : PhysicalBivector) :
    identityDiracDualECCurvatureObservation rawCurvature
        (coframeCoordinateDirection 3 2) =
      -rawCurvature 1 2 - rawCurvature 5 4 := by
  simp +decide [identityDiracDualECCurvatureObservation,
    coframeCoordinateDirection, physicalIIPlusCoframeTangent,
    coframeWedgeTangent, internalBivectorDual, lorentzianCoframeHodge,
    gravityInternalPairVarianceNormalization,
    gravityTopologicalWedgeCoefficient,
    orientedTwoFormWedgeCoefficient_explicit, lorentzianTwoFormSign,
    minkowskiInternalSign, pairFirst, pairSecond, Matrix.one_apply,
    Fin.sum_univ_six]
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

private theorem globalDevelopment_connection_derivative_origin_zero_of_ne_time
    (direction formDirection internalOut internalIn : LorentzianIndex)
    (spatial : direction ≠ 0) :
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        direction formDirection internalOut internalIn = 0 := by
  fin_cases direction
  · exact (spatial rfl).elim
  · exact globalDevelopment_connection_spatialDerivative_origin_zero
      (0 : Fin 3) formDirection internalOut internalIn
  · exact globalDevelopment_connection_spatialDerivative_origin_zero
      (1 : Fin 3) formDirection internalOut internalIn
  · exact globalDevelopment_connection_spatialDerivative_origin_zero
      (2 : Fin 3) formDirection internalOut internalIn

private theorem existingDevelopment_connection_derivative_origin_zero_of_ne_time
    (direction formDirection internalOut internalIn : LorentzianIndex)
    (spatial : direction ≠ 0) :
    gravityConnectionDerivative ExistingActual 0
        direction formDirection internalOut internalIn = 0 := by
  exact globalDevelopment_connection_derivative_origin_zero_of_ne_time
    direction formDirection internalOut internalIn spatial

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

private theorem minkowskiInternalMetric_inv_probe :
    minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num

private theorem identityCoframeMetric_inv_probe :
    (lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ =
      minkowskiInternalMetric := by
  rw [show lorentzianMetricOfCoframe (1 : LorentzianCoframe) =
      minkowskiInternalMetric by
    simp [lorentzianMetricOfCoframe]]
  exact minkowskiInternalMetric_inv_probe

private theorem identityECSpinConnectionComponentOfCarrier_one_323
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 3 2 3
        ((1 : LorentzianCoframe), derivative) =
      derivative 3 3 2 - derivative 2 3 3 := by
  unfold identityECSpinConnectionComponentOfCarrier
    pointwiseCoframeJetOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
    PointwiseLorentzianCoframeJet.metric
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [identityCoframeMetric_inv_probe]
  simp +decide [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, minkowskiInternalMetric, Matrix.diagonal_apply,
    minkowskiInternalSign, Fin.sum_univ_four]
  ring

private theorem identityECSpinConnectionComponentOfCarrier_one_112
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 1 1 2
        ((1 : LorentzianCoframe), derivative) =
      derivative 2 1 1 - derivative 1 1 2 := by
  unfold identityECSpinConnectionComponentOfCarrier
    pointwiseCoframeJetOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
    PointwiseLorentzianCoframeJet.metric
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [identityCoframeMetric_inv_probe]
  simp +decide [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, minkowskiInternalMetric, Matrix.diagonal_apply,
    minkowskiInternalSign, Fin.sum_univ_four]

private theorem identityECSpinConnectionComponentOfCarrier_one_203
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 2 0 3
        ((1 : LorentzianCoframe), derivative) =
      (-derivative 2 0 3 - derivative 2 3 0 + derivative 3 0 2 -
          derivative 3 2 0 + derivative 0 2 3 + derivative 0 3 2) / 2 := by
  unfold identityECSpinConnectionComponentOfCarrier
    pointwiseCoframeJetOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
    PointwiseLorentzianCoframeJet.metric
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [identityCoframeMetric_inv_probe]
  simp +decide [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, minkowskiInternalMetric, Matrix.diagonal_apply,
    minkowskiInternalSign, Fin.sum_univ_four]
  ring

private theorem identityECSpinConnectionComponentOfCarrier_one_302
    (derivative : LorentzianCoframeDerivative) :
    identityECSpinConnectionComponentOfCarrier 3 0 2
        ((1 : LorentzianCoframe), derivative) =
      (-derivative 3 0 2 - derivative 3 2 0 + derivative 2 0 3 -
          derivative 2 3 0 + derivative 0 2 3 + derivative 0 3 2) / 2 := by
  unfold identityECSpinConnectionComponentOfCarrier
    pointwiseCoframeJetOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
    PointwiseLorentzianCoframeJet.leviCivitaConnection
    PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
    PointwiseLorentzianCoframeJet.metric
    PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    PointwiseLorentzianCoframeJet.metricDerivative
  rw [identityCoframeMetric_inv_probe]
  simp +decide [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, minkowskiInternalMetric, Matrix.diagonal_apply,
    minkowskiInternalSign, Fin.sum_univ_four]
  ring

private theorem inputActual_coframe_eq_primitiveDiagonal :
    InputActual.coframe =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]

private theorem fixedContact_coframe_eq_quadratic_probe :
    (fixedIdentityECHessianCartanECNormalContactActual 0).coframe =
      fun point =>
        (1 : LorentzianCoframe) +
          coframeHolonomicSecondJetQuadraticRealization OldHessian point := by
  rw [fixedIdentityECHessianCartanECNormalContactActual]
  rw [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalJointLocalActualLift_coframe]
  funext point
  change
    OldContact.coframe point +
        coframeHolonomicSecondJetQuadraticRealization OldHessian point = _
  rw [fixedCartanReactionContact_coframe_one]

private theorem inputActual_coframe_timeAxis
    (time : ℝ) :
    InputActual.coframe (canonicalCauchySlicePoint time 0) =
      (1 : LorentzianCoframe) +
        coframeHolonomicSecondJetQuadraticRealization OldHessian
          (canonicalCauchySlicePoint time 0) := by
  rw [inputActual_coframe_eq_primitiveDiagonal]
  unfold positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
  rw [primitiveDiagonalActual_coframe_slice]
  change
    (fixedIdentityECHessianCartanECNormalContactActual 0).coframe
        (canonicalCauchySlicePoint time 0) = _
  exact congrFun fixedContact_coframe_eq_quadratic_probe
    (canonicalCauchySlicePoint time 0)

private theorem deriv_alongCanonicalSlice_at
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → V)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (differentiable :
      DifferentiableAt ℝ field (canonicalCauchySlicePoint time space)) :
    deriv (fun parameter : ℝ =>
        field (canonicalCauchySlicePoint parameter space)) time =
      fieldDirectionalDerivative field
        (canonicalCauchySlicePoint time space)
        canonicalLorentzianTimeDirection := by
  let line := fun parameter : ℝ =>
    parameter • coordinateDirection canonicalLorentzianTimeDirection +
      canonicalCauchySlicePoint 0 space
  have lineDerivative :
      HasDerivAt line
        (coordinateDirection canonicalLorentzianTimeDirection) time := by
    simpa [line] using
      ((hasDerivAt_id (𝕜 := ℝ) time).smul_const
        (coordinateDirection canonicalLorentzianTimeDirection)).add_const
          (canonicalCauchySlicePoint 0 space)
  have lineAt : line time = canonicalCauchySlicePoint time space := by
    ext direction
    fin_cases direction <;>
      simp [line, canonicalCauchySlicePoint,
        canonicalLorentzianTimeDirection, coordinateDirection,
        Fin.sum_univ_three]
  have outerDerivative :
      HasFDerivAt field
        (fderiv ℝ field (canonicalCauchySlicePoint time space))
        (line time) := by
    rw [lineAt]
    exact differentiable.hasFDerivAt
  have composed := outerDerivative.comp_hasDerivAt time lineDerivative
  unfold fieldDirectionalDerivative
  rw [show
    (fun parameter : ℝ =>
      field (canonicalCauchySlicePoint parameter space)) =
      field ∘ line by
        funext parameter
        congr 1
        ext direction
        fin_cases direction <;>
          simp [line, canonicalCauchySlicePoint,
            canonicalLorentzianTimeDirection, coordinateDirection,
            Fin.sum_univ_three]]
  exact composed.deriv

private theorem canonicalTimeAxisPoint_eq_smul
    (time : ℝ) :
    canonicalCauchySlicePoint time (0 : StageNineSpatialPoint) =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      coordinateDirection, Fin.sum_univ_three]

private theorem inputActual_coframeComponent_timeAxis_normalForm
    (time : ℝ) (internal coordinate : LorentzianIndex) :
    InputActual.coframe (canonicalCauchySlicePoint time 0)
        internal coordinate =
      (1 : LorentzianCoframe) internal coordinate +
        (1 / 2 : ℝ) * time ^ 2 *
          OldHessian.1
            (coordinateDirection canonicalLorentzianTimeDirection)
            (coordinateDirection canonicalLorentzianTimeDirection)
            internal coordinate := by
  rw [congrFun (congrFun (inputActual_coframe_timeAxis time) internal)
    coordinate]
  rw [canonicalTimeAxisPoint_eq_smul]
  simp [coframeHolonomicSecondJetQuadraticRealization_apply]
  ring

private theorem inputActual_coframeComponent_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point => InputActual.coframe point internal coordinate) :=
  fixedP506FormNativeJointActionSolvedSuccessor_smooth.1 internal coordinate

private theorem inputActual_coframeComponent_temporal_timeAxis
    (time : ℝ) (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => InputActual.coframe point internal coordinate)
        (canonicalCauchySlicePoint time 0)
        canonicalLorentzianTimeDirection =
      time *
        OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection)
          internal coordinate := by
  let component : BasePoint → ℝ := fun point =>
    InputActual.coframe point internal coordinate
  have componentDifferentiable : DifferentiableAt ℝ component
      (canonicalCauchySlicePoint time 0) :=
    ((inputActual_coframeComponent_contDiff internal coordinate).differentiable
      (by simp)).differentiableAt
  rw [← deriv_alongCanonicalSlice_at component time 0
    componentDifferentiable]
  let hessianCoordinate : ℝ :=
    OldHessian.1
      (coordinateDirection canonicalLorentzianTimeDirection)
      (coordinateDirection canonicalLorentzianTimeDirection)
      internal coordinate
  have curveEquality :
      (fun parameter : ℝ =>
        component (canonicalCauchySlicePoint parameter 0)) =
      fun parameter =>
        (1 : LorentzianCoframe) internal coordinate +
          (1 / 2 : ℝ) * parameter ^ 2 * hessianCoordinate := by
    funext parameter
    exact inputActual_coframeComponent_timeAxis_normalForm
      parameter internal coordinate
  rw [curveEquality]
  have derivative : HasDerivAt
      (fun parameter : ℝ =>
        (1 : LorentzianCoframe) internal coordinate +
          (1 / 2 : ℝ) * parameter ^ 2 * hessianCoordinate)
      (time * hessianCoordinate) time := by
    have raw :=
      (hasDerivAt_const time
        ((1 : LorentzianCoframe) internal coordinate)).add
          (((hasDerivAt_id time).pow 2).const_mul
            ((1 / 2 : ℝ) * hessianCoordinate))
    change HasDerivAt
      (fun parameter : ℝ =>
        (1 : LorentzianCoframe) internal coordinate +
          ((1 / 2 : ℝ) * hessianCoordinate) * parameter ^ 2)
      (0 + ((1 / 2 : ℝ) * hessianCoordinate) *
        ((2 : ℝ) * time ^ (2 - 1) * 1)) time at raw
    rw [show
      (fun parameter : ℝ =>
        (1 : LorentzianCoframe) internal coordinate +
          (1 / 2 : ℝ) * parameter ^ 2 * hessianCoordinate) =
      (fun parameter : ℝ =>
        (1 : LorentzianCoframe) internal coordinate +
          ((1 / 2 : ℝ) * hessianCoordinate) * parameter ^ 2) by
        funext parameter
        ring]
    exact raw.congr_deriv (by norm_num; ring)
  exact derivative.deriv

private theorem inputActual_coframeComponent_temporalSecond_origin
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (fun candidate => InputActual.coframe candidate internal coordinate)
            point canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection =
      OldHessian.1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal coordinate := by
  let component : BasePoint → ℝ := fun point =>
    InputActual.coframe point internal coordinate
  let temporalField : BasePoint → ℝ := fun point =>
    fieldDirectionalDerivative component point
      canonicalLorentzianTimeDirection
  have temporalSmooth : ContDiff ℝ ∞ temporalField := by
    have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ component) :=
      (inputActual_coframeComponent_contDiff internal coordinate).fderiv_right
        (m := ∞) (by simp)
    exact derivativeSmooth.clm_apply contDiff_const
  have temporalDifferentiable : DifferentiableAt ℝ temporalField 0 :=
    (temporalSmooth.differentiable (by simp)).differentiableAt
  have origin : canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [← origin]
  rw [← deriv_alongCanonicalSlice_at temporalField 0 0 (by
    simpa only [origin] using temporalDifferentiable)]
  have curveEquality :
      (fun time : ℝ =>
        temporalField (canonicalCauchySlicePoint time 0)) =
      fun time =>
        time * OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection)
          internal coordinate := by
    funext time
    exact inputActual_coframeComponent_temporal_timeAxis
      time internal coordinate
  rw [curveEquality]
  simpa using
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const
      (OldHessian.1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal coordinate)).deriv

private theorem inputActual_coframeDerivativeComponent_contDiff
    (derivativeDirection internal coordinate : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point =>
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
          derivativeDirection internal coordinate) := by
  let component : BasePoint → ℝ := fun point =>
    InputActual.coframe point internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    inputActual_coframeComponent_contDiff internal coordinate
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      (componentSmooth.comp contDiff_snd).fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem fieldDirectionalDerivative_add_real_at_origin_local
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

private theorem fieldDirectionalDerivative_sub_real_at_origin_local
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point - second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction -
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub firstDifferentiable secondDifferentiable]
  rfl

private theorem inputActual_coframeDerivative_temporal_temporal
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            0 internal coordinate)
        0 canonicalLorentzianTimeDirection =
      OldHessian.1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal coordinate := by
  simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative,
    canonicalLorentzianTimeDirection] using
    inputActual_coframeComponent_temporalSecond_origin internal coordinate

private theorem inputActual_coframeDerivative_mixed_temporal_spatial_zero
    (axis : Fin 3) (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            axis.succ internal coordinate)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative] using
    fixed_input_coframeComponent_mixed_temporal_spatial_zero
      axis internal coordinate

private theorem inputActual_leviCivita323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 2 3
            (InputActual.coframe point,
              (holonomicCoframeFirstJetAt InputActual.coframe point).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_identityJet]
  rw [show
    (fun point =>
      (identityECCoframeJetOfDerivative
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
        ).lorentzSpinConnection 3 2 3) =
      (fun point =>
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            3 3 2 -
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            2 3 3) by
      funext point
      exact identityECSpinConnectionComponentOfCarrier_one_323 _]
  rw [fieldDirectionalDerivative_sub_real_at_origin_local _ _
    ((inputActual_coframeDerivativeComponent_contDiff 3 3 2).differentiable
      (by simp) |>.differentiableAt)
    ((inputActual_coframeDerivativeComponent_contDiff 2 3 3).differentiable
      (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            3 3 2)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using inputActual_coframeDerivative_mixed_temporal_spatial_zero
        (2 : Fin 3) 3 2,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            2 3 3)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using inputActual_coframeDerivative_mixed_temporal_spatial_zero
        (1 : Fin 3) 3 3]
  norm_num

private theorem inputActual_leviCivita112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 1 2
            (InputActual.coframe point,
              (holonomicCoframeFirstJetAt InputActual.coframe point).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_identityJet]
  rw [show
    (fun point =>
      (identityECCoframeJetOfDerivative
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
        ).lorentzSpinConnection 1 1 2) =
      (fun point =>
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            2 1 1 -
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            1 1 2) by
      funext point
      exact identityECSpinConnectionComponentOfCarrier_one_112 _]
  rw [fieldDirectionalDerivative_sub_real_at_origin_local _ _
    ((inputActual_coframeDerivativeComponent_contDiff 2 1 1).differentiable
      (by simp) |>.differentiableAt)
    ((inputActual_coframeDerivativeComponent_contDiff 1 1 2).differentiable
      (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            2 1 1)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using inputActual_coframeDerivative_mixed_temporal_spatial_zero
        (1 : Fin 3) 1 1,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            1 1 2)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using inputActual_coframeDerivative_mixed_temporal_spatial_zero
        (0 : Fin 3) 1 2]
  norm_num

private theorem inputActual_identityJet203_function :
    (fun point =>
      (identityECCoframeJetOfDerivative
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
        ).lorentzSpinConnection 2 0 3) =
      (fun point =>
        (-(holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              2 0 3 -
            (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              2 3 0 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              3 0 2 -
            (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              3 2 0 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              0 2 3 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              0 3 2) / 2) := by
  funext point
  exact identityECSpinConnectionComponentOfCarrier_one_203 _

private theorem inputActual_identityJet302_function :
    (fun point =>
      (identityECCoframeJetOfDerivative
        (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
        ).lorentzSpinConnection 3 0 2) =
      (fun point =>
        (-(holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              3 0 2 -
            (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              3 2 0 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              2 0 3 -
            (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              2 3 0 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              0 2 3 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
              0 3 2) / 2) := by
  funext point
  exact identityECSpinConnectionComponentOfCarrier_one_302 _

private theorem inputActual_identityJet203_contDiff :
    ContDiff ℝ ∞
      (fun point =>
        (identityECCoframeJetOfDerivative
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
          ).lorentzSpinConnection 2 0 3) := by
  rw [inputActual_identityJet203_function]
  exact ((((((inputActual_coframeDerivativeComponent_contDiff 2 0 3).neg.sub
      (inputActual_coframeDerivativeComponent_contDiff 2 3 0)).add
      (inputActual_coframeDerivativeComponent_contDiff 3 0 2)).sub
      (inputActual_coframeDerivativeComponent_contDiff 3 2 0)).add
      (inputActual_coframeDerivativeComponent_contDiff 0 2 3)).add
      (inputActual_coframeDerivativeComponent_contDiff 0 3 2)).div_const 2

private theorem inputActual_identityJet302_contDiff :
    ContDiff ℝ ∞
      (fun point =>
        (identityECCoframeJetOfDerivative
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
          ).lorentzSpinConnection 3 0 2) := by
  rw [inputActual_identityJet302_function]
  exact ((((((inputActual_coframeDerivativeComponent_contDiff 3 0 2).neg.sub
      (inputActual_coframeDerivativeComponent_contDiff 3 2 0)).add
      (inputActual_coframeDerivativeComponent_contDiff 2 0 3)).sub
      (inputActual_coframeDerivativeComponent_contDiff 2 3 0)).add
      (inputActual_coframeDerivativeComponent_contDiff 0 2 3)).add
      (inputActual_coframeDerivativeComponent_contDiff 0 3 2)).div_const 2

private theorem
    inputActual_leviCivita203_add_302_temporalDerivative_eq_oldHessian :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 0 3
              (InputActual.coframe point,
                (holonomicCoframeFirstJetAt InputActual.coframe point).derivative) +
            identityECSpinConnectionComponentOfCarrier 3 0 2
              (InputActual.coframe point,
                (holonomicCoframeFirstJetAt InputActual.coframe point).derivative))
        0 canonicalLorentzianTimeDirection =
      OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 2 3 +
        OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 3 2 := by
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    (fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      2 0 3)
    (fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      3 0 2)
    canonicalLorentzianTimeDirection]
  rw [fixed_input_leviCivita_component_temporalDerivative_eq_identityJet,
    fixed_input_leviCivita_component_temporalDerivative_eq_identityJet]
  rw [← fieldDirectionalDerivative_add_real_at_origin_local _ _
    ((inputActual_identityJet203_contDiff.differentiable
      (by simp)).differentiableAt)
    ((inputActual_identityJet302_contDiff.differentiable
      (by simp)).differentiableAt)
    canonicalLorentzianTimeDirection]
  rw [show
    (fun point =>
      (identityECCoframeJetOfDerivative
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
          ).lorentzSpinConnection 2 0 3 +
        (identityECCoframeJetOfDerivative
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
          ).lorentzSpinConnection 3 0 2) =
      (fun point =>
        ((holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            0 2 3 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            0 3 2) -
        ((holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            2 3 0 +
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            3 2 0)) by
      funext point
      rw [congrFun inputActual_identityJet203_function point,
        congrFun inputActual_identityJet302_function point]
      ring]
  rw [fieldDirectionalDerivative_sub_real_at_origin_local _ _
    (((inputActual_coframeDerivativeComponent_contDiff 0 2 3).add
      (inputActual_coframeDerivativeComponent_contDiff 0 3 2)).differentiable
        (by simp) |>.differentiableAt)
    (((inputActual_coframeDerivativeComponent_contDiff 2 3 0).add
      (inputActual_coframeDerivativeComponent_contDiff 3 2 0)).differentiable
        (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection]
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    ((inputActual_coframeDerivativeComponent_contDiff 0 2 3).differentiable
      (by simp) |>.differentiableAt)
    ((inputActual_coframeDerivativeComponent_contDiff 0 3 2).differentiable
      (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection]
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    ((inputActual_coframeDerivativeComponent_contDiff 2 3 0).differentiable
      (by simp) |>.differentiableAt)
    ((inputActual_coframeDerivativeComponent_contDiff 3 2 0).differentiable
      (by simp) |>.differentiableAt)
    canonicalLorentzianTimeDirection]
  rw [inputActual_coframeDerivative_temporal_temporal 2 3,
    inputActual_coframeDerivative_temporal_temporal 3 2,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            2 3 0)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using inputActual_coframeDerivative_mixed_temporal_spatial_zero
        (1 : Fin 3) 3 0,
    show fieldDirectionalDerivative
        (fun point =>
          (holonomicCoframeFirstJetAt InputActual.coframe point).derivative
            3 2 0)
        0 canonicalLorentzianTimeDirection = 0 by
      simpa using inputActual_coframeDerivative_mixed_temporal_spatial_zero
        (2 : Fin 3) 2 0]
  ring

private theorem newCartanInput_coframe_eq_input_local :
    NewCartanInput.coframe = InputActual.coframe := by
  change NewActual.coframe = InputActual.coframe
  rw [newActual_coframe_eq_profileRestart,
    profileRestartActual_coframe_eq_input]

private theorem newCartanInput_leviCivitaComponent_differentiableAt_local
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn
          (NewCartanInput.coframe point,
            (holonomicCoframeFirstJetAt NewCartanInput.coframe point
              ).derivative)) 0 := by
  rw [newCartanInput_coframe_eq_input_local]
  exact
    fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      formDirection internalOut internalIn

private theorem newCartanInput_leviCivita323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 2 3
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [newCartanInput_coframe_eq_input_local]
  exact inputActual_leviCivita323_temporalDerivative_zero

private theorem newCartanInput_leviCivita112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 1 2
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [newCartanInput_coframe_eq_input_local]
  exact inputActual_leviCivita112_temporalDerivative_zero

private theorem newCartanInput_cartanSkew323_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point)
          3 2 3) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 3 3

private theorem newCartanInput_cartanSkew112_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point)
          1 1 2) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 1 5

private theorem newCartanInput_cartanSkew323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              Source NewCartanInput point)
            3 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_temporalDerivative_zero 3 3

private theorem newCartanInput_cartanSkew112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              Source NewCartanInput point)
            1 1 2)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_temporalDerivative_zero 1 5

private theorem newCartanInput_cartanConnection323_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            Source NewCartanInput point 3 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 2 3
              (NewCartanInput.coframe point,
                (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                  ).derivative) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                Source NewCartanInput point)
              3 2 3)
        0 canonicalLorentzianTimeDirection = 0
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    (newCartanInput_leviCivitaComponent_differentiableAt_local 3 2 3)
    newCartanInput_cartanSkew323_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanInput_leviCivita323_temporalDerivative_zero,
    newCartanInput_cartanSkew323_temporalDerivative_zero]
  norm_num

private theorem newCartanInput_cartanConnection112_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            Source NewCartanInput point 1 1 2)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 1 2
              (NewCartanInput.coframe point,
                (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                  ).derivative) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                Source NewCartanInput point)
              1 1 2)
        0 canonicalLorentzianTimeDirection = 0
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    (newCartanInput_leviCivitaComponent_differentiableAt_local 1 1 2)
    newCartanInput_cartanSkew112_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanInput_leviCivita112_temporalDerivative_zero,
    newCartanInput_cartanSkew112_temporalDerivative_zero]
  norm_num

private theorem globalDevelopment_cartanConnection323_temporalDerivative_zero :
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        canonicalLorentzianTimeDirection 3 2 3 =
      0 := by
  unfold gravityConnectionDerivative
    fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact newCartanInput_cartanConnection323_temporalDerivative_zero

private theorem globalDevelopment_cartanConnection112_temporalDerivative_zero :
    gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0
        canonicalLorentzianTimeDirection 1 1 2 =
      0 := by
  unfold gravityConnectionDerivative
    fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact newCartanInput_cartanConnection112_temporalDerivative_zero

private theorem newCartanInput_leviCivita203_temporalDerivative_eq_input :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 0 3
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 0 3
            (InputActual.coframe point,
              (holonomicCoframeFirstJetAt InputActual.coframe point).derivative))
        0 canonicalLorentzianTimeDirection := by
  rw [newCartanInput_coframe_eq_input_local]

private theorem newCartanInput_leviCivita302_temporalDerivative_eq_input :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 0 2
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 0 2
            (InputActual.coframe point,
              (holonomicCoframeFirstJetAt InputActual.coframe point).derivative))
        0 canonicalLorentzianTimeDirection := by
  rw [newCartanInput_coframe_eq_input_local]

private theorem newCartanInput_cartanSkew203_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point)
          2 0 3) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 2 2

private theorem newCartanInput_cartanSkew302_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point)
          3 0 2) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 3 1

private theorem newCartanInput_cartanConnection203_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        diracDualFormNativeActionCartanConnectionAt
          Source NewCartanInput point 2 0 3) 0 := by
  change DifferentiableAt ℝ
    (fun point =>
      identityECSpinConnectionComponentOfCarrier 2 0 3
          (NewCartanInput.coframe point,
            (holonomicCoframeFirstJetAt NewCartanInput.coframe point
              ).derivative) +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point)
          2 0 3) 0
  exact (newCartanInput_leviCivitaComponent_differentiableAt_local 2 0 3).add
    newCartanInput_cartanSkew203_differentiableAt

private theorem newCartanInput_cartanConnection302_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        diracDualFormNativeActionCartanConnectionAt
          Source NewCartanInput point 3 0 2) 0 := by
  change DifferentiableAt ℝ
    (fun point =>
      identityECSpinConnectionComponentOfCarrier 3 0 2
          (NewCartanInput.coframe point,
            (holonomicCoframeFirstJetAt NewCartanInput.coframe point
              ).derivative) +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point)
          3 0 2) 0
  exact (newCartanInput_leviCivitaComponent_differentiableAt_local 3 0 2).add
    newCartanInput_cartanSkew302_differentiableAt

private theorem newCartanInput_cartanSkew203_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              Source NewCartanInput point)
            2 0 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [show
    (fun point =>
      lorentzSkewConnectionOfBivectorOneForm
        (diracDualFormNativeActionCartanContorsionAt
          Source NewCartanInput point)
        2 0 3) =
      (fun point =>
        -diracDualFormNativeActionCartanContorsionAt
          Source NewCartanInput point 2 2) by
      funext point
      simp [lorentzSkewConnectionOfBivectorOneForm,
        loweredLorentzBivectorMatrix,
        orientedLorentzBivectorBasisCoefficient,
        pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six]]
  unfold fieldDirectionalDerivative
  rw [show
    (fun point =>
      -diracDualFormNativeActionCartanContorsionAt
        Source NewCartanInput point 2 2) =
      -(fun point =>
        diracDualFormNativeActionCartanContorsionAt
          Source NewCartanInput point 2 2) by rfl]
  rw [(newCartanInput_cartanContorsion_component_differentiableAt
    2 2).hasFDerivAt.neg.fderiv]
  change
    -fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point 2 2)
        0 canonicalLorentzianTimeDirection = 0
  rw [newCartanInput_cartanContorsion_component_temporalDerivative_zero]
  norm_num

private theorem newCartanInput_cartanSkew302_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              Source NewCartanInput point)
            3 0 2)
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [show
    (fun point =>
      lorentzSkewConnectionOfBivectorOneForm
        (diracDualFormNativeActionCartanContorsionAt
          Source NewCartanInput point)
        3 0 2) =
      (fun point =>
        -diracDualFormNativeActionCartanContorsionAt
          Source NewCartanInput point 3 1) by
      funext point
      simp [lorentzSkewConnectionOfBivectorOneForm,
        loweredLorentzBivectorMatrix,
        orientedLorentzBivectorBasisCoefficient,
        pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six]]
  unfold fieldDirectionalDerivative
  rw [show
    (fun point =>
      -diracDualFormNativeActionCartanContorsionAt
        Source NewCartanInput point 3 1) =
      -(fun point =>
        diracDualFormNativeActionCartanContorsionAt
          Source NewCartanInput point 3 1) by rfl]
  rw [(newCartanInput_cartanContorsion_component_differentiableAt
    3 1).hasFDerivAt.neg.fderiv]
  change
    -fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanContorsionAt
            Source NewCartanInput point 3 1)
        0 canonicalLorentzianTimeDirection = 0
  rw [newCartanInput_cartanContorsion_component_temporalDerivative_zero]
  norm_num

private theorem
    newCartanInput_cartanConnection203_temporalDerivative_eq_leviCivita :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            Source NewCartanInput point 2 0 3)
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 0 3
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 0 3
              (NewCartanInput.coframe point,
                (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                  ).derivative) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                Source NewCartanInput point)
              2 0 3)
        0 canonicalLorentzianTimeDirection = _
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    (newCartanInput_leviCivitaComponent_differentiableAt_local 2 0 3)
    newCartanInput_cartanSkew203_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanInput_cartanSkew203_temporalDerivative_zero]
  ring

private theorem
    newCartanInput_cartanConnection302_temporalDerivative_eq_leviCivita :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            Source NewCartanInput point 3 0 2)
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 0 2
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 3 0 2
              (NewCartanInput.coframe point,
                (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                  ).derivative) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                Source NewCartanInput point)
              3 0 2)
        0 canonicalLorentzianTimeDirection = _
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    (newCartanInput_leviCivitaComponent_differentiableAt_local 3 0 2)
    newCartanInput_cartanSkew302_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanInput_cartanSkew302_temporalDerivative_zero]
  ring

private theorem
    newCartanInput_cartanConnection203_add_302_temporalDerivative_eq_oldHessian :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
              Source NewCartanInput point 2 0 3 +
            diracDualFormNativeActionCartanConnectionAt
              Source NewCartanInput point 3 0 2)
        0 canonicalLorentzianTimeDirection =
      OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 2 3 +
      OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 3 2 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            Source NewCartanInput point 2 0 3 +
          diracDualFormNativeActionCartanConnectionAt
            Source NewCartanInput point 3 0 2)
        0 canonicalLorentzianTimeDirection = _
  rw [fieldDirectionalDerivative_add_real_at_origin_local _ _
    newCartanInput_cartanConnection203_differentiableAt
    newCartanInput_cartanConnection302_differentiableAt
    canonicalLorentzianTimeDirection]
  rw [newCartanInput_cartanConnection203_temporalDerivative_eq_leviCivita,
    newCartanInput_cartanConnection302_temporalDerivative_eq_leviCivita,
    newCartanInput_leviCivita203_temporalDerivative_eq_input,
    newCartanInput_leviCivita302_temporalDerivative_eq_input]
  have inputSum :=
    inputActual_leviCivita203_add_302_temporalDerivative_eq_oldHessian
  rw [← fieldDirectionalDerivative_add_real_at_origin_local _ _
    (fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      2 0 3)
    (fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      3 0 2)
    canonicalLorentzianTimeDirection]
  exact inputSum

private theorem
    globalDevelopment_cartanConnection203_add_302_temporalDerivative_eq_oldHessian :
    gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          canonicalLorentzianTimeDirection 2 0 3 +
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0
          canonicalLorentzianTimeDirection 3 0 2 =
      OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 2 3 +
        OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 3 2 := by
  unfold gravityConnectionDerivative
    fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  change
    fieldDirectionalDerivative
          (fun point =>
            diracDualFormNativeActionCartanConnectionAt
              Source NewCartanInput point 2 0 3)
          0 canonicalLorentzianTimeDirection +
        fieldDirectionalDerivative
          (fun point =>
            diracDualFormNativeActionCartanConnectionAt
              Source NewCartanInput point 3 0 2)
          0 canonicalLorentzianTimeDirection = _
  rw [newCartanInput_cartanConnection203_temporalDerivative_eq_leviCivita,
    newCartanInput_cartanConnection302_temporalDerivative_eq_leviCivita,
    newCartanInput_leviCivita203_temporalDerivative_eq_input,
    newCartanInput_leviCivita302_temporalDerivative_eq_input]
  rw [← fieldDirectionalDerivative_add_real_at_origin_local _ _
    (fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      2 0 3)
    (fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      3 0 2)
    canonicalLorentzianTimeDirection]
  exact inputActual_leviCivita203_add_302_temporalDerivative_eq_oldHessian

private theorem oldAccelerationRows_three_two_eq_two_three :
    fixedP506L0ContactAccelerationRows 3 2 =
      fixedP506L0ContactAccelerationRows 2 3 := by
  rw [fixedAccelerationRows_coordinate_normalForm,
    fixedAccelerationRows_coordinate_normalForm]
  simp [minkowskiInternalSign]
  ring

private theorem oldHessian_timeTime_two_three_add_three_two :
    OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 2 3 +
        OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 3 2 =
      fixedP506L0ContactAccelerationRows 2 3 / 3 := by
  have forward := congrFun
    (congrFun fixedP506L0ContactCoframeHessian_timeTime_spatial_normalForm
      (1 : Fin 3)) (2 : Fin 3)
  have backward := congrFun
    (congrFun fixedP506L0ContactCoframeHessian_timeTime_spatial_normalForm
      (2 : Fin 3)) (1 : Fin 3)
  change
    OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 2 3 +
        OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 3 2 = _
  rw [show
      OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 2 3 =
        (fixedP506L0ContactAccelerationRows 2 3 +
          fixedP506L0ContactAccelerationRows 3 2) / 12 by
      simpa [OldHessian, fixedP506L0ContactCoframeHessian,
        fixedP506L0ContactTimeTimeSpatialHessianNormalForm] using forward,
    show
      OldHessian.1
          (coordinateDirection canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) 3 2 =
        (fixedP506L0ContactAccelerationRows 3 2 +
          fixedP506L0ContactAccelerationRows 2 3) / 12 by
      simpa [OldHessian, fixedP506L0ContactCoframeHessian,
        fixedP506L0ContactTimeTimeSpatialHessianNormalForm] using backward,
    oldAccelerationRows_three_two_eq_two_three]
  ring

private theorem globalPreEC_curvatureObservation_eta02_eq_temporalDerivatives :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0)
        EtaSymmetric02Variation =
      -gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 3 2 3 +
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 1 1 2 := by
  unfold EtaSymmetric02Variation
  rw [map_sub, curvatureObservation_spatialTemporal20_probe,
    curvatureObservation_temporalSpatial02_probe,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]
  unfold holonomicGravityCurvature
  dsimp only
  simp +decide [pairFirst, pairSecond]
  rw [existingDevelopment_connection_derivative_origin_zero_of_ne_time
      2 1 0 1 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      1 2 0 1 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      3 2 0 3 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      2 3 0 3 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      3 0 2 3 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      1 0 1 2 (by decide)]
  rw [globalDevelopment_gravityConnection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm]
  norm_num [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    pairFirst, pairSecond, minkowskiInternalSign,
    Fin.sum_univ_four, Fin.sum_univ_six]
  simp +decide
  ring

private theorem globalPreEC_curvatureObservation_spatial23_eq_temporalDerivatives :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0)
        SpatialSymmetric23Variation =
      gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 2 0 3 +
        gravityConnectionDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 3 0 2 := by
  unfold SpatialSymmetric23Variation
  rw [map_add, curvatureObservation_spatialSpatial23_probe,
    curvatureObservation_spatialSpatial32_probe,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]
  unfold holonomicGravityCurvature
  dsimp only
  simp +decide [pairFirst, pairSecond]
  rw [existingDevelopment_connection_derivative_origin_zero_of_ne_time
      2 0 0 3 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      1 2 3 1 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      2 1 3 1 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      3 0 0 2 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      3 1 1 2 (by decide),
    existingDevelopment_connection_derivative_origin_zero_of_ne_time
      1 3 1 2 (by decide)]
  rw [globalDevelopment_gravityConnection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm]
  norm_num [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    positiveDiracDualCartanContorsionNormalForm,
    pairFirst, pairSecond, minkowskiInternalSign,
    Fin.sum_univ_four, Fin.sum_univ_six]
  simp +decide

private theorem current_curvatureObservation_eta02_zero :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        EtaSymmetric02Variation =
      0 := by
  rw [current_gravityCurvature_origin_eq_globalPreEC,
    globalPreEC_curvatureObservation_eta02_eq_temporalDerivatives,
    show gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 3 2 3 = 0 by
      simpa [canonicalLorentzianTimeDirection] using
        globalDevelopment_cartanConnection323_temporalDerivative_zero,
    show gravityConnectionDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 1 1 2 = 0 by
      simpa [canonicalLorentzianTimeDirection] using
        globalDevelopment_cartanConnection112_temporalDerivative_zero]
  norm_num

private theorem current_curvatureObservation_spatial23_eq_oldAcceleration :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        SpatialSymmetric23Variation =
      fixedP506L0ContactAccelerationRows 2 3 / 3 := by
  rw [current_gravityCurvature_origin_eq_globalPreEC,
    globalPreEC_curvatureObservation_spatial23_eq_temporalDerivatives,
    show
      gravityConnectionDerivative
            fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 2 0 3 +
          gravityConnectionDerivative
            fixedP506L0CompleteJointGlobalDevelopmentActual 0 0 3 0 2 =
        OldHessian.1
            (coordinateDirection canonicalLorentzianTimeDirection)
            (coordinateDirection canonicalLorentzianTimeDirection) 2 3 +
          OldHessian.1
            (coordinateDirection canonicalLorentzianTimeDirection)
            (coordinateDirection canonicalLorentzianTimeDirection) 3 2 by
      simpa [canonicalLorentzianTimeDirection] using
        globalDevelopment_cartanConnection203_add_302_temporalDerivative_eq_oldHessian,
    oldHessian_timeTime_two_three_add_three_two]

private theorem intrinsic_etaSymmetric02_zero :
    identityDiracDualECIntrinsicIIPlusObservation EtaSymmetric02Variation =
      0 := by
  simp +decide [EtaSymmetric02Variation,
    identityDiracDualECIntrinsicIIPlusObservation,
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

private theorem intrinsic_spatialSymmetric23_zero :
    identityDiracDualECIntrinsicIIPlusObservation
        SpatialSymmetric23Variation = 0 := by
  simp +decide [SpatialSymmetric23Variation,
    identityDiracDualECIntrinsicIIPlusObservation,
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

private theorem intrinsic_spatial12_zero :
    identityDiracDualECIntrinsicIIPlusObservation
        (coframeCoordinateDirection 1 2) = 0 := by
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

private theorem intrinsic_temporalSpatial01_zero :
    identityDiracDualECIntrinsicIIPlusObservation
        (coframeCoordinateDirection 0 1) = 0 := by
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

private theorem intrinsic_temporalSpatial02_zero :
    identityDiracDualECIntrinsicIIPlusObservation
        (coframeCoordinateDirection 0 2) = 0 := by
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

private theorem intrinsic_spatialTemporal20_zero :
    identityDiracDualECIntrinsicIIPlusObservation
        (coframeCoordinateDirection 2 0) = 0 := by
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

theorem current_identityECLoad_eta02_reduction :
    diracDualFormNativeIdentityECLoad Source Current EtaSymmetric02Variation =
      diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
          EtaSymmetric02Variation +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
          EtaSymmetric02Variation := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation EtaSymmetric02Variation +
          diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
            EtaSymmetric02Variation +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
          EtaSymmetric02Variation = _
  rw [intrinsic_etaSymmetric02_zero]
  ring

theorem current_identityECLoad_spatial23_reduction :
    diracDualFormNativeIdentityECLoad Source Current
        SpatialSymmetric23Variation =
      diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
          SpatialSymmetric23Variation +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
          SpatialSymmetric23Variation := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          SpatialSymmetric23Variation +
          diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
            SpatialSymmetric23Variation +
        diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
          SpatialSymmetric23Variation = _
  rw [intrinsic_spatialSymmetric23_zero]
  ring

theorem current_curvatureObservation_temporalSpatial02_support :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        (coframeCoordinateDirection 0 2) =
      holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 3 2 -
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 5 0 := by
  rw [current_gravityCurvature_origin_eq_globalPreEC,
    curvatureObservation_temporalSpatial02_probe]

theorem current_curvatureObservation_spatialTemporal20_support :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        (coframeCoordinateDirection 2 0) =
      holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 0 5 -
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 2 3 := by
  rw [current_gravityCurvature_origin_eq_globalPreEC,
    curvatureObservation_spatialTemporal20_probe]

theorem current_curvatureObservation_spatialSpatial23_support :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        (coframeCoordinateDirection 2 3) =
      -holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 2 1 -
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 4 5 := by
  rw [current_gravityCurvature_origin_eq_globalPreEC,
    curvatureObservation_spatialSpatial23_probe]

theorem current_curvatureObservation_spatialSpatial32_support :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Current 0)
        (coframeCoordinateDirection 3 2) =
      -holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 1 2 -
        holonomicGravityCurvature
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 5 4 := by
  rw [current_gravityCurvature_origin_eq_globalPreEC,
    curvatureObservation_spatialSpatial32_probe]

theorem hessianRows_zero_two_exact_support :
    HessianRows.1 0 2 =
      ((holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 0 5 -
            holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 2 3 +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 2 0)) -
        (holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 3 2 -
            holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 5 0 +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 0 2))) / 2 := by
  rw [hessianRows_zero_two_eq_lowerOrderRows]
  change
    ((identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Current 0)
            (coframeCoordinateDirection 2 0) +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 2 0)) -
      (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Current 0)
            (coframeCoordinateDirection 0 2) +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 0 2))) / 2 = _
  rw [
    current_curvatureObservation_spatialTemporal20_support,
    current_curvatureObservation_temporalSpatial02_support]

theorem hessianRows_two_three_exact_support :
    HessianRows.1 2 3 =
      -((-holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 2 1 -
            holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 4 5 +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 2 3)) +
        (-holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 1 2 -
            holonomicGravityCurvature
              fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 5 4 +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 3 2))) / 2 := by
  rw [hessianRows_two_three_eq_lowerOrderRows]
  change
    -((identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Current 0)
            (coframeCoordinateDirection 2 3) +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 2 3)) +
      (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Current 0)
            (coframeCoordinateDirection 3 2) +
          diracDualFormNativeIdentityECLoad Source Current
            (coframeCoordinateDirection 3 2))) / 2 = _
  rw [
    current_curvatureObservation_spatialSpatial23_support,
    current_curvatureObservation_spatialSpatial32_support]

private theorem inverseCoframeDiracGamma_etaSymmetric02Path
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := EtaSymmetric02Path parameter, derivative := 0 }
        direction =
      ![(1 - (parameter : ℂ) ^ 2) • diracGamma 0 +
          (parameter : ℂ) • diracGamma 2,
        diracGamma 1,
        diracGamma 2 - (parameter : ℂ) • diracGamma 0,
        diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [etaSymmetric02Path_inverse]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

private theorem inverseCoframeDiracGamma_spatialSymmetric23Path
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := SpatialSymmetric23Path parameter, derivative := 0 }
        direction =
      ![diracGamma 0,
        diracGamma 1,
        diracGamma 2 - (parameter : ℂ) • diracGamma 3,
        (1 + (parameter : ℂ) ^ 2) • diracGamma 3 -
          (parameter : ℂ) • diracGamma 2] direction := by
  unfold inverseCoframeDiracGamma
  rw [spatialSymmetric23Path_inverse]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

private theorem fixedMatter_gammaZero_spatialTwo_kinetic_zero :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 0)
          (holonomicMatterCovariantDerivative
            FixedP506JointActual 0 2))).re = 0 := by
  have spatial :=
    fixedP506JointActual_spatialCovariantDerivative_normalForm (1 : Fin 3)
  change holonomicMatterCovariantDerivative FixedP506JointActual 0 2 = _
    at spatial
  rw [spatial]
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

private theorem fixedP506JointActual_temporalCovariantDerivative_normalForm_local :
    holonomicMatterCovariantDerivative FixedP506JointActual 0 0 =
      diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm
            positiveDiracDualCartanContorsionNormalForm)
          0)
        diracSpinTwoMatterProbe := by
  have gaugeZero : FixedP506JointActual.gaugeConnection 0 0 = 0 := by
    apply p286CoordinateEquiv.injective
    rw [map_zero]
    change holonomicP286GaugeConnectionCoordinate
      FixedP506JointActual 0 0 = 0
    rw [congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero 0]
    simp
  unfold holonomicMatterCovariantDerivative
  rw [show fieldDirectionalDerivative
      (fun point => matterCoordinateEquiv (FixedP506JointActual.matter point))
      0 0 = 0 by
    simpa [canonicalLorentzianTimeDirection] using
      fixedP506JointActual_matterCoordinate_temporalDerivative_zero,
    fixedP506JointActual_connection_origin_eq_fixedAction,
    fixedActionCartanConnection_eq_positiveNormalForm,
    fixedP506JointActual_matter_origin, gaugeZero]
  simp

private theorem fixedMatter_gammaOne_temporal_kinetic_zero :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 1)
          (holonomicMatterCovariantDerivative
            FixedP506JointActual 0 0))).re = 0 := by
  rw [fixedP506JointActual_temporalCovariantDerivative_normalForm_local]
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

private theorem fixedMatter_gammaTwo_temporal_kinetic_zero :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 2)
          (holonomicMatterCovariantDerivative
            FixedP506JointActual 0 0))).re = 0 := by
  rw [fixedP506JointActual_temporalCovariantDerivative_normalForm_local]
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

private theorem fixedMatter_gammaThree_spatialTwo_kinetic_zero :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 3)
          (holonomicMatterCovariantDerivative
            FixedP506JointActual 0 2))).re = 0 := by
  have spatial :=
    fixedP506JointActual_spatialCovariantDerivative_normalForm (1 : Fin 3)
  change holonomicMatterCovariantDerivative FixedP506JointActual 0 2 = _
    at spatial
  rw [spatial]
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

private theorem fixedMatter_gammaTwo_spatialThree_kinetic_zero :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 2)
          (holonomicMatterCovariantDerivative
            FixedP506JointActual 0 3))).re = 0 := by
  have spatial :=
    fixedP506JointActual_spatialCovariantDerivative_normalForm (2 : Fin 3)
  change holonomicMatterCovariantDerivative FixedP506JointActual 0 3 = _
    at spatial
  rw [spatial]
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

private theorem fixedMatter_gammaTwo_spatialOne_kinetic_zero :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        diracMatrixMatterAction (diracGamma 2)
          (holonomicMatterCovariantDerivative
            FixedP506JointActual 0 1))).re = 0 := by
  have spatial :=
    fixedP506JointActual_spatialCovariantDerivative_normalForm (0 : Fin 3)
  change holonomicMatterCovariantDerivative FixedP506JointActual 0 1 = _
    at spatial
  rw [spatial]
  conv_lhs =>
    simp [positiveDiracDualCartanContorsionNormalForm,
      diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracSpinZeroMatterCoordinate,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

private def liveGammaKineticVector
    (gamma : DiracMatrix)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction gamma
      (LiveContact.matterCovariantDerivative direction)

private def liveGammaKineticReal
    (gamma : DiracMatrix)
    (direction : LorentzianIndex) : ℝ :=
  (LiveContact.conjugateMatter
    (liveGammaKineticVector gamma direction)).re

private theorem liveGammaZeroSpatialTwoKinetic_zero :
    liveGammaKineticReal (diracGamma 0) 2 = 0 := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  exact fixedMatter_gammaZero_spatialTwo_kinetic_zero

private theorem liveGammaOneTemporalKinetic_zero :
    liveGammaKineticReal (diracGamma 1) 0 = 0 := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  exact fixedMatter_gammaOne_temporal_kinetic_zero

private theorem liveGammaTwoTemporalKinetic_zero :
    liveGammaKineticReal (diracGamma 2) 0 = 0 := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  exact fixedMatter_gammaTwo_temporal_kinetic_zero

private theorem liveGammaThreeSpatialTwoKinetic_zero :
    liveGammaKineticReal (diracGamma 3) 2 = 0 := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  exact fixedMatter_gammaThree_spatialTwo_kinetic_zero

private theorem liveGammaTwoSpatialThreeKinetic_zero :
    liveGammaKineticReal (diracGamma 2) 3 = 0 := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  exact fixedMatter_gammaTwo_spatialThree_kinetic_zero

private theorem liveGammaTwoSpatialOneKinetic_zero :
    liveGammaKineticReal (diracGamma 2) 1 = 0 := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin]
  exact fixedMatter_gammaTwo_spatialOne_kinetic_zero

private theorem liveGammaZeroTemporalKinetic_eq :
    liveGammaKineticReal (diracGamma 0) 0 = (1 / 8 : ℝ) := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  rw [fixedP506JointActual_conjugateMatter_origin,
    fixedP506JointActual_temporalCovariantDerivative_normalForm_local]
  exact fixedMatterTemporalConnectionKinetic

private theorem liveGammaThreeSpatialThreeKinetic_eq :
    liveGammaKineticReal (diracGamma 3) 3 = -(1 / 8 : ℝ) := by
  unfold liveGammaKineticReal liveGammaKineticVector
  rw [fixedP506L0HessianLiveContact_conjugateMatter_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual]
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

private theorem live_repairedMatterVector_base_zero_local :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact 1) = 0 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    generatedContinuumDiracDualYukawaVector
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart]
  rw [fixedP506L0HessianLiveContact_matterCovariantDerivative_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_scalar_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_matter_eq_fixedP506JointActual]
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

private theorem inverseCoframeDiracGamma_transvection01
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := offDiagonalTransvectionPath 0 1 parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0 - (parameter : ℂ) • diracGamma 1,
        diracGamma 1, diracGamma 2, diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [offDiagonalTransvectionPath_inverse 0 1 (by decide) parameter]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

private theorem inverseCoframeDiracGamma_transvection20
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := offDiagonalTransvectionPath 2 0 parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0, diracGamma 1,
        diracGamma 2 - (parameter : ℂ) • diracGamma 0,
        diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [offDiagonalTransvectionPath_inverse 2 0 (by decide) parameter]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

private theorem inverseCoframeDiracGamma_transvection02
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := offDiagonalTransvectionPath 0 2 parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0 - (parameter : ℂ) • diracGamma 2,
        diracGamma 1, diracGamma 2, diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [offDiagonalTransvectionPath_inverse 0 2 (by decide) parameter]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

private theorem inverseCoframeDiracGamma_transvection23
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := offDiagonalTransvectionPath 2 3 parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0, diracGamma 1,
        diracGamma 2 - (parameter : ℂ) • diracGamma 3,
        diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [offDiagonalTransvectionPath_inverse 2 3 (by decide) parameter]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

private theorem inverseCoframeDiracGamma_transvection32
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := offDiagonalTransvectionPath 3 2 parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0, diracGamma 1, diracGamma 2,
        diracGamma 3 - (parameter : ℂ) • diracGamma 2] direction := by
  unfold inverseCoframeDiracGamma
  rw [offDiagonalTransvectionPath_inverse 3 2 (by decide) parameter]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

private theorem inverseCoframeDiracGamma_transvection12
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := offDiagonalTransvectionPath 1 2 parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0,
        diracGamma 1 - (parameter : ℂ) • diracGamma 2,
        diracGamma 2, diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [offDiagonalTransvectionPath_inverse 1 2 (by decide) parameter]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

private theorem diracMatrixMatterAction_sub_matrix_local
    (first second : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first - second) matter =
      diracMatrixMatterAction first matter -
        diracMatrixMatterAction second matter := by
  rw [sub_eq_add_neg,
    show -second = (-1 : ℂ) • second by simp,
    diracMatrixMatterAction_add_matrix,
    diracMatrixMatterAction_smul_matrix]
  rw [show
    (-1 : ℂ) •
        (diracMatrixMatterAction second matter : DiracExteriorMatterCarrier) =
      -(diracMatrixMatterAction second matter : DiracExteriorMatterCarrier) by
        exact neg_one_smul ℂ
          (diracMatrixMatterAction second matter :
            DiracExteriorMatterCarrier)]
  exact (sub_eq_add_neg _ _).symm

private theorem live_repairedMatterVector_transvection01
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath 0 1 parameter)) =
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact 1) -
        (parameter : ℂ) •
          liveGammaKineticVector (diracGamma 1) 0 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_transvection01]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveGammaKineticVector generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four, Matrix.cons_val]
  rw [diracMatrixMatterAction_sub_matrix_local,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_sub, smul_smul]
  module

private theorem live_repairedMatterVector_transvection20
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath 2 0 parameter)) =
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact 1) -
        (parameter : ℂ) •
          liveGammaKineticVector (diracGamma 0) 2 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_transvection20]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveGammaKineticVector generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four]
  simp only [Matrix.cons_val]
  rw [diracMatrixMatterAction_sub_matrix_local,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_sub, smul_smul]
  module

private theorem live_repairedMatterVector_transvection02
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath 0 2 parameter)) =
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact 1) -
        (parameter : ℂ) •
          liveGammaKineticVector (diracGamma 2) 0 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_transvection02]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveGammaKineticVector generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four, Matrix.cons_val]
  rw [diracMatrixMatterAction_sub_matrix_local,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_sub, smul_smul]
  module

private theorem live_repairedMatterVector_transvection23
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath 2 3 parameter)) =
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact 1) -
        (parameter : ℂ) •
          liveGammaKineticVector (diracGamma 3) 2 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_transvection23]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveGammaKineticVector generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four, Matrix.cons_val]
  rw [diracMatrixMatterAction_sub_matrix_local,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_sub, smul_smul]
  module

private theorem live_repairedMatterVector_transvection32
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath 3 2 parameter)) =
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact 1) -
        (parameter : ℂ) •
          liveGammaKineticVector (diracGamma 2) 3 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_transvection32]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveGammaKineticVector generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four, Matrix.cons_val]
  rw [diracMatrixMatterAction_sub_matrix_local,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_sub, smul_smul]
  module

private theorem live_repairedMatterVector_transvection12
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath 1 2 parameter)) =
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact 1) -
        (parameter : ℂ) •
          liveGammaKineticVector (diracGamma 2) 1 := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withCoframe, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_transvection12]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold liveGammaKineticVector generatedContinuumDiracDualYukawaVector
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, Fin.sum_univ_four, Matrix.cons_val]
  rw [diracMatrixMatterAction_sub_matrix_local,
    diracMatrixMatterAction_smul_matrix]
  simp only [smul_add, smul_sub, smul_smul]
  module

private theorem live_scalarDensity_offDiagonal_zero
    (coframe : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity Source 0 0
        (withCoframe LiveContact coframe) = 0 := by
  unfold generatedDensitizedContinuumScalarDensity
  simp only [withCoframe]
  rw [fixedP506L0HessianLiveContact_scalarCovariantDerivative_eq_fixedP506JointActual,
    fixedP506L0HessianLiveContact_scalar_eq_fixedP506JointActual]
  simp only [toContinuumPointField]
  have derivativeZero :
      holonomicScalarCovariantDerivative FixedP506JointActual 0 = 0 := by
    funext direction
    exact fixedP506JointActual_scalarCovariantDerivative_origin_zero direction
  rw [derivativeZero, fixedP506JointActual_scalar_origin]
  simp [generatedScalarKineticDensity,
    scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe,
    generatedScalarPotential, scalarCoordinateSquaredNorm]

private theorem live_repairedMatterDensity_transvection_zero
    (row column : LorentzianIndex) (distinct : row ≠ column)
    (gamma : DiracMatrix) (direction : LorentzianIndex)
    (vectorNormalForm : ∀ parameter : ℝ,
      generatedContinuumDiracDualMatterVector Source 0 0
          (withCoframe LiveContact
            (offDiagonalTransvectionPath row column parameter)) =
        generatedContinuumDiracDualMatterVector Source 0 0
            (withCoframe LiveContact 1) -
          (parameter : ℂ) • liveGammaKineticVector gamma direction)
    (kineticZero : liveGammaKineticReal gamma direction = 0)
    (parameter : ℝ) :
    generatedDensitizedContinuumDiracDualMatterDensity Source 0 0
        (withCoframe LiveContact
          (offDiagonalTransvectionPath row column parameter)) = 0 := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    vectorNormalForm parameter,
    live_repairedMatterVector_base_zero_local]
  simp only [withCoframe, matterDualFrameRelative_zeroChart,
    map_sub, map_smul, map_zero, Complex.zero_re,
    Complex.sub_re, Complex.smul_re, zero_sub]
  unfold generatedVolumeDensity
  rw [offDiagonalTransvectionPath_det row column distinct parameter,
    abs_one]
  have correction :
      (LiveContact.conjugateMatter
          (-((parameter : ℂ) •
            liveGammaKineticVector gamma direction))).re =
        -(parameter * liveGammaKineticReal gamma direction) := by
    unfold liveGammaKineticReal
    rw [map_neg, map_smul]
    rw [smul_eq_mul, Complex.neg_re, Complex.mul_re]
    simp
  rw [correction, kineticZero]
  ring

private theorem live_matterDensity_transvection01_zero
    (parameter : ℝ) :
    diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath 0 1 parameter) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_offDiagonal_zero,
    live_repairedMatterDensity_transvection_zero
      0 1 (by decide) (diracGamma 1) 0
      live_repairedMatterVector_transvection01
      liveGammaOneTemporalKinetic_zero parameter]
  ring

private theorem live_matterDensity_transvection20_zero
    (parameter : ℝ) :
    diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath 2 0 parameter) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_offDiagonal_zero,
    live_repairedMatterDensity_transvection_zero
      2 0 (by decide) (diracGamma 0) 2
      live_repairedMatterVector_transvection20
      liveGammaZeroSpatialTwoKinetic_zero parameter]
  ring

private theorem live_matterDensity_transvection02_zero
    (parameter : ℝ) :
    diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath 0 2 parameter) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_offDiagonal_zero,
    live_repairedMatterDensity_transvection_zero
      0 2 (by decide) (diracGamma 2) 0
      live_repairedMatterVector_transvection02
      liveGammaTwoTemporalKinetic_zero parameter]
  ring

private theorem live_matterDensity_transvection23_zero
    (parameter : ℝ) :
    diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath 2 3 parameter) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_offDiagonal_zero,
    live_repairedMatterDensity_transvection_zero
      2 3 (by decide) (diracGamma 3) 2
      live_repairedMatterVector_transvection23
      liveGammaThreeSpatialTwoKinetic_zero parameter]
  ring

private theorem live_matterDensity_transvection32_zero
    (parameter : ℝ) :
    diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath 3 2 parameter) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_offDiagonal_zero,
    live_repairedMatterDensity_transvection_zero
      3 2 (by decide) (diracGamma 2) 3
      live_repairedMatterVector_transvection32
      liveGammaTwoSpatialThreeKinetic_zero parameter]
  ring

private theorem live_matterDensity_transvection12_zero
    (parameter : ℝ) :
    diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath 1 2 parameter) = 0 := by
  unfold diracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  rw [live_scalarDensity_offDiagonal_zero,
    live_repairedMatterDensity_transvection_zero
      1 2 (by decide) (diracGamma 2) 1
      live_repairedMatterVector_transvection12
      liveGammaTwoSpatialOneKinetic_zero parameter]
  ring

private theorem live_matterDensity_offDiagonal_hasDerivAt
    (row column : LorentzianIndex)
    (densityZero : ∀ parameter : ℝ,
      diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
        (offDiagonalTransvectionPath row column parameter) = 0) :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
          (offDiagonalTransvectionPath row column parameter))
      0 0 := by
  exact (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall densityZero)

private theorem live_matterEuler_offDiagonal
    (row column : LorentzianIndex)
    (pathDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          diracDualFormNativeCoframeMatterDensity Source 0 LiveContact
            (offDiagonalTransvectionPath row column parameter))
        0 0) :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection row column) = 0 := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_offDiagonalTransvectionPath_hasDerivAt
    row column
    (diracDualFormNativeCoframeMatterDensity Source 0 LiveContact)
    (diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeMatterDensity_hasFDerivAt
          Source 0 LiveContact nondegenerate)
    0 pathDerivative

private theorem live_matterEuler_transvection01_zero :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 0 1) = 0 :=
  live_matterEuler_offDiagonal 0 1
    (live_matterDensity_offDiagonal_hasDerivAt
      0 1 live_matterDensity_transvection01_zero)

private theorem live_matterEuler_transvection20_zero :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 2 0) = 0 :=
  live_matterEuler_offDiagonal 2 0
    (live_matterDensity_offDiagonal_hasDerivAt
      2 0 live_matterDensity_transvection20_zero)

private theorem live_matterEuler_transvection02_zero :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 0 2) = 0 :=
  live_matterEuler_offDiagonal 0 2
    (live_matterDensity_offDiagonal_hasDerivAt
      0 2 live_matterDensity_transvection02_zero)

theorem live_matterEuler_transvection23_zero :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 2 3) = 0 :=
  live_matterEuler_offDiagonal 2 3
    (live_matterDensity_offDiagonal_hasDerivAt
      2 3 live_matterDensity_transvection23_zero)

theorem live_matterEuler_transvection32_zero :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 3 2) = 0 :=
  live_matterEuler_offDiagonal 3 2
    (live_matterDensity_offDiagonal_hasDerivAt
      3 2 live_matterDensity_transvection32_zero)

private theorem live_matterEuler_transvection12_zero :
    diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 1 2) = 0 :=
  live_matterEuler_offDiagonal 1 2
    (live_matterDensity_offDiagonal_hasDerivAt
      1 2 live_matterDensity_transvection12_zero)

private theorem offdiagLiveP506_formNativePairing_zero_left
    (coordinate : P286CoordinateCarrier) :
    formNativeP286CoordinateLiePairing 0 coordinate = 0 := by
  unfold formNativeP286CoordinateLiePairing formNativeP286LiePairing
  simp [specialUnitaryLiePairing, hyperchargeLiePairing]

private theorem offdiagLiveP506Gauss_formNativePairing_self :
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

private theorem live_gaugeDensity_transvection01
    (parameter : ℝ) :
    diracDualFormNativeCoframeGaugeDensity Source LiveContact
        (offDiagonalTransvectionPath 0 1 parameter) = (5 / 108 : ℝ) := by
  rw [fixedP506L0HessianLiveContact_gaugeDensity_normalForm,
    offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [offDiagonalTransvectionPath_inverse 0 1 (by decide) parameter]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    offDiagonalTransvectionPath, Matrix.transvection,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    offdiagLiveP506_formNativePairing_zero_left,
    offdiagLiveP506Gauss_formNativePairing_self,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul]
  ring

private theorem live_gaugeDensity_transvection20
    (parameter : ℝ) :
    diracDualFormNativeCoframeGaugeDensity Source LiveContact
        (offDiagonalTransvectionPath 2 0 parameter) = (5 / 108 : ℝ) := by
  rw [fixedP506L0HessianLiveContact_gaugeDensity_normalForm,
    offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [offDiagonalTransvectionPath_inverse 2 0 (by decide) parameter]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    offDiagonalTransvectionPath, Matrix.transvection,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    offdiagLiveP506_formNativePairing_zero_left,
    offdiagLiveP506Gauss_formNativePairing_self,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul]
  ring

private theorem live_gaugeDensity_transvection02
    (parameter : ℝ) :
    diracDualFormNativeCoframeGaugeDensity Source LiveContact
        (offDiagonalTransvectionPath 0 2 parameter) =
      (5 / 108 : ℝ) * (1 + parameter ^ 2) := by
  rw [fixedP506L0HessianLiveContact_gaugeDensity_normalForm,
    offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [offDiagonalTransvectionPath_inverse 0 2 (by decide) parameter]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    offDiagonalTransvectionPath, Matrix.transvection,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    offdiagLiveP506_formNativePairing_zero_left,
    offdiagLiveP506Gauss_formNativePairing_self,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul]
  ring

private theorem live_gaugeDensity_transvection23
    (parameter : ℝ) :
    diracDualFormNativeCoframeGaugeDensity Source LiveContact
        (offDiagonalTransvectionPath 2 3 parameter) = (5 / 108 : ℝ) := by
  rw [fixedP506L0HessianLiveContact_gaugeDensity_normalForm,
    offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [offDiagonalTransvectionPath_inverse 2 3 (by decide) parameter]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    offDiagonalTransvectionPath, Matrix.transvection,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    offdiagLiveP506_formNativePairing_zero_left,
    offdiagLiveP506Gauss_formNativePairing_self,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul]
  ring

private theorem live_gaugeDensity_transvection32
    (parameter : ℝ) :
    diracDualFormNativeCoframeGaugeDensity Source LiveContact
        (offDiagonalTransvectionPath 3 2 parameter) = (5 / 108 : ℝ) := by
  rw [fixedP506L0HessianLiveContact_gaugeDensity_normalForm,
    offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [offDiagonalTransvectionPath_inverse 3 2 (by decide) parameter]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    offDiagonalTransvectionPath, Matrix.transvection,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    offdiagLiveP506_formNativePairing_zero_left,
    offdiagLiveP506Gauss_formNativePairing_self,
    pairFirst, pairSecond, Fin.sum_univ_six,
      Matrix.cons_val, Matrix.one_apply, smul_smul]
  ring

private theorem live_gaugeDensity_transvection12
    (parameter : ℝ) :
    diracDualFormNativeCoframeGaugeDensity Source LiveContact
        (offDiagonalTransvectionPath 1 2 parameter) =
      (5 / 108 : ℝ) * (1 - parameter ^ 2) := by
  rw [fixedP506L0HessianLiveContact_gaugeDensity_normalForm,
    offdiagLiveP506CoordinateBlockwiseConstitutive_eq_unified,
    liftGaugeTwoFormOperator_smul_operator_p286]
  unfold formNativeP286GaugeCoordinateWedgeCoefficient
    generatedTwoFormWedgeCoefficient
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [offDiagonalTransvectionPath_inverse 1 2 (by decide) parameter]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    twoFormComplement, liftGaugeTwoFormOperator,
    gaugeOperatorCoefficient, coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    offDiagonalTransvectionPath, Matrix.transvection,
    formNativeP286CoordinateLiePairing_smul_left,
    formNativeP286CoordinateLiePairing_smul_right,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    offdiagLiveP506_formNativePairing_zero_left,
    offdiagLiveP506Gauss_formNativePairing_self,
    pairFirst, pairSecond, Fin.sum_univ_six,
    Matrix.cons_val, Matrix.one_apply, smul_smul]
  ring

private theorem live_gaugeDensity_transvection20_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity Source LiveContact
          (offDiagonalTransvectionPath 2 0 parameter))
      0 0 := by
  exact (hasDerivAt_const (x := (0 : ℝ)) (5 / 108 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall live_gaugeDensity_transvection20)

private theorem live_gaugeDensity_transvection01_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity Source LiveContact
          (offDiagonalTransvectionPath 0 1 parameter))
      0 0 := by
  exact (hasDerivAt_const (x := (0 : ℝ)) (5 / 108 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall live_gaugeDensity_transvection01)

private theorem live_gaugeDensity_transvection02_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity Source LiveContact
          (offDiagonalTransvectionPath 0 2 parameter))
      0 0 := by
  have polynomial : HasDerivAt
      (fun parameter : ℝ => (5 / 108 : ℝ) * (1 + parameter ^ 2)) 0 0 := by
    have quadratic :=
      ((hasDerivAt_id (x := (0 : ℝ))).pow 2).const_mul (5 / 108 : ℝ)
    have shifted := quadratic.const_add (5 / 108 : ℝ)
    simpa [mul_add, Function.id_def] using shifted
  exact polynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall live_gaugeDensity_transvection02)

private theorem live_gaugeDensity_transvection23_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity Source LiveContact
          (offDiagonalTransvectionPath 2 3 parameter))
      0 0 := by
  exact (hasDerivAt_const (x := (0 : ℝ)) (5 / 108 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall live_gaugeDensity_transvection23)

private theorem live_gaugeDensity_transvection32_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity Source LiveContact
          (offDiagonalTransvectionPath 3 2 parameter))
      0 0 := by
  exact (hasDerivAt_const (x := (0 : ℝ)) (5 / 108 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall live_gaugeDensity_transvection32)

private theorem live_gaugeDensity_transvection12_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        diracDualFormNativeCoframeGaugeDensity Source LiveContact
          (offDiagonalTransvectionPath 1 2 parameter))
      0 0 := by
  have polynomial : HasDerivAt
      (fun parameter : ℝ => (5 / 108 : ℝ) * (1 - parameter ^ 2)) 0 0 := by
    have quadratic :=
      ((hasDerivAt_id (x := (0 : ℝ))).pow 2).const_mul (5 / 108 : ℝ)
    have shifted := HasDerivAt.const_sub (5 / 108 : ℝ) quadratic
    simpa [mul_sub, Function.id_def] using shifted
  exact polynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall live_gaugeDensity_transvection12)

private theorem live_gaugeEuler_offDiagonal
    (row column : LorentzianIndex)
    (pathDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          diracDualFormNativeCoframeGaugeDensity Source LiveContact
            (offDiagonalTransvectionPath row column parameter))
        0 0) :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection row column) = 0 := by
  have nondegenerate : Matrix.det LiveContact.coframe ≠ 0 := by
    rw [liveContact_coframe]
    simp
  exact live_stress_apply_of_offDiagonalTransvectionPath_hasDerivAt
    row column
    (diracDualFormNativeCoframeGaugeDensity Source LiveContact)
    (diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact)
    (by
      simpa [liveContact_coframe] using
        diracDualFormNativeCoframeGaugeDensity_hasFDerivAt
          Source LiveContact nondegenerate)
    0 pathDerivative

private theorem live_gaugeEuler_transvection01_zero :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection 0 1) = 0 :=
  live_gaugeEuler_offDiagonal 0 1
    live_gaugeDensity_transvection01_hasDerivAt

private theorem live_gaugeEuler_transvection20_zero :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection 2 0) = 0 :=
  live_gaugeEuler_offDiagonal 2 0
    live_gaugeDensity_transvection20_hasDerivAt

private theorem live_gaugeEuler_transvection02_zero :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection 0 2) = 0 :=
  live_gaugeEuler_offDiagonal 0 2
    live_gaugeDensity_transvection02_hasDerivAt

theorem live_gaugeEuler_transvection23_zero :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection 2 3) = 0 :=
  live_gaugeEuler_offDiagonal 2 3
    live_gaugeDensity_transvection23_hasDerivAt

theorem live_gaugeEuler_transvection32_zero :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection 3 2) = 0 :=
  live_gaugeEuler_offDiagonal 3 2
    live_gaugeDensity_transvection32_hasDerivAt

private theorem live_gaugeEuler_transvection12_zero :
    diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
        (coframeCoordinateDirection 1 2) = 0 :=
  live_gaugeEuler_offDiagonal 1 2
    live_gaugeDensity_transvection12_hasDerivAt

theorem current_identityECLoad_eta02_zero :
    diracDualFormNativeIdentityECLoad Source Current
        EtaSymmetric02Variation = 0 := by
  rw [current_identityECLoad_eta02_reduction]
  unfold EtaSymmetric02Variation
  rw [map_sub, map_sub,
    live_gaugeEuler_transvection20_zero,
    live_gaugeEuler_transvection02_zero,
    live_matterEuler_transvection20_zero,
    live_matterEuler_transvection02_zero]
  ring

/-- The fixed source/current identity-EC load vanishes on the individual
temporal-to-spatial `E01` direction.  This is a forward read of the existing
live action density; no load coordinate is supplied to its producer. -/
theorem current_identityECLoad_temporalSpatial01_zero :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 0 1) = 0 := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 0 1) +
        diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
          (coframeCoordinateDirection 0 1) +
      diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 0 1) = 0
  rw [intrinsic_temporalSpatial01_zero,
    live_gaugeEuler_transvection01_zero,
    live_matterEuler_transvection01_zero]
  ring

/-- The same fixed source/current identity-EC load also vanishes on the
individual temporal-to-spatial `E02` direction. -/
theorem current_identityECLoad_temporalSpatial02_zero :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 0 2) = 0 := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 0 2) +
        diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
          (coframeCoordinateDirection 0 2) +
      diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 0 2) = 0
  rw [intrinsic_temporalSpatial02_zero,
    live_gaugeEuler_transvection02_zero,
    live_matterEuler_transvection02_zero]
  ring

/-- The fixed source/current identity-EC load vanishes on the individual
spatial-to-temporal `E20` direction.  This is the exact action read consumed
by the Candidate EC target at curvature coordinate `(0,5)`. -/
theorem current_identityECLoad_spatialTemporal20_zero :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 2 0) = 0 := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 2 0) +
        diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
          (coframeCoordinateDirection 2 0) +
      diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 2 0) = 0
  rw [intrinsic_spatialTemporal20_zero,
    live_gaugeEuler_transvection20_zero,
    live_matterEuler_transvection20_zero]
  ring

/-- The fixed source/current identity-EC load vanishes on the spatial
off-diagonal `E12` direction. -/
theorem current_identityECLoad_spatial12_zero :
    diracDualFormNativeIdentityECLoad Source Current
        (coframeCoordinateDirection 1 2) = 0 := by
  rw [current_identityECLoad_eq_localPreEC]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  change
    identityDiracDualECIntrinsicIIPlusObservation
          (coframeCoordinateDirection 1 2) +
        diracDualFormNativeCoframeGaugeEulerCovector Source LiveContact
          (coframeCoordinateDirection 1 2) +
      diracDualFormNativeCoframeMatterEulerCovector Source 0 LiveContact
        (coframeCoordinateDirection 1 2) = 0
  rw [intrinsic_spatial12_zero,
    live_gaugeEuler_transvection12_zero,
    live_matterEuler_transvection12_zero]
  ring

theorem current_identityECLoad_spatial23_zero :
    diracDualFormNativeIdentityECLoad Source Current
        SpatialSymmetric23Variation = 0 := by
  rw [current_identityECLoad_spatial23_reduction]
  unfold SpatialSymmetric23Variation
  rw [map_add, map_add,
    live_gaugeEuler_transvection23_zero,
    live_gaugeEuler_transvection32_zero,
    live_matterEuler_transvection23_zero,
    live_matterEuler_transvection32_zero]
  ring

/-- The fixed source/current action Hessian has vanishing determinant-support
`02` row.  The statement exposes the public generated row carrier directly. -/
theorem fixedP506L0U6HessianRows_zero_two :
    (sourceActionGeneratedIdentityECCoframeAccelerationRows
      positiveSmoothUnifiedSource
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual).1 0 2 = 0 := by
  rw [hessianRows_zero_two_eq_actionResidual]
  simp only [add_apply]
  rw [current_curvatureObservation_eta02_zero,
    current_identityECLoad_eta02_zero]
  norm_num

/-- The fixed source/current action Hessian `23` row is the exact old-contact
acceleration support divided by `-6`; no old row is substituted for the
public current Hessian carrier. -/
theorem fixedP506L0U6HessianRows_two_three_eq_oldAcceleration :
    (sourceActionGeneratedIdentityECCoframeAccelerationRows
      positiveSmoothUnifiedSource
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual).1 2 3 =
      -fixedP506L0ContactAccelerationRows 2 3 / 6 := by
  rw [hessianRows_two_three_eq_actionResidual]
  simp only [add_apply]
  rw [current_curvatureObservation_spatial23_eq_oldAcceleration,
    current_identityECLoad_spatial23_zero]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianOffDiagonalRows
