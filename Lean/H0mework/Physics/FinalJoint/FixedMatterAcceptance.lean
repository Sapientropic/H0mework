import H0mework.Physics.FinalJoint.FixedActionWrite
import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterIdentityCoframeAcceptance
import H0mework.Physics.DualVariation.RepairedMatterEquationReadout

/-!
# Fixed P506/L0 matter acceptance of the final common action write

This module reads the two repaired Dirac action laws on the same final
common actual.  The response remains source/action-owned: no Euler residual,
support coordinate, target derivative, branch, or zero-fiber witness enters
either matter constructor.

Only fixed-contact regularity used by the linear-time installers is required
here.  In particular, no global nondegeneracy or identity-coframe
claim is introduced.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonMatterAcceptance

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterPointwiseEquation
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem fixedP506L0RecenteredInput_smooth
    (space : StageNineSpatialPoint) :
    (fixedP506L0RecenteredInput space).Smooth := by
  exact
    spatiallyRecenterHolonomicConfiguration_smooth
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_smooth space

private theorem fixedP506L0CartanRestartActual_matter_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        ((fixedP506L0CartanRestartActual space).matter point) := by
  change ContDiff ℝ ∞ fun point =>
    matterCoordinateEquiv ((fixedP506L0RecenteredInput space).matter point)
  exact (fixedP506L0RecenteredInput_smooth space).2.2.2.2.2.2.2.1

private theorem
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin_of_contDiff
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
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_of_contDiff
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
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin_of_contDiff
      configuration matterSmooth response direction]
  split_ifs <;>
    simp only [map_add, matterCoordinateEquiv.symm_apply_apply, map_zero,
      installMatterLinearTimeResponse_gravityConnection,
      installMatterLinearTimeResponse_gaugeConnection,
      installMatterLinearTimeResponse_matter_origin] <;>
    module

private theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw_of_matterContDiff
    (configuration : StageNineHolonomicConfiguration)
    (matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point))
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
        configuration)
      0
      (holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have spatialDerivative (direction : Fin 3) :
      holonomicMatterCovariantDerivative
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration)
          0 direction.succ =
        holonomicMatterCovariantDerivative configuration 0 direction.succ := by
    unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    rw [
      holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_of_contDiff
        configuration matterSmooth
        (diracDualCurrentCoframeMatterTimeResponseWrite configuration)]
    simp [canonicalLorentzianTimeDirection]
  have timeDerivative :
      holonomicMatterCovariantDerivative
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration)
          0 canonicalLorentzianTimeDirection =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          configuration 0 := by
    unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    rw [
      holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin_of_contDiff
        configuration matterSmooth
        (diracDualCurrentCoframeMatterTimeResponseWrite configuration)]
    simp only [if_pos]
    unfold diracDualCurrentCoframeMatterTimeResponseWrite
    abel
  have knownVector :
      holonomicDiracDualCurrentCoframeMatterKnownVector
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration)
          0 =
        holonomicDiracDualCurrentCoframeMatterKnownVector configuration 0 := by
    unfold holonomicDiracDualCurrentCoframeMatterKnownVector
    rw [
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar,
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]
    simp_rw [spatialDerivative]
  have generatedLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      configuration 0 noncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generatedLaw ⊢
  rw [
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
    knownVector, timeDerivative]
  exact generatedLaw

private theorem fixedP506L0CartanRestartActual_noncharacteristic
    (space : StageNineSpatialPoint) :
    coframeTemporalPrincipalScalar
        ((fixedP506L0CartanRestartActual space).coframe 0) ≠ 0 := by
  rw [← recenteredCartanRepairedConstitutiveCurrent_coframe_eq_cartan]
  rw [recenteredCartanRepairedConstitutiveCurrent_coframe_origin]
  simpa only [coframeTemporalPrincipalScalar_one] using
    (one_ne_zero : (1 : ℝ) ≠ 0)

private theorem fixedP506L0RepairedMatterJoint_primalActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (actionGeneratedDiracDualRepairedMatterJointResponseActual
        (fixedP506L0CartanRestartActual space))
      0
      (holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualRepairedMatterJointResponseActual
          (fixedP506L0CartanRestartActual space))
        0 canonicalLorentzianTimeDirection) := by
  have law :=
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw_of_matterContDiff
      (fixedP506L0CartanRestartActual space)
      (fixedP506L0CartanRestartActual_matter_contDiff space)
      (fixedP506L0CartanRestartActual_noncharacteristic space)
  simpa [actionGeneratedDiracDualRepairedMatterJointResponseActual,
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw,
    holonomicDiracDualCurrentCoframeMatterKnownVector,
    holonomicMatterCovariantDerivative] using law

private theorem recenteredCartanRepairedConstitutiveCurrent_primalActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (recenteredCartanRepairedConstitutiveCurrent space)
      0
      (holonomicMatterCovariantDerivative
        (recenteredCartanRepairedConstitutiveCurrent space)
        0 canonicalLorentzianTimeDirection) := by
  have law := fixedP506L0RepairedMatterJoint_primalActionLaw space
  simpa [recenteredCartanRepairedConstitutiveCurrent,
    fixedP506L0CartanRestartActual, fixedP506L0RecenteredInput,
    diracDualFormNativeRepairedConstitutiveWrittenCurrent,
    diracDualFormNativeRepairedMatterWrittenCurrent,
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw,
    holonomicDiracDualCurrentCoframeMatterKnownVector,
    holonomicMatterCovariantDerivative] using law

private theorem fixedP506L0FinalCommonActionActual_scalar_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).scalar 0 =
      (recenteredCartanRepairedConstitutiveCurrent space).scalar 0 := by
  rw [fixedP506L0FinalCommonActionActual_scalar]
  exact congrArg (fun field => field.scalar)
    (recenteredCartanRepairedScalarSecondJetActual_pointField_origin space)

private theorem fixedP506L0FinalCommonActionActual_matter_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).matter 0 =
      (recenteredCartanRepairedConstitutiveCurrent space).matter 0 := by
  rw [fixedP506L0FinalCommonActionActual_matter,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_matter]

private theorem
    fixedP506L0FinalCommonActionActual_matterCovariantDerivative_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    holonomicMatterCovariantDerivative
        (fixedP506L0FinalCommonActionActual space) 0 =
      holonomicMatterCovariantDerivative
        (recenteredCartanRepairedConstitutiveCurrent space) 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [fixedP506L0FinalCommonActionActual_matter,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_matter,
    fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC,
    fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered,
    fixedP506L0FinalCommonActionActual_gaugeConnection,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_gaugeConnection]

theorem fixedP506L0FinalCommonActionActual_primalActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (fixedP506L0FinalCommonActionActual space)
      0
      (holonomicMatterCovariantDerivative
        (fixedP506L0FinalCommonActionActual space)
        0 canonicalLorentzianTimeDirection) := by
  have law := recenteredCartanRepairedConstitutiveCurrent_primalActionLaw space
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at law ⊢
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector at law ⊢
  rw [recenteredCartanRepairedConstitutiveCurrent_coframe_origin] at law
  rw [fixedP506L0FinalCommonActionActual_coframe_origin,
    fixedP506L0FinalCommonActionActual_scalar_origin_eq_recentered,
    fixedP506L0FinalCommonActionActual_matter_origin_eq_recentered,
    fixedP506L0FinalCommonActionActual_matterCovariantDerivative_origin_eq_recentered]
  exact law

theorem fixedP506L0FinalCommonActionActual_matterVector_origin_zero
    (space : StageNineSpatialPoint) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (fixedP506L0FinalCommonActionActual space) 0) = 0 := by
  exact generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    positiveSmoothUnifiedSource
    (fixedP506L0FinalCommonActionActual space) 0
    (fixedP506L0FinalCommonActionActual_primalActionLaw space)

theorem fixedP506L0FinalCommonActionResidual_conjugateMatter_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [fixedP506L0FinalCommonActionActual_matterVector_origin_zero]
  simp

/-! ## Fixed zero-first-jet producer seam -/

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold canonicalSpatialContactTranslation
  exact add_zero _

private theorem fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ field
      (canonicalSpatialContactTranslation space point)) :
    fieldDirectionalDerivative
        (field ∘ canonicalSpatialContactTranslation space) point direction =
      fieldDirectionalDerivative field
        (canonicalSpatialContactTranslation space point) direction := by
  have translation :
      HasFDerivAt (canonicalSpatialContactTranslation space)
        (ContinuousLinearMap.id ℝ BasePoint) point := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have composed := differentiable.hasFDerivAt.comp point translation
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  rfl

private theorem fixedP506L0RecenteredInput_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt (fixedP506L0RecenteredInput space).coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  have sourceJet :
      holonomicCoframeFirstJetAt
          FixedP506FormNativeJointActionSolvedSuccessor.coframe
          (canonicalCauchySlicePoint 0 space) =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) := by
    rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
      fixedP506JointActionSuccessor_coframe,
      fixedGlobalMatterDualP286Complete_coframe,
      fixedGlobalMatterDualFullCauchy_coframe,
      fixedGlobalFullCauchy_coframe]
    exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space
  have valueEq :
      (holonomicCoframeFirstJetAt
        (fixedP506L0RecenteredInput space).coframe 0).coframe = 1 := by
    change (fixedP506L0RecenteredInput space).coframe 0 = 1
    change
      FixedP506FormNativeJointActionSolvedSuccessor.coframe
          (canonicalSpatialContactTranslation space 0) = 1
    rw [canonicalSpatialContactTranslation_zero_local]
    exact congrArg PointwiseLorentzianCoframeJet.coframe sourceJet
  have derivativeEq :
      (holonomicCoframeFirstJetAt
        (fixedP506L0RecenteredInput space).coframe 0).derivative = 0 := by
    have sourceDerivative :=
      congrArg PointwiseLorentzianCoframeJet.derivative sourceJet
    funext direction internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point =>
              FixedP506FormNativeJointActionSolvedSuccessor.coframe point
                internal coordinate) ∘
            canonicalSpatialContactTranslation space)
          0 direction = 0
    rw [
      fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
        (fun point =>
          FixedP506FormNativeJointActionSolvedSuccessor.coframe point
            internal coordinate)
        space 0 direction
        (((fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
          internal coordinate).differentiable (by simp)).differentiableAt)]
    rw [canonicalSpatialContactTranslation_zero_local]
    exact congrFun (congrFun (congrFun sourceDerivative direction) internal)
      coordinate
  exact coframeJet_eq_of_fields_eq _ _ valueEq derivativeEq

private theorem fixedP506L0PrimalResponseActual_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)).coframe 0 =
      identityCoframeMatterGeometry := by
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
    fixedP506L0CartanRestartActual,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  simpa [identityCoframeMatterGeometry] using
    fixedP506L0RecenteredInput_coframeFirstJet_origin space

/-- The fixed identity presentation is a compatibility readout of the live
producer at this generated identity first jet; it does not select the write. -/
private theorem fixedP506L0RepairedMatterJoint_eq_identityActual
    (space : StageNineSpatialPoint) :
    actionGeneratedDiracDualRepairedMatterJointResponseActual
        (fixedP506L0CartanRestartActual space) =
      actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)) := by
  unfold actionGeneratedDiracDualRepairedMatterJointResponseActual
  exact
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_identity_of_firstJet
      _ (fixedP506L0PrimalResponseActual_coframeFirstJet_origin space)

/-! ## Repaired adjoint action law on the same final actual -/

private theorem
    holonomicConjugateMatterDerivativeCoordinates_installConjugateMatterLinearTimeResponse_origin_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (coordinateSmooth :
      ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates configuration))
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (installConjugateMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicConjugateMatterDerivativeCoordinates configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterDualCoordinates response
        else
          0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) 0 :=
    (coordinateSmooth.differentiable (by simp)).differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (conjugateMatterLinearTimeCoordinateWrite response) 0 :=
    ((conjugateMatterLinearTimeCoordinateWrite_contDiff response).differentiable
      (by simp)).differentiableAt
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [show
    holonomicConjugateMatterCoordinates
        (installConjugateMatterLinearTimeResponse configuration response) =
      holonomicConjugateMatterCoordinates configuration +
        conjugateMatterLinearTimeCoordinateWrite response by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        configuration response point]
  rw [fderiv_add backgroundDifferentiable responseDifferentiable, add_apply]
  change
    _ + fieldDirectionalDerivative
          (conjugateMatterLinearTimeCoordinateWrite response) 0 direction = _
  rw [conjugateMatterLinearTimeCoordinateWrite_directionalDerivative]

private theorem
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (coordinateSmooth :
      ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates configuration))
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (installConjugateMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicConjugateMatterDerivativeDual configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then response else 0 := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [
    holonomicConjugateMatterDerivativeCoordinates_installConjugateMatterLinearTimeResponse_origin_of_contDiff
      configuration coordinateSmooth response direction]
  split_ifs <;>
    simp [matterDualOfCoordinates_add,
      matterDualOfCoordinates_surjective]

private theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw_of_coordinateContDiff
    (configuration : StageNineHolonomicConfiguration)
    (coordinateSmooth :
      ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates configuration)) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        configuration)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have spatialTransport :
      holonomicIdentityCoframeConjugateMatterSpatialTransport
          (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
            configuration)
          0 =
        holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
          0 := by
    unfold
      actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      holonomicIdentityCoframeConjugateMatterSpatialTransport
    apply Finset.sum_congr rfl
    intro direction _
    rw [
      holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin_of_contDiff
        configuration coordinateSmooth
        (diracDualIdentityCoframeConjugateMatterTimeResponseWrite configuration)
        direction.succ]
    have spatialNe :
        direction.succ ≠ canonicalLorentzianTimeDirection := by
      fin_cases direction <;> decide
    simp [spatialNe]
  have knownDual :
      holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
          (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
            configuration)
          0 =
        holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
          configuration 0 := by
    unfold holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    rw [
      actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin,
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator_actionGeneratedAdjointActual_origin,
      spatialTransport]
  have actionVelocity :
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
            configuration)
          0 =
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          configuration 0 := by
    unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    rw [knownDual]
  have timeDerivative :
      holonomicConjugateMatterDerivativeDual
          (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
            configuration)
          0 canonicalLorentzianTimeDirection =
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          configuration 0 := by
    unfold
      actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
    rw [
      holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin_of_contDiff
        configuration coordinateSmooth
        (diracDualIdentityCoframeConjugateMatterTimeResponseWrite configuration)
        canonicalLorentzianTimeDirection]
    simp [diracDualIdentityCoframeConjugateMatterTimeResponseWrite]
  have generatedLaw :=
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_satisfies
      (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        configuration)
      0
  rw [timeDerivative, ← actionVelocity]
  exact generatedLaw

private theorem fixedP506L0CartanRestartActual_conjugateCoordinates_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (fixedP506L0CartanRestartActual space)) := by
  change ContDiff ℝ ∞
    (holonomicConjugateMatterCoordinates (fixedP506L0RecenteredInput space))
  exact holonomicConjugateMatterCoordinates_contDiff
    (fixedP506L0RecenteredInput space)
    (fixedP506L0RecenteredInput_smooth space)

private theorem
    fixedP506L0PrimalResponseActual_conjugateCoordinates_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space))) := by
  unfold holonomicConjugateMatterCoordinates
  rw [show
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      (fixedP506L0CartanRestartActual space)).conjugateMatter =
        (fixedP506L0CartanRestartActual space).conjugateMatter by
      rfl]
  exact fixedP506L0CartanRestartActual_conjugateCoordinates_contDiff space

private theorem fixedP506L0RepairedMatterJoint_adjointActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualRepairedMatterJointResponseActual
        (fixedP506L0CartanRestartActual space))
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualRepairedMatterJointResponseActual
          (fixedP506L0CartanRestartActual space))
        0 canonicalLorentzianTimeDirection) := by
  rw [fixedP506L0RepairedMatterJoint_eq_identityActual]
  exact
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw_of_coordinateContDiff
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
        (fixedP506L0CartanRestartActual space))
      (fixedP506L0PrimalResponseActual_conjugateCoordinates_contDiff space)

private theorem recenteredCartanRepairedConstitutiveCurrent_adjointActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (recenteredCartanRepairedConstitutiveCurrent space)
      0
      (holonomicConjugateMatterDerivativeDual
        (recenteredCartanRepairedConstitutiveCurrent space)
        0 canonicalLorentzianTimeDirection) := by
  have law := fixedP506L0RepairedMatterJoint_adjointActionLaw space
  have derivativeEq :
      holonomicConjugateMatterDerivativeDual
          (recenteredCartanRepairedConstitutiveCurrent space) 0 =
        holonomicConjugateMatterDerivativeDual
          (actionGeneratedDiracDualRepairedMatterJointResponseActual
            (fixedP506L0CartanRestartActual space)) 0 := by
    rfl
  have conjugateEq :
      (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter 0 =
        (actionGeneratedDiracDualRepairedMatterJointResponseActual
          (fixedP506L0CartanRestartActual space)).conjugateMatter 0 := by
    rfl
  have algebraicEq :
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
          (recenteredCartanRepairedConstitutiveCurrent space) 0 =
        holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
          (actionGeneratedDiracDualRepairedMatterJointResponseActual
            (fixedP506L0CartanRestartActual space)) 0 := by
    rfl
  unfold HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport at law ⊢
  rw [derivativeEq, conjugateEq, algebraicEq]
  exact law

private theorem
    fixedP506L0FinalCommonActionActual_conjugateMatter_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).conjugateMatter =
      (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter := by
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_conjugateMatter]

private theorem
    fixedP506L0FinalCommonActionActual_conjugateMatterDerivative_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    holonomicConjugateMatterDerivativeDual
        (fixedP506L0FinalCommonActionActual space) 0 =
      holonomicConjugateMatterDerivativeDual
        (recenteredCartanRepairedConstitutiveCurrent space) 0 := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter_eq_recentered]

private theorem
    fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gravityConnection 0 =
      (recenteredCartanRepairedConstitutiveCurrent space).gravityConnection 0 := by
  rw [fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC,
    fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered]

private theorem
    fixedP506L0FinalCommonActionActual_gaugeConnection_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gaugeConnection 0 =
      (recenteredCartanRepairedConstitutiveCurrent space).gaugeConnection 0 := by
  rw [fixedP506L0FinalCommonActionActual_gaugeConnection,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_gaugeConnection]

private theorem
    fixedP506L0FinalCommonActionActual_adjointAlgebraicOperator_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        (fixedP506L0FinalCommonActionActual space) 0 =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        (recenteredCartanRepairedConstitutiveCurrent space) 0 := by
  unfold holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_recentered,
    fixedP506L0FinalCommonActionActual_gaugeConnection_origin_eq_recentered,
    fixedP506L0FinalCommonActionActual_scalar_origin_eq_recentered]

theorem fixedP506L0FinalCommonActionActual_adjointActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (fixedP506L0FinalCommonActionActual space)
      0
      (holonomicConjugateMatterDerivativeDual
        (fixedP506L0FinalCommonActionActual space)
        0 canonicalLorentzianTimeDirection) := by
  have law := recenteredCartanRepairedConstitutiveCurrent_adjointActionLaw space
  unfold HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport at law ⊢
  rw [fixedP506L0FinalCommonActionActual_conjugateMatterDerivative_origin_eq_recentered]
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter_eq_recentered,
    fixedP506L0FinalCommonActionActual_adjointAlgebraicOperator_origin_eq_recentered]
  exact law

/-! ## Proof-only smooth carrier for the fixed-contact adjoint calculus -/

private theorem
    installConjugateMatterLinearTimeResponse_coordinates_contDiff_of_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (coordinateSmooth :
      ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates configuration))
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (installConjugateMatterLinearTimeResponse configuration response)) := by
  rw [show
    holonomicConjugateMatterCoordinates
        (installConjugateMatterLinearTimeResponse configuration response) =
      holonomicConjugateMatterCoordinates configuration +
        conjugateMatterLinearTimeCoordinateWrite response by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        configuration response point]
  exact coordinateSmooth.add
    (conjugateMatterLinearTimeCoordinateWrite_contDiff response)

private theorem fixedP506L0RepairedMatterJoint_conjugateCoordinates_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (actionGeneratedDiracDualRepairedMatterJointResponseActual
          (fixedP506L0CartanRestartActual space))) := by
  rw [fixedP506L0RepairedMatterJoint_eq_identityActual]
  unfold actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
  exact
    installConjugateMatterLinearTimeResponse_coordinates_contDiff_of_contDiff
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
        (fixedP506L0CartanRestartActual space))
      (fixedP506L0PrimalResponseActual_conjugateCoordinates_contDiff space)
      (diracDualIdentityCoframeConjugateMatterTimeResponseWrite
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          (fixedP506L0CartanRestartActual space)))

private theorem fixedP506L0FinalCommonActionActual_conjugateCoordinates_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (fixedP506L0FinalCommonActionActual space)) := by
  have fieldEq :
      holonomicConjugateMatterCoordinates
          (fixedP506L0FinalCommonActionActual space) =
        holonomicConjugateMatterCoordinates
          (actionGeneratedDiracDualRepairedMatterJointResponseActual
            (fixedP506L0CartanRestartActual space)) := by
    funext point
    unfold holonomicConjugateMatterCoordinates
    rw [fixedP506L0FinalCommonActionActual_conjugateMatter_eq_recentered]
    rfl
  rw [fieldEq]
  exact fixedP506L0RepairedMatterJoint_conjugateCoordinates_contDiff space

/-- A proof-only smooth comparison for the final fixed contact.  It preserves
the physical coframe and reconstructed adjoint field, while replacing the
Cartan connection away from the contact by its constant contact value. -/
def fixedP506L0FinalCommonMatterSmoothComparison
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  { fixedP506L0RecenteredInput space with
    gravityConnection :=
      fun _ => (fixedP506L0FinalCommonActionActual space).gravityConnection 0
    conjugateMatter := fun point =>
      matterDualOfCoordinates
        (holonomicConjugateMatterCoordinates
          (fixedP506L0FinalCommonActionActual space) point) }

theorem fixedP506L0FinalCommonMatterSmoothComparison_smooth
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonMatterSmoothComparison space).Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  dsimp only [fixedP506L0FinalCommonMatterSmoothComparison]
  rcases fixedP506L0RecenteredInput_smooth space with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, _conjugateMatterSmooth⟩
  have connectionSmooth :
      ∀ direction internalOut internalIn,
        ContDiff ℝ ∞ fun _ : BasePoint =>
          (fixedP506L0FinalCommonActionActual space).gravityConnection 0
            direction internalOut internalIn := by
    intro direction internalOut internalIn
    exact contDiff_const
  have conjugateSmooth :
      ∀ index : MatterCoordinateIndex,
        ContDiff ℝ ∞ fun point =>
          matterDualOfCoordinates
              (holonomicConjugateMatterCoordinates
                (fixedP506L0FinalCommonActionActual space) point)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    intro index
    rw [show
      (fun point =>
        matterDualOfCoordinates
            (holonomicConjugateMatterCoordinates
              (fixedP506L0FinalCommonActionActual space) point)
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) =
        fun point =>
          holonomicConjugateMatterCoordinates
            (fixedP506L0FinalCommonActionActual space) point index by
      funext point
      exact matterDualOfCoordinates_basis_apply _ _]
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj index).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
    exact (projection.restrictScalars ℝ).contDiff.comp
      (fixedP506L0FinalCommonActionActual_conjugateCoordinates_contDiff space)
  exact
    ⟨coframeSmooth, connectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateSmooth⟩

theorem fixedP506L0FinalCommonMatterSmoothComparison_coframe_eq_final
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonMatterSmoothComparison space).coframe =
      (fixedP506L0FinalCommonActionActual space).coframe := by
  rfl

theorem
    fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonMatterSmoothComparison space).conjugateMatter =
      (fixedP506L0FinalCommonActionActual space).conjugateMatter := by
  funext point
  exact matterDualOfCoordinates_surjective _

private theorem
    fixedP506L0FinalCommonMatterSmoothComparison_conjugateDerivative_origin_eq_final
    (space : StageNineSpatialPoint) :
    holonomicConjugateMatterDerivativeDual
        (fixedP506L0FinalCommonMatterSmoothComparison space) 0 =
      holonomicConjugateMatterDerivativeDual
        (fixedP506L0FinalCommonActionActual space) 0 := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final]

theorem
    fixedP506L0FinalCommonMatterSmoothComparison_algebraicOperator_origin_eq_final
    (space : StageNineSpatialPoint) :
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        (fixedP506L0FinalCommonMatterSmoothComparison space) 0 =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        (fixedP506L0FinalCommonActionActual space) 0 := by
  unfold holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
  rw [fixedP506L0FinalCommonActionActual_gaugeConnection]
  rw [recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_gaugeConnection]
  rw [fixedP506L0FinalCommonActionActual_scalar_origin_eq_recentered]
  rfl

theorem fixedP506L0FinalCommonMatterSmoothComparison_adjointActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (fixedP506L0FinalCommonMatterSmoothComparison space) 0
      (holonomicConjugateMatterDerivativeDual
        (fixedP506L0FinalCommonMatterSmoothComparison space) 0
        canonicalLorentzianTimeDirection) := by
  have law := fixedP506L0FinalCommonActionActual_adjointActionLaw space
  unfold HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport at law ⊢
  rw [
    fixedP506L0FinalCommonMatterSmoothComparison_conjugateDerivative_origin_eq_final,
    fixedP506L0FinalCommonMatterSmoothComparison_conjugateMatter_eq_final,
    fixedP506L0FinalCommonMatterSmoothComparison_algebraicOperator_origin_eq_final]
  exact law

def fixedP506L0FinalCommonMatterIdentityCoframeComparison
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  identityCoframeComparison
    (fixedP506L0FinalCommonMatterSmoothComparison space)

private theorem fixedP506L0FinalCommonMatterIdentityCoframeComparison_smooth
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonMatterIdentityCoframeComparison space).Smooth := by
  exact identityCoframeComparison_smooth
    (fixedP506L0FinalCommonMatterSmoothComparison space)
    (fixedP506L0FinalCommonMatterSmoothComparison_smooth space)

private theorem
    fixedP506L0FinalCommonMatterIdentityCoframeComparison_hasIdentityCoframe
    (space : StageNineSpatialPoint) :
    HasIdentityCoframe
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison space) := by
  exact identityCoframeComparison_hasIdentityCoframe
    (fixedP506L0FinalCommonMatterSmoothComparison space)

private theorem
    fixedP506L0FinalCommonMatterIdentityCoframeComparison_adjointActionLaw
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison space) 0
      (holonomicConjugateMatterDerivativeDual
        (fixedP506L0FinalCommonMatterIdentityCoframeComparison space) 0
        canonicalLorentzianTimeDirection) := by
  apply
    (identityCoframeComparison_diracDualTimeActionLaw_iff
      (fixedP506L0FinalCommonMatterSmoothComparison space) 0 _).2
  exact fixedP506L0FinalCommonMatterSmoothComparison_adjointActionLaw space

theorem fixedP506L0FinalCommonMatterIdentityCoframeComparison_matterEuler_zero
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonMatterIdentityCoframeComparison space)
        direction 0 = 0 := by
  exact
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison space)
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison_smooth space)
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison_hasIdentityCoframe
        space)
      0
      (fixedP506L0FinalCommonMatterIdentityCoframeComparison_adjointActionLaw
        space)
      direction

theorem fixedP506L0FinalCommonMatterSmoothComparison_coframeFirstJet_origin
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedP506L0FinalCommonMatterSmoothComparison space).coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  exact fixedP506L0RecenteredInput_coframeFirstJet_origin space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonMatterAcceptance
