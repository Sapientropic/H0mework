import H0mework.Physics.CartanAction.CartanPointCoframeRegularity
import H0mework.Physics.RecenteredJoint.FixedCauchyEvolutionAction

/-!
# Fixed Cartan contact-origin regularity

This module proves that the source/action-generated Cartan origin of the
fixed P506/L0 recentered contact family is differentiable in the source-owned
spatial occurrence.  It unfolds the actual coframe, W13, Levi--Civita, and
contorsion dependencies; it does not introduce an arbitrary-current
regularity interface or a new dynamics operator.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionAction
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionProducer
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineResidualLinearPlebanskiTorsionReduction
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-! ## Post-Cartan translation naturality -/

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

private theorem recenteredInput_coframeFirstJet_origin_eq_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicCoframeFirstJetAt
        (fixedP506L0RecenteredInput space).coframe 0 =
      holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 space) := by
  apply coframeJet_eq_of_fields_eq
  · change InputActual.coframe
        (canonicalSpatialContactTranslation space 0) = _
    rw [canonicalSpatialContactTranslation_zero_local]
    rfl
  · funext derivativeDirection internal coordinate
    let component : BasePoint → ℝ := fun point =>
      InputActual.coframe point internal coordinate
    have differentiable : DifferentiableAt ℝ component
        (canonicalSpatialContactTranslation space 0) :=
      ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
        internal coordinate).differentiable (by simp)).differentiableAt
    change
      fieldDirectionalDerivative
          (component ∘ canonicalSpatialContactTranslation space) 0
          derivativeDirection =
        fieldDirectionalDerivative component
          (canonicalCauchySlicePoint 0 space) derivativeDirection
    rw [fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
      component space 0 derivativeDirection differentiable]
    rw [canonicalSpatialContactTranslation_zero_local]

private theorem recenteredInput_spinResponse_origin_eq_zeroSlice
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        (fixedP506L0RecenteredInput space) 0 =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        InputActual (canonicalCauchySlicePoint 0 space) := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  all_goals
    simp [fixedP506L0RecenteredInput,
      spatiallyRecenterHolonomicConfiguration,
      canonicalSpatialContactTranslation_zero_local]

/-- The recentered fixed contact Cartan origin reads the same action-owned
Cartan connection as the unrecentered input at the matching zero-slice
occurrence. -/
theorem
    fixedP506L0CartanRestartActual_connection_origin_eq_zeroSliceAction
    (space : StageNineSpatialPoint) :
    (fixedP506L0CartanRestartActual space).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual (canonicalCauchySlicePoint 0 space) := by
  rw [fixedP506L0CartanRestartActual,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  dsimp only
  have coframeEq :
      (fixedP506L0RecenteredInput space).coframe 0 =
        InputActual.coframe (canonicalCauchySlicePoint 0 space) := by
    change InputActual.coframe
        (canonicalSpatialContactTranslation space 0) = _
    rw [canonicalSpatialContactTranslation_zero_local]
  rw [recenteredInput_coframeFirstJet_origin_eq_zeroSlice, coframeEq,
    recenteredInput_spinResponse_origin_eq_zeroSlice]

/-! ## Fixed action-origin regularity -/

private theorem canonicalZeroSlice_contDiff :
    ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

private theorem inputActual_coframe_contDiff :
    ContDiff ℝ ∞ InputActual.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
      internal coordinate

private def inputActualCoframeJetCarrier
    (point : BasePoint) : IdentityECCoframeJetCarrier :=
  (InputActual.coframe point,
    (holonomicCoframeFirstJetAt InputActual.coframe point).derivative)

private theorem inputActualCoframeJetCarrier_contDiff :
    ContDiff ℝ ∞ inputActualCoframeJetCarrier := by
  refine inputActual_coframe_contDiff.prodMk ?_
  apply contDiff_pi'
  intro derivativeDirection
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  let component : BasePoint → ℝ := fun point =>
    InputActual.coframe point internal coordinate
  have componentSmooth : ContDiff ℝ ∞ component :=
    contDiff_pi.mp (contDiff_pi.mp inputActual_coframe_contDiff internal)
      coordinate
  have familySmooth : ContDiff ℝ ∞
      (Function.uncurry (fun _ : BasePoint => component)) :=
    componentSmooth.comp contDiff_snd
  have derivativeSmooth : ContDiff ℝ ∞ fun point =>
      fderiv ℝ component point := by
    simpa only [Function.uncurry_apply_pair, id_eq] using
      familySmooth.fderiv
        (contDiff_id : ContDiff ℝ ∞ (fun point : BasePoint => point))
        (by simp)
  change ContDiff ℝ ∞
    (fun point =>
      fderiv ℝ component point
        (coordinateDirection derivativeDirection))
  exact derivativeSmooth.clm_apply contDiff_const

private theorem inputActualCoframeJetCarrier_zeroSlice
    (space : StageNineSpatialPoint) :
    inputActualCoframeJetCarrier (canonicalCauchySlicePoint 0 space) =
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  unfold inputActualCoframeJetCarrier
  have jet :
      holonomicCoframeFirstJetAt InputActual.coframe
          (canonicalCauchySlicePoint 0 space) =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) := by
    rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
      fixedP506JointActionSuccessor_coframe,
      fixedGlobalMatterDualP286Complete_coframe,
      fixedGlobalMatterDualFullCauchy_coframe,
      fixedGlobalFullCauchy_coframe]
    exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice space
  exact congrArg (fun actual => (actual.coframe, actual.derivative)) jet

private theorem inputActualSpinResponse_zeroSlice_differentiableAt
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          InputActual (canonicalCauchySlicePoint 0 candidate))
      space := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeOne : InputActual.coframe point = 1 := by
    exact fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have outer : DifferentiableAt ℝ
      (diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource InputActual)
      (point, InputActual.coframe point) := by
    exact
      (diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
        positiveSmoothUnifiedSource InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        point (InputActual.coframe point)
        (by rw [coframeOne]; simp)).differentiableAt (by simp)
  have inner : DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        (canonicalCauchySlicePoint 0 candidate,
          InputActual.coframe (canonicalCauchySlicePoint 0 candidate)))
      space := by
    exact
      ((canonicalZeroSlice_contDiff.prodMk
        (inputActual_coframe_contDiff.comp canonicalZeroSlice_contDiff)
        ).differentiable (by simp)).differentiableAt
  have composed := outer.comp space inner
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        InputActual (canonicalCauchySlicePoint 0 candidate)) =
    fun candidate =>
      diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource InputActual
        (canonicalCauchySlicePoint 0 candidate,
          InputActual.coframe (canonicalCauchySlicePoint 0 candidate)) by
      funext candidate
      exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
        positiveSmoothUnifiedSource InputActual
          (canonicalCauchySlicePoint 0 candidate)]
  exact composed

private def inputActualCoframeSpinResponseCarrier
    (space : StageNineSpatialPoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (InputActual.coframe (canonicalCauchySlicePoint 0 space),
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual (canonicalCauchySlicePoint 0 space))

private theorem
    inputActualCoframeSpinResponseCarrier_differentiableAt
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ inputActualCoframeSpinResponseCarrier space := by
  exact
    (((inputActual_coframe_contDiff.comp canonicalZeroSlice_contDiff
      ).differentiable (by simp)).differentiableAt.prodMk
        (inputActualSpinResponse_zeroSlice_differentiableAt space))

private theorem
    inputActualCartanContorsion_component_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource InputActual
          (canonicalCauchySlicePoint 0 candidate)
          formDirection internalPair)
      space := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual (canonicalCauchySlicePoint 0 space)
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierAt :
      inputActualCoframeSpinResponseCarrier space =
        ((1 : LorentzianCoframe), response) := by
    unfold inputActualCoframeSpinResponseCarrier response
    rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
  have outerAt : DifferentiableAt ℝ outer
      (inputActualCoframeSpinResponseCarrier space) := by
    rw [carrierAt]
    exact
      cartanContorsionCoframeResponseComponent_differentiableAt
        (1 : LorentzianCoframe) response (by simp)
        formDirection internalPair
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      diracDualFormNativeActionCartanContorsionAt
        positiveSmoothUnifiedSource InputActual
        (canonicalCauchySlicePoint 0 candidate)
        formDirection internalPair) =
      outer ∘ inputActualCoframeSpinResponseCarrier by rfl]
  exact outerAt.comp space
    (inputActualCoframeSpinResponseCarrier_differentiableAt space)

private theorem
    inputActualLeviCivita_component_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        (holonomicCoframeFirstJetAt InputActual.coframe
          (canonicalCauchySlicePoint 0 candidate)).lorentzSpinConnection
            formDirection internalOut internalIn)
      space := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : DifferentiableAt ℝ outer
      (inputActualCoframeJetCarrier
        (canonicalCauchySlicePoint 0 space)) := by
    rw [inputActualCoframeJetCarrier_zeroSlice]
    exact
      identityECSpinConnectionComponentOfCarrier_differentiableAt
        formDirection internalOut internalIn
  have inner : DifferentiableAt ℝ
      (inputActualCoframeJetCarrier ∘ canonicalCauchySlicePoint 0) space :=
    ((inputActualCoframeJetCarrier_contDiff.comp canonicalZeroSlice_contDiff
      ).differentiable (by simp)).differentiableAt
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      (holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 candidate)).lorentzSpinConnection
          formDirection internalOut internalIn) =
      outer ∘ (inputActualCoframeJetCarrier ∘ canonicalCauchySlicePoint 0) by
        rfl]
  exact outerAt.comp space inner

private theorem
    inputActualCartanConnection_component_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource InputActual
          (canonicalCauchySlicePoint 0 candidate)
          formDirection internalOut internalIn)
      space := by
  have levi :=
    inputActualLeviCivita_component_differentiableAt_zeroSlice
      space formDirection internalOut internalIn
  have contorsionSum : DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource InputActual
              (canonicalCauchySlicePoint 0 candidate)
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn)
      space := by
    apply DifferentiableAt.fun_sum
    intro internalPair _
    exact
      (inputActualCartanContorsion_component_differentiableAt_zeroSlice
        space formDirection internalPair).mul_const _
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contorsionSum.const_mul _)

/-- The source/action-generated Cartan origin is a differentiable spatial
field on the fixed P506/L0 lineage.  This is the analytic producer needed to
make the full-joint origin profile `Ω` carry an actual spatial first jet. -/
theorem fixedP506L0CartanRestartActual_gravityConnection_origin_component_differentiableAt
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun candidate : StageNineSpatialPoint =>
        (fixedP506L0CartanRestartActual candidate).gravityConnection 0
          formDirection internalOut internalIn)
      space := by
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      (fixedP506L0CartanRestartActual candidate).gravityConnection 0
        formDirection internalOut internalIn) =
    (fun candidate =>
      diracDualFormNativeActionCartanConnectionAt
        positiveSmoothUnifiedSource InputActual
        (canonicalCauchySlicePoint 0 candidate)
        formDirection internalOut internalIn) by
      funext candidate
      exact congrFun (congrFun (congrFun
        (fixedP506L0CartanRestartActual_connection_origin_eq_zeroSliceAction
          candidate) formDirection) internalOut) internalIn]
  exact inputActualCartanConnection_component_differentiableAt_zeroSlice
    space formDirection internalOut internalIn

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionRegularity
