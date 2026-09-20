import H0mework.Physics.CartanAction.CartanAlgebraicSmoothness
import H0mework.Physics.RecenteredJoint.FixedCauchyEvolutionRegularity
import H0mework.Physics.RecenteredJoint.FixedFullJointConnectionOriginRegularity

/-!
# Fixed P506/L0 Cartan-restart curvature regularity

The fixed action-owned Cartan restart is smooth enough for its literal
`dω + ω ∧ ω` curvature at the recentered origin to vary smoothly with the
source-owned spatial occurrence.  The proof differentiates the actual
Cartan connection generated from the fixed P506/L0 input and transports its
first jet through the canonical spatial translation.

No curvature target, residual, field equation, or acceptance certificate is
accepted as input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanRestartCurvatureSpatialRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
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

private def InputCartanActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource InputActual

private theorem canonicalSpatialContactTranslation_zero_local
    (space : StageNineSpatialPoint) :
    canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold canonicalSpatialContactTranslation
  exact add_zero _

private theorem fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
    (field : BasePoint → ℝ)
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

private theorem inputActualSpinResponse_contDiffAt_zeroSlicePoint
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource InputActual)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeOne : InputActual.coframe point = 1 :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have outer : ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource InputActual)
      (point, InputActual.coframe point) := by
    exact
      diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
        positiveSmoothUnifiedSource InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        point (InputActual.coframe point)
        (by rw [coframeOne]; simp)
  have inner : ContDiffAt ℝ ∞
      (fun candidate : BasePoint =>
        (candidate, InputActual.coframe candidate))
      point :=
    contDiffAt_id.prodMk inputActual_coframe_contDiff.contDiffAt
  have composed := outer.comp point inner
  rw [show
    diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource InputActual =
      fun candidate =>
        diracDualFormNativeActionSpinResponsePointCoframe
          positiveSmoothUnifiedSource InputActual
          (candidate, InputActual.coframe candidate) by
    funext candidate
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource InputActual candidate]
  exact composed

private def inputActualCoframeSpinResponsePointCarrier
    (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (InputActual.coframe point,
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual point)

private theorem inputActualCoframeSpinResponsePointCarrier_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞ inputActualCoframeSpinResponsePointCarrier
      (canonicalCauchySlicePoint 0 space) := by
  exact inputActual_coframe_contDiff.contDiffAt.prodMk
    (inputActualSpinResponse_contDiffAt_zeroSlicePoint space)

private theorem inputActualCartanContorsion_component_contDiffAt_zeroSlicePoint
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource InputActual point
          formDirection internalPair)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual point
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierAt :
      inputActualCoframeSpinResponsePointCarrier point =
        ((1 : LorentzianCoframe), response) := by
    unfold inputActualCoframeSpinResponsePointCarrier response point
    rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeSpinResponsePointCarrier point) := by
    rw [carrierAt]
    exact
      cartanContorsionCoframeResponseComponent_contDiffAt
        (1 : LorentzianCoframe) response (by simp)
        formDirection internalPair
  rw [show
    (fun candidate : BasePoint =>
      diracDualFormNativeActionCartanContorsionAt
        positiveSmoothUnifiedSource InputActual candidate
        formDirection internalPair) =
      outer ∘ inputActualCoframeSpinResponsePointCarrier by rfl]
  exact outerAt.comp point
    (inputActualCoframeSpinResponsePointCarrier_contDiffAt space)

private theorem inputActualLeviCivita_component_contDiffAt_zeroSlicePoint
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        (holonomicCoframeFirstJetAt InputActual.coframe point)
          |>.lorentzSpinConnection
            formDirection internalOut internalIn)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeJetCarrier point) := by
    rw [show point = canonicalCauchySlicePoint 0 space by rfl,
      inputActualCoframeJetCarrier_zeroSlice]
    exact
      identityECSpinConnectionComponentOfCarrier_contDiffAt
        formDirection internalOut internalIn
  rw [show
    (fun candidate : BasePoint =>
      (holonomicCoframeFirstJetAt InputActual.coframe candidate)
        |>.lorentzSpinConnection
          formDirection internalOut internalIn) =
      outer ∘ inputActualCoframeJetCarrier by rfl]
  exact outerAt.comp point inputActualCoframeJetCarrier_contDiff.contDiffAt

private theorem inputActualCartanConnection_component_contDiffAt_zeroSlicePoint
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource InputActual point
          formDirection internalOut internalIn)
      (canonicalCauchySlicePoint 0 space) := by
  have levi :=
    inputActualLeviCivita_component_contDiffAt_zeroSlicePoint
      space formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource InputActual point
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn)
      (canonicalCauchySlicePoint 0 space) := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (inputActualCartanContorsion_component_contDiffAt_zeroSlicePoint
        space formDirection internalPair).mul contDiffAt_const
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

private theorem inputCartanActual_connection_component_contDiffAt_zeroSlicePoint
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        InputCartanActual.gravityConnection point
          formDirection internalOut internalIn)
      (canonicalCauchySlicePoint 0 space) := by
  simpa only [InputCartanActual,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
    using
      inputActualCartanConnection_component_contDiffAt_zeroSlicePoint
        space formDirection internalOut internalIn

private theorem inputActualSpinResponse_zeroSlice_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          InputActual (canonicalCauchySlicePoint 0 candidate))
      space := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeOne : InputActual.coframe point = 1 :=
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space
  have outer : ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource InputActual)
      (point, InputActual.coframe point) := by
    exact
      diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
        positiveSmoothUnifiedSource InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        point (InputActual.coframe point)
        (by rw [coframeOne]; simp)
  have inner : ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        (canonicalCauchySlicePoint 0 candidate,
          InputActual.coframe (canonicalCauchySlicePoint 0 candidate)))
      space :=
    (canonicalZeroSlice_contDiff.prodMk
      (inputActual_coframe_contDiff.comp canonicalZeroSlice_contDiff)
      ).contDiffAt
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

private theorem inputActualCoframeSpinResponseCarrier_contDiffAt
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞ inputActualCoframeSpinResponseCarrier space := by
  exact
    (inputActual_coframe_contDiff.comp canonicalZeroSlice_contDiff
      ).contDiffAt.prodMk
        (inputActualSpinResponse_zeroSlice_contDiffAt space)

private theorem inputActualCartanContorsion_component_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ ∞
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
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeSpinResponseCarrier space) := by
    rw [carrierAt]
    exact
      cartanContorsionCoframeResponseComponent_contDiffAt
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
    (inputActualCoframeSpinResponseCarrier_contDiffAt space)

private theorem inputActualLeviCivita_component_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        (holonomicCoframeFirstJetAt InputActual.coframe
          (canonicalCauchySlicePoint 0 candidate)).lorentzSpinConnection
            formDirection internalOut internalIn)
      space := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeJetCarrier
        (canonicalCauchySlicePoint 0 space)) := by
    rw [inputActualCoframeJetCarrier_zeroSlice]
    exact
      identityECSpinConnectionComponentOfCarrier_contDiffAt
        formDirection internalOut internalIn
  have inner : ContDiffAt ℝ ∞
      (inputActualCoframeJetCarrier ∘ canonicalCauchySlicePoint 0) space :=
    (inputActualCoframeJetCarrier_contDiff.comp canonicalZeroSlice_contDiff
      ).contDiffAt
  rw [show
    (fun candidate : StageNineSpatialPoint =>
      (holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalCauchySlicePoint 0 candidate)).lorentzSpinConnection
          formDirection internalOut internalIn) =
      outer ∘ (inputActualCoframeJetCarrier ∘ canonicalCauchySlicePoint 0) by
        rfl]
  exact outerAt.comp space inner

private theorem inputActualCartanConnection_component_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource InputActual
          (canonicalCauchySlicePoint 0 candidate)
          formDirection internalOut internalIn)
      space := by
  have levi :=
    inputActualLeviCivita_component_contDiffAt_zeroSlice
      space formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource InputActual
              (canonicalCauchySlicePoint 0 candidate)
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn)
      space := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (inputActualCartanContorsion_component_contDiffAt_zeroSlice
        space formDirection internalPair).mul contDiffAt_const
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

private theorem inputCartanActual_connection_component_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate : StageNineSpatialPoint =>
        InputCartanActual.gravityConnection
          (canonicalCauchySlicePoint 0 candidate)
          formDirection internalOut internalIn)
      space := by
  simpa only [InputCartanActual,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
    using
      inputActualCartanConnection_component_contDiffAt_zeroSlice
        space formDirection internalOut internalIn

private theorem inputCartanActual_connection_component_zeroSlice_contDiff
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun space : StageNineSpatialPoint =>
        InputCartanActual.gravityConnection
          (canonicalCauchySlicePoint 0 space)
          formDirection internalOut internalIn) := by
  rw [contDiff_iff_contDiffAt]
  intro space
  exact
    inputCartanActual_connection_component_contDiffAt_zeroSlice
      space formDirection internalOut internalIn

private theorem inputCartanActual_connectionDerivative_zeroSlice_contDiff
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      gravityConnectionDerivative InputCartanActual
        (canonicalCauchySlicePoint 0 space)
        derivativeDirection formDirection internalOut internalIn := by
  rw [contDiff_iff_contDiffAt]
  intro space
  let coordinate : BasePoint → ℝ := fun point =>
    InputCartanActual.gravityConnection point
      formDirection internalOut internalIn
  have coordinateSmooth : ContDiffAt ℝ ∞ coordinate
      (canonicalCauchySlicePoint 0 space) :=
    inputCartanActual_connection_component_contDiffAt_zeroSlicePoint
      space formDirection internalOut internalIn
  have jointSmooth : ContDiffAt ℝ ∞
      (Function.uncurry
        (fun _ : StageNineSpatialPoint => coordinate))
      (space, canonicalCauchySlicePoint 0 space) :=
    coordinateSmooth.comp
      (space, canonicalCauchySlicePoint 0 space) contDiffAt_snd
  have derivativeSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        fderiv ℝ coordinate (canonicalCauchySlicePoint 0 candidate))
      space := by
    simpa only [Function.uncurry_apply_pair] using
      jointSmooth.fderiv canonicalZeroSlice_contDiff.contDiffAt (by simp)
  unfold gravityConnectionDerivative
  exact derivativeSmooth.clm_apply contDiffAt_const

private theorem inputCartanActual_curvature_zeroSlice_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature InputCartanActual
        (canonicalCauchySlicePoint 0 space)
        internalPair spacetimePair := by
  unfold holonomicGravityCurvature
  dsimp only
  apply contDiff_const.mul
  apply ContDiff.add
  · apply ContDiff.sub
    · exact
        inputCartanActual_connectionDerivative_zeroSlice_contDiff
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair)
    · exact
        inputCartanActual_connectionDerivative_zeroSlice_contDiff
          (pairSecond spacetimePair) (pairFirst spacetimePair)
          (pairFirst internalPair) (pairSecond internalPair)
  · apply ContDiff.sum
    intro middle _
    exact
      ((inputCartanActual_connection_component_zeroSlice_contDiff
          (pairFirst spacetimePair) (pairFirst internalPair) middle).mul
        (inputCartanActual_connection_component_zeroSlice_contDiff
          (pairSecond spacetimePair) middle
          (pairSecond internalPair))).sub
      ((inputCartanActual_connection_component_zeroSlice_contDiff
          (pairSecond spacetimePair) (pairFirst internalPair) middle).mul
        (inputCartanActual_connection_component_zeroSlice_contDiff
          (pairFirst spacetimePair) middle
          (pairSecond internalPair)))

private theorem recenteredInput_coframeFirstJet_eq_translation
    (space : StageNineSpatialPoint) (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (fixedP506L0RecenteredInput space).coframe point =
      holonomicCoframeFirstJetAt InputActual.coframe
        (canonicalSpatialContactTranslation space point) := by
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    let component : BasePoint → ℝ := fun candidate =>
      InputActual.coframe candidate internal coordinate
    have differentiable : DifferentiableAt ℝ component
        (canonicalSpatialContactTranslation space point) :=
      ((fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
        internal coordinate).differentiable (by simp)).differentiableAt
    change
      fieldDirectionalDerivative
          (component ∘ canonicalSpatialContactTranslation space) point
          derivativeDirection =
        fieldDirectionalDerivative component
          (canonicalSpatialContactTranslation space point)
          derivativeDirection
    exact
      fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation
        component space point derivativeDirection differentiable

private theorem recenteredInput_spinResponse_eq_translation
    (space : StageNineSpatialPoint) (point : BasePoint) :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        (fixedP506L0RecenteredInput space) point =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        InputActual (canonicalSpatialContactTranslation space point) := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  all_goals
    rfl

private theorem recenteredInput_actionCartanConnection_eq_translation
    (space : StageNineSpatialPoint) (point : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedP506L0RecenteredInput space) point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual (canonicalSpatialContactTranslation space point) := by
  have coframeEq :
      (fixedP506L0RecenteredInput space).coframe point =
        InputActual.coframe
          (canonicalSpatialContactTranslation space point) :=
    rfl
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recenteredInput_coframeFirstJet_eq_translation, coframeEq,
    recenteredInput_spinResponse_eq_translation]

private theorem fixedCartanRestart_connection_component_eq_translation
    (space : StageNineSpatialPoint) (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    (fixedP506L0CartanRestartActual space).gravityConnection point
        formDirection internalOut internalIn =
      InputCartanActual.gravityConnection
        (canonicalSpatialContactTranslation space point)
        formDirection internalOut internalIn := by
  change
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedP506L0RecenteredInput space) point
        formDirection internalOut internalIn =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual (canonicalSpatialContactTranslation space point)
        formDirection internalOut internalIn
  exact congrFun (congrFun (congrFun
    (recenteredInput_actionCartanConnection_eq_translation space point)
    formDirection) internalOut) internalIn

private theorem fixedCartanRestart_connectionDerivative_origin_eq_zeroSlice
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual space) 0
        derivativeDirection formDirection internalOut internalIn =
      gravityConnectionDerivative InputCartanActual
        (canonicalCauchySlicePoint 0 space)
        derivativeDirection formDirection internalOut internalIn := by
  unfold gravityConnectionDerivative
  rw [show
    (fun point =>
      (fixedP506L0CartanRestartActual space).gravityConnection point
        formDirection internalOut internalIn) =
    (fun point =>
      InputCartanActual.gravityConnection
        (canonicalSpatialContactTranslation space point)
        formDirection internalOut internalIn) by
      funext point
      exact fixedCartanRestart_connection_component_eq_translation
        space point formDirection internalOut internalIn]
  change
    fieldDirectionalDerivative
        ((fun point =>
          InputCartanActual.gravityConnection point
            formDirection internalOut internalIn) ∘
          canonicalSpatialContactTranslation space)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (fun point =>
          InputCartanActual.gravityConnection point
            formDirection internalOut internalIn)
        (canonicalCauchySlicePoint 0 space) derivativeDirection
  rw [fieldDirectionalDerivative_comp_canonicalSpatialContactTranslation]
  · rw [canonicalSpatialContactTranslation_zero_local]
  · rw [canonicalSpatialContactTranslation_zero_local]
    exact
      (inputCartanActual_connection_component_contDiffAt_zeroSlicePoint
        space formDirection internalOut internalIn).differentiableAt
        (by simp)

private theorem fixedCartanRestart_curvature_origin_eq_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature (fixedP506L0CartanRestartActual space) 0 =
      holonomicGravityCurvature InputCartanActual
        (canonicalCauchySlicePoint 0 space) := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only
  rw [fixedCartanRestart_connectionDerivative_origin_eq_zeroSlice,
    fixedCartanRestart_connectionDerivative_origin_eq_zeroSlice]
  simp_rw [fixedCartanRestart_connection_component_eq_translation]
  rw [canonicalSpatialContactTranslation_zero_local]

/-- At the fixed P506/L0 origin, every spatial derivative of the
action-native Cartan restart connection vanishes.  This is a direct
whole-slice consequence of the already generated restart: its origin value
is independent of the source-owned spatial occurrence, and recentering
identifies occurrence variation with the corresponding spatial field jet. -/
theorem fixedP506L0CartanRestartActual_connection_spatialDerivative_origin_zero
    (axis : Fin 3)
    (formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative (fixedP506L0CartanRestartActual 0) 0
        axis.succ formDirection internalOut internalIn = 0 := by
  rw [fixedCartanRestart_connectionDerivative_origin_eq_zeroSlice]
  let field : BasePoint → ℝ := fun point =>
    InputCartanActual.gravityConnection point
      formDirection internalOut internalIn
  have fieldDifferentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) := by
    simpa [field] using
      (inputCartanActual_connection_component_contDiffAt_zeroSlicePoint
        0 formDirection internalOut internalIn).differentiableAt (by simp)
  have sliceDerivative :=
    fieldDifferentiable.hasFDerivAt.comp
      (0 : StageNineSpatialPoint)
      (canonicalCauchySlicePoint_hasFDerivAt 0 0)
  have sliceConstant :
      field ∘ canonicalCauchySlicePoint 0 =
        fun _ : StageNineSpatialPoint =>
          field (canonicalCauchySlicePoint 0 0) := by
    funext space
    change
      InputCartanActual.gravityConnection
          (canonicalCauchySlicePoint 0 space)
          formDirection internalOut internalIn =
        InputCartanActual.gravityConnection
          (canonicalCauchySlicePoint 0 0)
          formDirection internalOut internalIn
    calc
      _ = (fixedP506L0CartanRestartActual space).gravityConnection 0
            formDirection internalOut internalIn := by
        rw [fixedCartanRestart_connection_component_eq_translation]
        simp [canonicalSpatialContactTranslation]
      _ = (fixedP506L0CartanRestartActual 0).gravityConnection 0
            formDirection internalOut internalIn := by
        exact congrFun (congrFun (congrFun
          (fixedP506L0CartanRestartActual_gravityConnection_origin_eq_zero
            space) formDirection) internalOut) internalIn
      _ = InputCartanActual.gravityConnection
            (canonicalCauchySlicePoint 0 0)
            formDirection internalOut internalIn := by
        rw [fixedCartanRestart_connection_component_eq_translation]
        simp [canonicalSpatialContactTranslation]
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
  change
    (fderiv ℝ
      (fun point =>
        InputCartanActual.gravityConnection point
          formDirection internalOut internalIn)
      (canonicalCauchySlicePoint 0 0))
        (coordinateDirection axis.succ) = 0
  simpa [field, ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

/-- The fixed P506/L0 action-native Cartan restart has a smooth spatial
origin-curvature profile. -/
theorem fixedP506L0CartanRestartActual_curvature_origin_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature
        (fixedP506L0CartanRestartActual space) 0
        internalPair spacetimePair := by
  rw [show
    (fun space : StageNineSpatialPoint =>
      holonomicGravityCurvature
        (fixedP506L0CartanRestartActual space) 0
        internalPair spacetimePair) =
      (fun space =>
        holonomicGravityCurvature InputCartanActual
          (canonicalCauchySlicePoint 0 space)
          internalPair spacetimePair) by
    funext space
    exact congrFun
      (congrFun
        (fixedCartanRestart_curvature_origin_eq_zeroSlice space)
        internalPair)
      spacetimePair]
  exact
    inputCartanActual_curvature_zeroSlice_component_contDiff
      internalPair spacetimePair

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanRestartCurvatureSpatialRegularity
