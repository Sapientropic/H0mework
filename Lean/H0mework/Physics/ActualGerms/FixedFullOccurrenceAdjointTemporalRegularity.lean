import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.FixedJoint.FixedCartanRestartCurvatureSpatialRegularity
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Fixed P506/L0 full-occurrence adjoint temporal regularity

This module derives local `C¹` regularity of the complete-joint adjoint
temporal correction at the fixed P506/L0 occurrence.  The proof expands the
actual live-coframe response through its finite-dimensional momentum, drift,
principal inverse, Cartan restart, and exact recenter lineage.  It then
differentiates the already generated canonical temporal primitive.

No residual coordinate, target response, branch choice, differentiability
receipt, or global time-independence premise enters the producer.  The
analytic chain is kept in one module because the terminal statement consumes
the fixed current's exact full-occurrence lineage across all of those layers.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanAlgebraicSmoothness
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActualVariationRegularity
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance probeP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance probeP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance probeP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private def InputCartanActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource InputActual

private theorem canonicalZeroSliceOrigin :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

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
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
      internal coordinate
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

private theorem inputActual_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt InputActual.coframe 0 =
      ({ coframe := 1, derivative := 0 } :
        PointwiseLorentzianCoframeJet) := by
  have jet :
      holonomicCoframeFirstJetAt InputActual.coframe
          (canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint)) =
        ({ coframe := 1, derivative := 0 } :
          PointwiseLorentzianCoframeJet) := by
    rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
      fixedP506JointActionSuccessor_coframe,
      fixedGlobalMatterDualP286Complete_coframe,
      fixedGlobalMatterDualFullCauchy_coframe,
      fixedGlobalFullCauchy_coframe]
    exact fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice 0
  rw [canonicalZeroSliceOrigin] at jet
  exact jet

private theorem inputActualSpinResponse_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource InputActual) 0 := by
  have coframeOne : InputActual.coframe 0 = 1 := by
    exact congrArg PointwiseLorentzianCoframeJet.coframe
      inputActual_coframeFirstJet_origin
  have outer : ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource InputActual)
      (0, InputActual.coframe 0) := by
    exact
      diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
        positiveSmoothUnifiedSource InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        0 (InputActual.coframe 0)
        (by rw [coframeOne]; simp)
  have inner : ContDiffAt ℝ ∞
      (fun point : BasePoint => (point, InputActual.coframe point)) 0 :=
    contDiffAt_id.prodMk inputActual_coframe_contDiff.contDiffAt
  have composed := outer.comp 0 inner
  rw [show
    diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource InputActual =
      fun point =>
        diracDualFormNativeActionSpinResponsePointCoframe
          positiveSmoothUnifiedSource InputActual
          (point, InputActual.coframe point) by
    funext point
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource InputActual point]
  exact composed

private def inputActualCoframeSpinResponseCarrier
    (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (InputActual.coframe point,
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual point)

private theorem inputActualCoframeSpinResponseCarrier_contDiffAt_origin :
    ContDiffAt ℝ ∞ inputActualCoframeSpinResponseCarrier 0 :=
  inputActual_coframe_contDiff.contDiffAt.prodMk
    inputActualSpinResponse_contDiffAt_origin

private theorem inputActualCartanContorsion_component_contDiffAt_origin
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource InputActual point
          formDirection internalPair) 0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      InputActual 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have coframeOne : InputActual.coframe 0 = 1 := by
    exact congrArg PointwiseLorentzianCoframeJet.coframe
      inputActual_coframeFirstJet_origin
  have carrierAt :
      inputActualCoframeSpinResponseCarrier 0 =
        ((1 : LorentzianCoframe), response) := by
    unfold inputActualCoframeSpinResponseCarrier response
    rw [coframeOne]
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeSpinResponseCarrier 0) := by
    rw [carrierAt]
    exact
      cartanContorsionCoframeResponseComponent_contDiffAt
        (1 : LorentzianCoframe) response (by simp)
        formDirection internalPair
  rw [show
    (fun point : BasePoint =>
      diracDualFormNativeActionCartanContorsionAt
        positiveSmoothUnifiedSource InputActual point
        formDirection internalPair) =
      outer ∘ inputActualCoframeSpinResponseCarrier by rfl]
  exact outerAt.comp 0
    inputActualCoframeSpinResponseCarrier_contDiffAt_origin

private theorem inputActualLeviCivita_component_contDiffAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        (holonomicCoframeFirstJetAt InputActual.coframe point)
          |>.lorentzSpinConnection
            formDirection internalOut internalIn) 0 := by
  let outer := identityECSpinConnectionComponentOfCarrier
    formDirection internalOut internalIn
  have outerAt : ContDiffAt ℝ ∞ outer
      (inputActualCoframeJetCarrier 0) := by
    have carrierOrigin :
        inputActualCoframeJetCarrier 0 =
          ((1 : LorentzianCoframe),
            (0 : LorentzianCoframeDerivative)) := by
      unfold inputActualCoframeJetCarrier
      exact congrArg
        (fun jet : PointwiseLorentzianCoframeJet =>
          (jet.coframe, jet.derivative))
        inputActual_coframeFirstJet_origin
    rw [carrierOrigin]
    exact
      identityECSpinConnectionComponentOfCarrier_contDiffAt
        formDirection internalOut internalIn
  rw [show
    (fun point : BasePoint =>
      (holonomicCoframeFirstJetAt InputActual.coframe point)
        |>.lorentzSpinConnection
          formDirection internalOut internalIn) =
      outer ∘ inputActualCoframeJetCarrier by rfl]
  exact outerAt.comp 0 inputActualCoframeJetCarrier_contDiff.contDiffAt

private theorem inputCartanActual_connection_component_contDiffAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        InputCartanActual.gravityConnection point
          formDirection internalOut internalIn) 0 := by
  have levi :=
    inputActualLeviCivita_component_contDiffAt_origin
      formDirection internalOut internalIn
  have contorsionSum : ContDiffAt ℝ ∞
      (fun point : BasePoint =>
        ∑ internalPair : Fin 6,
          diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource InputActual point
              formDirection internalPair *
            orientedLorentzBivectorBasisCoefficient internalPair
              internalOut internalIn) 0 := by
    apply ContDiffAt.sum
    intro internalPair _
    exact
      (inputActualCartanContorsion_component_contDiffAt_origin
        formDirection internalPair).mul contDiffAt_const
  unfold InputCartanActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  unfold diracDualFormNativeActionCartanConnectionAt
    cartanAffineSpinConnection lorentzSkewConnectionOfBivectorOneForm
    loweredLorentzBivectorMatrix
  exact levi.add (contDiffAt_const.mul contorsionSum)

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

private theorem liveCoframeAlgebraicDual_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier) :
    holonomicDiracDualLiveCoframeAlgebraicDual configuration point vector =
      ((generatedVolumeDensity
        (toContinuumPointField configuration point) : ℝ) : ℂ) *
        configuration.conjugateMatter point
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            configuration point) vector) :=
  rfl

private theorem liveCoframeKnownDensitizedDual_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier) :
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        configuration point vector =
      holonomicDiracDualLiveCoframeAlgebraicDual configuration point vector -
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              configuration point)
            vector -
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              configuration point)
            vector -
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              configuration point)
            vector :=
  rfl

private theorem liveCoframeActionVelocity_apply
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (vector : DiracExteriorMatterCarrier) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration point vector =
      (((generatedVolumeDensity
        (toContinuumPointField configuration point) : ℝ) : ℂ)⁻¹) *
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          configuration point
          (currentCoframeMatterTemporalPrincipalInverse
            (configuration.coframe point) vector) :=
  rfl

/-- The live adjoint action velocity is determined by its complete local
coframe/connection/scalar/dual-matter first-jet data. -/
theorem liveCoframeActionVelocity_eq_of_pointData
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (coframeJet :
      holonomicCoframeFirstJetAt first.coframe firstPoint =
        holonomicCoframeFirstJetAt second.coframe secondPoint)
    (connection :
      first.gravityConnection firstPoint =
        second.gravityConnection secondPoint)
    (gauge :
      first.gaugeConnection firstPoint =
        second.gaugeConnection secondPoint)
    (scalar :
      first.scalar firstPoint = second.scalar secondPoint)
    (conjugate :
      first.conjugateMatter firstPoint =
        second.conjugateMatter secondPoint)
    (conjugateDerivative :
      ∀ direction : LorentzianIndex,
        holonomicConjugateMatterDerivativeDual first firstPoint direction =
          holonomicConjugateMatterDerivativeDual second secondPoint
            direction) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        first firstPoint =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        second secondPoint := by
  have coframe :
      first.coframe firstPoint = second.coframe secondPoint :=
    congrArg PointwiseLorentzianCoframeJet.coframe coframeJet
  have conjugateCoordinates :
      holonomicConjugateMatterCoordinates first firstPoint =
        holonomicConjugateMatterCoordinates second secondPoint := by
    unfold holonomicConjugateMatterCoordinates
    rw [conjugate]
  have volume :
      generatedVolumeDensity (toContinuumPointField first firstPoint) =
        generatedVolumeDensity (toContinuumPointField second secondPoint) := by
    unfold generatedVolumeDensity toContinuumPointField
    rw [coframe]
  unfold holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
    holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
    holonomicDiracDualLiveCoframeAlgebraicDual
    holonomicDiracDualLiveCoframeMatterAlgebraicOperator
    holonomicIdentityCoframeMatterConnectionOperator
    holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
    holonomicLiveCoframeSpatialPrincipalDriftCoordinates
    holonomicLiveCoframeTemporalPrincipalDriftCoordinates
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
    holonomicLiveCoframeAffineGerm
  rw [coframe, volume, connection, gauge, scalar, conjugate, coframeJet,
    conjugateCoordinates]
  simp_rw [conjugateDerivative]

private theorem
    liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt_one
    (direction : LorentzianIndex)
    (coordinates : MatterCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (liveCoframeDensitizedAdjointMomentumCoordinates direction)
      ((1 : LorentzianCoframe), coordinates) := by
  apply contDiffAt_piLp'
  intro index
  unfold liveCoframeDensitizedAdjointMomentumCoordinates
    matterDualCoordinates
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  have volumeReal : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        abs (Matrix.det joint.1))
      ((1 : LorentzianCoframe), coordinates) :=
    (StageNineCoframeVariation.coframe_volume_contDiffAt
      (1 : LorentzianCoframe) (by simp)).comp
        ((1 : LorentzianCoframe), coordinates) contDiffAt_fst
  have volumeComplex : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        ((abs (Matrix.det joint.1) : ℝ) : ℂ))
      ((1 : LorentzianCoframe), coordinates) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp
      ((1 : LorentzianCoframe), coordinates) volumeReal
  have pairingSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        (matterDualOfCoordinates joint.2)
          ((liveCoframeMatterPrincipal joint.1 direction)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      ((1 : LorentzianCoframe), coordinates) := by
    rw [show
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        (matterDualOfCoordinates joint.2)
          ((liveCoframeMatterPrincipal joint.1 direction)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))) =
      fun joint =>
        ∑ coordinate : MatterCoordinateIndex,
          matterCoordinateEquiv
              ((liveCoframeMatterPrincipal joint.1 direction)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ))))
              coordinate *
            joint.2 coordinate by
      funext joint
      exact matterDualOfCoordinates_apply _ _]
    apply ContDiffAt.sum
    intro coordinate _
    have gammaSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          inverseCoframeDiracGamma
            { coframe := joint.1, derivative := 0 } direction)
        ((1 : LorentzianCoframe), coordinates) :=
      by
        let gamma := fun candidate : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := candidate, derivative := 0 } direction
        have outer : ContDiffAt ℝ ∞ gamma (1 : LorentzianCoframe) :=
          inverseCoframeDiracGamma_contDiffAt
            (1 : LorentzianCoframe) (by simp) direction
        have inner : ContDiffAt ℝ ∞
            (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
              joint.1)
            ((1 : LorentzianCoframe), coordinates) :=
          contDiffAt_fst
        have composed : ContDiffAt ℝ ∞
            (gamma ∘
              (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
                joint.1))
            ((1 : LorentzianCoframe), coordinates) :=
          outer.comp ((1 : LorentzianCoframe), coordinates) inner
        change ContDiffAt ℝ ∞
          (gamma ∘
            (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
              joint.1))
          ((1 : LorentzianCoframe), coordinates)
        exact composed
    have basisCoordinatesSmooth : ContDiffAt ℝ ∞
        (fun _ : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        ((1 : LorentzianCoframe), coordinates) :=
      contDiffAt_const
    have gammaActionSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.1, derivative := 0 } direction)
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))))
        ((1 : LorentzianCoframe), coordinates) := by
      have actual :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.contDiffAt.comp
            ((1 : LorentzianCoframe), coordinates) gammaSmooth).clm_apply
              basisCoordinatesSmooth
      change ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.1, derivative := 0 } direction)
              (matterCoordinateEquiv.symm
                (matterCoordinateEquiv
                  (matterCoordinateEquiv.symm
                    (EuclideanSpace.single index (1 : ℂ)))))))
        ((1 : LorentzianCoframe), coordinates) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    have principalCarrierSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal joint.1 direction)
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))))
        ((1 : LorentzianCoframe), coordinates) := by
      unfold liveCoframeMatterPrincipal
      simp only [LinearMap.smul_apply, map_smul]
      exact
        (contDiffAt_const :
          ContDiffAt ℝ ∞
            (fun _ : LorentzianCoframe × MatterCoordinateCarrier =>
              (Complex.I : ℂ))
            ((1 : LorentzianCoframe), coordinates)).smul gammaActionSmooth
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj coordinate).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
    have principalCoordinateSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
              ((liveCoframeMatterPrincipal joint.1 direction)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ))))
              coordinate)
        ((1 : LorentzianCoframe), coordinates) := by
      exact (projection.restrictScalars ℝ).contDiff.contDiffAt.comp
        ((1 : LorentzianCoframe), coordinates) principalCarrierSmooth
    have dualCoordinateSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          joint.2 coordinate)
        ((1 : LorentzianCoframe), coordinates) := by
      fun_prop
    exact principalCoordinateSmooth.mul dualCoordinateSmooth
  exact volumeComplex.mul pairingSmooth

private theorem inputActual_affineCoframeFamily_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt InputActual.coframe joint.1)
          joint.2)
      (0, 0) := by
  apply contDiffAt_pi'
  intro internal
  apply contDiffAt_pi'
  intro coordinate
  unfold affineCoframeFieldOfJet coframeJetAffineComponentLinear
  simp only [sum_apply, smul_apply, smul_eq_mul]
  have coframeSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        InputActual.coframe joint.1 internal coordinate)
      (0, 0) :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp
        ((inputActual_coframe_contDiff.comp contDiff_fst).contDiffAt)
        internal)
      coordinate
  have derivativeSmooth : ∀ derivativeDirection : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun joint : BasePoint × BasePoint =>
          (inputActualCoframeJetCarrier joint.1).2 derivativeDirection
            internal coordinate)
        (0, 0) := by
    intro derivativeDirection
    have carrierSmooth : ContDiff ℝ ∞
        (fun joint : BasePoint × BasePoint =>
          inputActualCoframeJetCarrier joint.1) :=
      inputActualCoframeJetCarrier_contDiff.comp contDiff_fst
    exact
      contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (contDiffAt_pi.mp
            ((contDiff_snd.comp carrierSmooth).contDiffAt)
            derivativeDirection)
          internal)
        coordinate
  exact
    coframeSmooth.add
      (ContDiffAt.sum fun derivativeDirection _ =>
        (derivativeSmooth derivativeDirection).mul
            ((coframeBaseCoordinate derivativeDirection).contDiff.contDiffAt.comp
              (0, 0) contDiffAt_snd))

private theorem
    inputCartanActual_liveCoframeDensitizedMomentumFamily_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (Function.uncurry
        (fun point : BasePoint => fun localPoint : BasePoint =>
          liveCoframeDensitizedAdjointMomentumCoordinates direction
            (affineCoframeFieldOfJet
                (holonomicCoframeFirstJetAt InputActual.coframe point)
                localPoint,
              holonomicConjugateMatterCoordinates InputCartanActual point)))
      (0, 0) := by
  have conjugateCoordinatesSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        holonomicConjugateMatterCoordinates InputCartanActual joint.1)
      (0, 0) := by
    have base : ContDiff ℝ ∞
        (holonomicConjugateMatterCoordinates InputActual) :=
      holonomicConjugateMatterCoordinates_contDiff InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
    rw [show
      (fun joint : BasePoint × BasePoint =>
        holonomicConjugateMatterCoordinates InputCartanActual joint.1) =
      fun joint =>
        holonomicConjugateMatterCoordinates InputActual joint.1 by
      funext joint
      unfold holonomicConjugateMatterCoordinates InputCartanActual
      rw [
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
    exact base.contDiffAt.comp (0, 0) contDiffAt_fst
  have inner : ContDiffAt ℝ ∞
      (fun joint : BasePoint × BasePoint =>
        (affineCoframeFieldOfJet
            (holonomicCoframeFirstJetAt InputActual.coframe joint.1)
            joint.2,
          holonomicConjugateMatterCoordinates InputCartanActual joint.1))
      (0, 0) :=
    inputActual_affineCoframeFamily_contDiffAt_origin.prodMk
      conjugateCoordinatesSmooth
  have innerValue :
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt InputActual.coframe 0) 0,
        holonomicConjugateMatterCoordinates InputCartanActual 0) =
      ((1 : LorentzianCoframe),
        holonomicConjugateMatterCoordinates InputCartanActual 0) := by
    rw [affineCoframeFieldOfJet_origin, inputActual_coframeFirstJet_origin]
  have outer :=
    liveCoframeDensitizedAdjointMomentumCoordinates_contDiffAt_one
      direction (holonomicConjugateMatterCoordinates InputCartanActual 0)
  rw [← innerValue] at outer
  exact outer.comp (0, 0) inner

private theorem
    inputCartanActual_liveCoframeDensitizedPrincipalDrift_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun point =>
        holonomicLiveCoframeDensitizedPrincipalDriftCoordinates
          InputCartanActual point direction)
      0 := by
  let family := fun point : BasePoint => fun localPoint : BasePoint =>
    liveCoframeDensitizedAdjointMomentumCoordinates direction
      (affineCoframeFieldOfJet
          (holonomicCoframeFirstJetAt InputActual.coframe point)
          localPoint,
        holonomicConjugateMatterCoordinates InputCartanActual point)
  have familyC2 : ContDiffAt ℝ 2 (Function.uncurry family) (0, 0) :=
    (inputCartanActual_liveCoframeDensitizedMomentumFamily_contDiffAt_origin
      direction).of_le (by decide)
  have sectionC1 : ContDiffAt ℝ 1 (fun _ : BasePoint => (0 : BasePoint)) 0 :=
    contDiffAt_const
  have derivativeC1 : ContDiffAt ℝ 1
      (fun point => fderiv ℝ (family point) 0)
      0 := by
    exact ContDiffAt.fderiv (m := 1) familyC2 sectionC1 (by norm_num)
  have evaluated :=
    derivativeC1.clm_apply
      (contDiffAt_const :
        ContDiffAt ℝ 1
          (fun _ : BasePoint => coordinateDirection direction) 0)
  change ContDiffAt ℝ 1
    (fun point =>
      fderiv ℝ
          (fun localPoint =>
            liveCoframeDensitizedAdjointMomentumCoordinates direction
              (affineCoframeFieldOfJet
                  (holonomicCoframeFirstJetAt InputActual.coframe point)
                  localPoint,
                holonomicConjugateMatterCoordinates InputCartanActual point))
          0 (coordinateDirection direction))
      0 at evaluated
  simpa [InputCartanActual, family,
    holonomicLiveCoframeDensitizedPrincipalDriftCoordinates,
    holonomicLiveCoframeAffineGerm, fieldDirectionalDerivative] using
      evaluated

private theorem inputCartanActual_coframe_origin :
    InputCartanActual.coframe 0 = 1 := by
  change InputActual.coframe 0 = 1
  exact congrArg PointwiseLorentzianCoframeJet.coframe
    inputActual_coframeFirstJet_origin

private theorem inputCartanActual_coframe_contDiffAt_origin :
    ContDiffAt ℝ ∞ InputCartanActual.coframe 0 := by
  simpa [InputCartanActual] using inputActual_coframe_contDiff.contDiffAt

private theorem inputCartanActual_volume_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (fun point =>
        ((generatedVolumeDensity
          (toContinuumPointField InputCartanActual point) : ℝ) : ℂ))
      0 := by
  have volumeReal : ContDiffAt ℝ ∞
      (fun point =>
        generatedVolumeDensity
          (toContinuumPointField InputCartanActual point))
      0 := by
    change ContDiffAt ℝ ∞
      (fun point => abs (Matrix.det (InputCartanActual.coframe point))) 0
    have outer : ContDiffAt ℝ ∞
        (fun coframe : LorentzianCoframe => abs (Matrix.det coframe))
        (InputCartanActual.coframe 0) := by
      rw [inputCartanActual_coframe_origin]
      exact
        StageNineCoframeVariation.coframe_volume_contDiffAt
          (1 : LorentzianCoframe) (by simp)
    have composed : ContDiffAt ℝ ∞
        ((fun coframe : LorentzianCoframe => abs (Matrix.det coframe)) ∘
          InputCartanActual.coframe)
        0 :=
      outer.comp 0 inputCartanActual_coframe_contDiffAt_origin
    change ContDiffAt ℝ ∞
      ((fun coframe : LorentzianCoframe => abs (Matrix.det coframe)) ∘
        InputCartanActual.coframe)
      0
    exact composed
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 volumeReal

private theorem inputCartanActual_inverseVolume_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (fun point =>
        (((generatedVolumeDensity
          (toContinuumPointField InputCartanActual point) : ℝ) : ℂ)⁻¹))
      0 := by
  exact inputCartanActual_volume_contDiffAt_origin.inv (by
    rw [show generatedVolumeDensity
        (toContinuumPointField InputCartanActual 0) =
      abs (Matrix.det (InputCartanActual.coframe 0)) by rfl,
      inputCartanActual_coframe_origin]
    norm_num)

private theorem inputCartanActual_conjugateCoordinates_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (holonomicConjugateMatterCoordinates InputCartanActual) 0 := by
  rw [show holonomicConjugateMatterCoordinates InputCartanActual =
      holonomicConjugateMatterCoordinates InputActual by
    funext point
    unfold holonomicConjugateMatterCoordinates InputCartanActual
    rw [
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
  exact
    (holonomicConjugateMatterCoordinates_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth).contDiffAt

private theorem
    inputCartanActual_conjugateDerivativeCoordinates_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        holonomicConjugateMatterDerivativeCoordinates
          InputCartanActual point direction)
      0 := by
  rw [show
    (fun point =>
      holonomicConjugateMatterDerivativeCoordinates
        InputCartanActual point direction) =
    fun point =>
      holonomicConjugateMatterDerivativeCoordinates
        InputActual point direction by
    funext point
    unfold holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates InputCartanActual
    rw [
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]]
  exact
    (holonomicConjugateMatterDerivativeCoordinates_contDiff InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth direction).contDiffAt

private theorem matterCoordinateDualPairing_contDiffAt_origin
    {coordinates : BasePoint → MatterCoordinateCarrier}
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (coordinatesSmooth : ContDiffAt ℝ 1 coordinates 0)
    (vectorSmooth : ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 1
      (fun point => matterDualOfCoordinates (coordinates point)
        (vector point))
      0 := by
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
      0 vectorSmooth).mul
    ((projection.restrictScalars ℝ).contDiff.contDiffAt.comp
      0 coordinatesSmooth)

private theorem inputCartanActual_conjugateApply_contDiffAt_origin
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorSmooth : ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 1
      (fun point => InputCartanActual.conjugateMatter point (vector point))
      0 := by
  rw [show
    (fun point => InputCartanActual.conjugateMatter point (vector point)) =
    fun point =>
      matterDualOfCoordinates
        (holonomicConjugateMatterCoordinates InputCartanActual point)
        (vector point) by
    funext point
    exact congrArg
      (fun dual : Module.Dual ℂ DiracExteriorMatterCarrier =>
        dual (vector point))
      (matterDualOfCoordinates_surjective
        (InputCartanActual.conjugateMatter point)).symm]
  exact matterCoordinateDualPairing_contDiffAt_origin
    (inputCartanActual_conjugateCoordinates_contDiffAt_origin.of_le
      (by decide))
    vectorSmooth

private theorem inputCartanActual_livePrincipal_coordinate_contDiffAt_origin
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorSmooth : ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal
            (InputCartanActual.coframe point) direction)
            (vector point)))
      0 := by
  have gammaSmooth : ContDiffAt ℝ ∞
      (fun point =>
        inverseCoframeDiracGamma
          { coframe := InputCartanActual.coframe point, derivative := 0 }
          direction)
      0 := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        (1 : LorentzianCoframe) (by simp) direction
    rw [← inputCartanActual_coframe_origin] at outer
    exact outer.comp 0 inputCartanActual_coframe_contDiffAt_origin
  have gammaActionSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := InputCartanActual.coframe point, derivative := 0 }
              direction)
            (vector point)))
      0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 (gammaSmooth.of_le (by decide))).clm_apply
          vectorSmooth
    change ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := InputCartanActual.coframe point, derivative := 0 }
              direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector point)))))
      0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold liveCoframeMatterPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    (contDiffAt_const :
      ContDiffAt ℝ 1 (fun _ : BasePoint => (Complex.I : ℂ)) 0).smul
        gammaActionSmooth

private theorem
    inputCartanActual_temporalPrincipalScalar_contDiffAt_origin :
    ContDiffAt ℝ ∞
      (fun point =>
        coframeTemporalPrincipalScalar (InputCartanActual.coframe point))
      0 := by
  have inverseSmooth : ContDiffAt ℝ ∞
      (fun point => (InputCartanActual.coframe point)⁻¹)
      0 := by
    have outer :=
      StageNineCoframeVariation.coframe_inv_contDiffAt
        (1 : LorentzianCoframe) (by simp)
    rw [← inputCartanActual_coframe_origin] at outer
    exact outer.comp 0 inputCartanActual_coframe_contDiffAt_origin
  unfold coframeTemporalPrincipalScalar
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro internal _
  have inverseEntrySmooth : ContDiffAt ℝ ∞
      (fun point =>
        (InputCartanActual.coframe point)⁻¹
          (0 : LorentzianIndex) internal)
      0 :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseSmooth (0 : LorentzianIndex)) internal
  exact contDiffAt_const.mul (inverseEntrySmooth.pow 2)

private theorem
    inputCartanActual_temporalPrincipalInverse_basis_coordinate_contDiffAt_origin
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (currentCoframeMatterTemporalPrincipalInverse
            (InputCartanActual.coframe point)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      0 := by
  have qComplexSmooth : ContDiffAt ℝ ∞
      (fun point =>
        ((coframeTemporalPrincipalScalar
          (InputCartanActual.coframe point) : ℝ) : ℂ))
      0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp
      0 inputCartanActual_temporalPrincipalScalar_contDiffAt_origin
  have qComplexOrigin :
      ((coframeTemporalPrincipalScalar
        (InputCartanActual.coframe 0) : ℝ) : ℂ) ≠ 0 := by
    rw [inputCartanActual_coframe_origin,
      coframeTemporalPrincipalScalar_one]
    norm_num
  have qInverseSmooth : ContDiffAt ℝ ∞
      (fun point =>
        (((coframeTemporalPrincipalScalar
          (InputCartanActual.coframe point) : ℝ) : ℂ)⁻¹))
      0 :=
    qComplexSmooth.inv qComplexOrigin
  have gammaTimeSmooth : ContDiffAt ℝ ∞
      (fun point =>
        inverseCoframeDiracGamma
          { coframe := InputCartanActual.coframe point, derivative := 0 }
          (0 : LorentzianIndex))
      0 := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        (1 : LorentzianCoframe) (by simp) (0 : LorentzianIndex)
    rw [← inputCartanActual_coframe_origin] at outer
    exact outer.comp 0 inputCartanActual_coframe_contDiffAt_origin
  have basisSmooth : ContDiffAt ℝ 1
      (fun _ : BasePoint =>
        matterCoordinateEquiv
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      0 :=
    contDiffAt_const
  have gammaActionSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := InputCartanActual.coframe point, derivative := 0 }
              (0 : LorentzianIndex))
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0
          (gammaTimeSmooth.of_le (by decide))).clm_apply basisSmooth
    change ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := InputCartanActual.coframe point, derivative := 0 }
              (0 : LorentzianIndex))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))))))
      0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold currentCoframeMatterTemporalPrincipalInverse
    currentCoframeMatterTemporalPrincipal
  simp only [LinearMap.smul_apply, map_smul]
  exact
    ((qInverseSmooth.of_le (by decide)).smul
      ((contDiffAt_const :
        ContDiffAt ℝ 1 (fun _ : BasePoint => (Complex.I : ℂ)) 0).smul
          gammaActionSmooth))

private theorem inputCartanActual_spinLift_contDiffAt_origin
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        diracSpinConnectionLift
          (InputCartanActual.gravityConnection point) direction)
      0 := by
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro column
  unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro pair _
  have realCoefficientSmooth : ContDiffAt ℝ ∞
      (fun point =>
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          InputCartanActual.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair))
      0 :=
    contDiffAt_const.mul
      (inputCartanActual_connection_component_contDiffAt_origin direction
        (lorentzBivectorFirst pair) (lorentzBivectorSecond pair))
  have complexCoefficientSmooth : ContDiffAt ℝ ∞
      (fun point =>
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          InputCartanActual.gravityConnection point direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ))
      0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 realCoefficientSmooth
  exact (contDiffAt_const.mul complexCoefficientSmooth).mul contDiffAt_const

private theorem
    inputCartanActual_connectionOperator_coordinate_contDiffAt_origin
    (direction : LorentzianIndex)
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorSmooth : ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          ((holonomicIdentityCoframeMatterConnectionOperator
            InputCartanActual point direction) (vector point)))
      0 := by
  have spinActionSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (InputCartanActual.gravityConnection point) direction)
            (vector point)))
      0 := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0
          ((inputCartanActual_spinLift_contDiffAt_origin direction).of_le
            (by decide))).clm_apply vectorSmooth
    change ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (InputCartanActual.gravityConnection point) direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector point)))))
      0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have gaugeSmooth : ContDiffAt ℝ 1
      (fun point =>
        p286CoordinateEquiv
          (InputCartanActual.gaugeConnection point direction))
      0 := by
    simpa [InputCartanActual] using
      (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
        direction).contDiffAt.of_le (by decide)
  have gaugeActionSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (InputCartanActual.gaugeConnection point direction))
            (vector point)))
      0 := by
    have actual :=
      (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0 gaugeSmooth).clm_apply vectorSmooth
    change ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm
                (p286CoordinateEquiv
                  (InputCartanActual.gaugeConnection point direction))))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector point)))))
      0 at actual
    simpa only [p286CoordinateEquiv.symm_apply_apply,
      matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicIdentityCoframeMatterConnectionOperator
  simp only [LinearMap.add_apply, map_add]
  exact spinActionSmooth.add gaugeActionSmooth

private theorem inputCartanActual_scalar_contDiffAt_origin :
    ContDiffAt ℝ 1 (fun point => InputCartanActual.scalar point) 0 := by
  simpa [InputCartanActual] using
    fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1.contDiffAt.of_le
      (by decide)

private theorem
    inputCartanActual_algebraicOperator_coordinate_contDiffAt_origin
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorSmooth : ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            InputCartanActual point) (vector point)))
      0 := by
  have directionSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 1
        (fun point =>
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal
                (InputCartanActual.coframe point) direction)
              ((holonomicIdentityCoframeMatterConnectionOperator
                InputCartanActual point direction) (vector point))))
        0 := by
    intro direction
    exact
      inputCartanActual_livePrincipal_coordinate_contDiffAt_origin direction
        (inputCartanActual_connectionOperator_coordinate_contDiffAt_origin
          direction vectorSmooth)
  have sumSmooth : ContDiffAt ℝ 1
      (fun point =>
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            ((liveCoframeMatterPrincipal
                (InputCartanActual.coframe point) direction)
              ((holonomicIdentityCoframeMatterConnectionOperator
                InputCartanActual point direction) (vector point))))
      0 :=
    ContDiffAt.sum fun direction _ => directionSmooth direction
  have yukawaSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (InputCartanActual.scalar point))
            (vector point)))
      0 := by
    have actual :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp 0
          inputCartanActual_scalar_contDiffAt_origin).clm_apply vectorSmooth
    change ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm
              (InputCartanActual.scalar point))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (vector point)))))
      0 at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold holonomicDiracDualLiveCoframeMatterAlgebraicOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_add, map_sum]
  exact sumSmooth.add yukawaSmooth

private theorem
    inputCartanActual_spatialTransportCoordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
        InputCartanActual)
      0 := by
  apply contDiffAt_piLp'
  intro index
  change ContDiffAt ℝ 1
    (fun point =>
      ∑ direction : Fin 3,
        ((generatedVolumeDensity
            (toContinuumPointField InputCartanActual point) : ℝ) : ℂ) *
          matterDualOfCoordinates
              (holonomicConjugateMatterDerivativeCoordinates
                InputCartanActual point direction.succ)
              ((liveCoframeMatterPrincipal
                  (InputCartanActual.coframe point) direction.succ)
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))))
    0
  apply ContDiffAt.sum
  intro direction _
  have vectorSmooth :=
    inputCartanActual_livePrincipal_coordinate_contDiffAt_origin
      direction.succ
      (vector := fun _ =>
        matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))
      contDiffAt_const
  have derivativePairingSmooth :=
    matterCoordinateDualPairing_contDiffAt_origin
      ((inputCartanActual_conjugateDerivativeCoordinates_contDiffAt_origin
        direction.succ).of_le (by decide))
      vectorSmooth
  exact
    (inputCartanActual_volume_contDiffAt_origin.of_le
      (by decide)).mul derivativePairingSmooth

private theorem
    inputCartanActual_spatialPrincipalDrift_contDiffAt_origin :
    ContDiffAt ℝ 1
      (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
        InputCartanActual)
      0 := by
  unfold holonomicLiveCoframeSpatialPrincipalDriftCoordinates
  exact ContDiffAt.sum fun direction _ =>
    inputCartanActual_liveCoframeDensitizedPrincipalDrift_contDiffAt_origin
      direction.succ

private theorem
    inputCartanActual_temporalPrincipalDrift_contDiffAt_origin :
    ContDiffAt ℝ 1
      (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
        InputCartanActual)
      0 := by
  exact
    inputCartanActual_liveCoframeDensitizedPrincipalDrift_contDiffAt_origin
      canonicalLorentzianTimeDirection

private theorem
    inputCartanActual_knownDensitizedDual_apply_contDiffAt_origin
    {vector : BasePoint → DiracExteriorMatterCarrier}
    (vectorSmooth : ContDiffAt ℝ 1
      (fun point => matterCoordinateEquiv (vector point)) 0) :
    ContDiffAt ℝ 1
      (fun point =>
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          InputCartanActual point (vector point))
      0 := by
  have algebraicVectorSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterCoordinateEquiv
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            InputCartanActual point) (vector point)))
      0 :=
    inputCartanActual_algebraicOperator_coordinate_contDiffAt_origin
      vectorSmooth
  have algebraicPairingSmooth : ContDiffAt ℝ 1
      (fun point =>
        InputCartanActual.conjugateMatter point
          ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
            InputCartanActual point) (vector point)))
      0 :=
    inputCartanActual_conjugateApply_contDiffAt_origin
      algebraicVectorSmooth
  have algebraicDualSmooth : ContDiffAt ℝ 1
      (fun point =>
        holonomicDiracDualLiveCoframeAlgebraicDual
          InputCartanActual point (vector point))
      0 := by
    rw [show
      (fun point =>
        holonomicDiracDualLiveCoframeAlgebraicDual
          InputCartanActual point (vector point)) =
      (fun point =>
        ((generatedVolumeDensity
          (toContinuumPointField InputCartanActual point) : ℝ) : ℂ) *
          InputCartanActual.conjugateMatter point
            ((holonomicDiracDualLiveCoframeMatterAlgebraicOperator
              InputCartanActual point) (vector point)))
      by
        funext point
        exact liveCoframeAlgebraicDual_apply
          InputCartanActual point (vector point)]
    exact
      (inputCartanActual_volume_contDiffAt_origin.of_le
        (by decide)).mul algebraicPairingSmooth
  have spatialTransportSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              InputCartanActual point)
            (vector point))
      0 :=
    matterCoordinateDualPairing_contDiffAt_origin
      inputCartanActual_spatialTransportCoordinates_contDiffAt_origin
      vectorSmooth
  have spatialDriftSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              InputCartanActual point)
            (vector point))
      0 :=
    matterCoordinateDualPairing_contDiffAt_origin
      inputCartanActual_spatialPrincipalDrift_contDiffAt_origin
      vectorSmooth
  have temporalDriftSmooth : ContDiffAt ℝ 1
      (fun point =>
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              InputCartanActual point)
            (vector point))
      0 :=
    matterCoordinateDualPairing_contDiffAt_origin
      inputCartanActual_temporalPrincipalDrift_contDiffAt_origin
      vectorSmooth
  rw [show
    (fun point =>
      holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
        InputCartanActual point (vector point)) =
    (fun point =>
      holonomicDiracDualLiveCoframeAlgebraicDual
          InputCartanActual point (vector point) -
        matterDualOfCoordinates
            (holonomicLiveCoframeConjugateMatterSpatialTransportCoordinates
              InputCartanActual point)
            (vector point) -
        matterDualOfCoordinates
            (holonomicLiveCoframeSpatialPrincipalDriftCoordinates
              InputCartanActual point)
            (vector point) -
        matterDualOfCoordinates
            (holonomicLiveCoframeTemporalPrincipalDriftCoordinates
              InputCartanActual point)
            (vector point))
    by
      funext point
      exact liveCoframeKnownDensitizedDual_apply
        InputCartanActual point (vector point)]
  exact
    ((algebraicDualSmooth.sub spatialTransportSmooth).sub
      spatialDriftSmooth).sub temporalDriftSmooth

private theorem
    inputCartanActual_liveAdjointActionVelocity_basis_contDiffAt_origin
    (index : MatterCoordinateIndex) :
    ContDiffAt ℝ 1
      (fun point =>
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            InputCartanActual point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
      0 := by
  have knownSmooth : ContDiffAt ℝ 1
      (fun point =>
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          InputCartanActual point
          (currentCoframeMatterTemporalPrincipalInverse
            (InputCartanActual.coframe point)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
      0 :=
    inputCartanActual_knownDensitizedDual_apply_contDiffAt_origin
      (inputCartanActual_temporalPrincipalInverse_basis_coordinate_contDiffAt_origin
        index)
  rw [show
    (fun point =>
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          InputCartanActual point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) =
    (fun point =>
      (((generatedVolumeDensity
        (toContinuumPointField InputCartanActual point) : ℝ) : ℂ)⁻¹) *
        holonomicDiracDualLiveCoframeConjugateMatterKnownDensitizedDual
          InputCartanActual point
          (currentCoframeMatterTemporalPrincipalInverse
            (InputCartanActual.coframe point)
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))))
    by
      funext point
      exact liveCoframeActionVelocity_apply
        InputCartanActual point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))]
  exact
    (inputCartanActual_inverseVolume_contDiffAt_origin.of_le
      (by decide)).mul knownSmooth

private theorem
    inputCartanActual_liveAdjointActionVelocity_coordinates_contDiffAt_origin :
    ContDiffAt ℝ 1
      (fun point =>
        matterDualCoordinates
          (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            InputCartanActual point))
      0 := by
  exact matterDualCoordinates_contDiffAt_of_basis
    (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
      InputCartanActual)
    0 inputCartanActual_liveAdjointActionVelocity_basis_contDiffAt_origin

private theorem recenteredInput_coframeFirstJet_origin
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (fullyRecenterHolonomicConfiguration InputActual contact).coframe 0 =
      holonomicCoframeFirstJetAt InputActual.coframe contact := by
  apply coframeJet_eq_of_fields_eq
  · change
      (fullyRecenterHolonomicConfiguration InputActual contact).coframe 0 =
        InputActual.coframe contact
    exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fieldDirectionalDerivative
          ((fun point => InputActual.coframe point internal coordinate) ∘
            canonicalSpacetimeContactTranslation contact)
          0 derivativeDirection =
        fieldDirectionalDerivative
          (fun point => InputActual.coframe point internal coordinate)
          contact derivativeDirection
    simpa [canonicalSpacetimeContactTranslation] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (fun point => InputActual.coframe point internal coordinate)
        contact 0 derivativeDirection

private theorem recenteredInput_spinResponse_origin
    (contact : BasePoint) :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration InputActual contact) 0 =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        InputActual contact := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · exact fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · exact fullyRecenterHolonomicConfiguration_matter_origin _ _
  · exact fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _

private theorem recenteredInput_actionCartanConnection_origin
    (contact : BasePoint) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration InputActual contact) 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual contact := by
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recenteredInput_coframeFirstJet_origin,
    fullyRecenterHolonomicConfiguration_coframe_origin,
    recenteredInput_spinResponse_origin]

private theorem restart_coframeFirstJet_origin
    (contact : BasePoint) :
    holonomicCoframeFirstJetAt
        (completeJointGeneratedProfileRestartCurrent
          positiveSmoothUnifiedSource InputActual contact).coframe 0 =
      holonomicCoframeFirstJetAt InputCartanActual.coframe contact := by
  unfold completeJointGeneratedProfileRestartCurrent InputCartanActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  exact recenteredInput_coframeFirstJet_origin contact

private theorem restart_connection_origin
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        positiveSmoothUnifiedSource InputActual contact).gravityConnection 0 =
      InputCartanActual.gravityConnection contact := by
  change
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fullyRecenterHolonomicConfiguration InputActual contact) 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual contact
  exact recenteredInput_actionCartanConnection_origin contact

private theorem restart_gaugeConnection_origin
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        positiveSmoothUnifiedSource InputActual contact).gaugeConnection 0 =
      InputCartanActual.gaugeConnection contact := by
  unfold completeJointGeneratedProfileRestartCurrent InputCartanActual
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  exact fullyRecenterHolonomicConfiguration_gaugeConnection_origin _ _

private theorem restart_scalar_origin
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        positiveSmoothUnifiedSource InputActual contact).scalar 0 =
      InputCartanActual.scalar contact := by
  unfold completeJointGeneratedProfileRestartCurrent InputCartanActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]
  exact fullyRecenterHolonomicConfiguration_scalar_origin _ _

private theorem restart_conjugateMatter_origin
    (contact : BasePoint) :
    (completeJointGeneratedProfileRestartCurrent
        positiveSmoothUnifiedSource InputActual contact).conjugateMatter 0 =
      InputCartanActual.conjugateMatter contact := by
  unfold completeJointGeneratedProfileRestartCurrent InputCartanActual
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  exact fullyRecenterHolonomicConfiguration_conjugateMatter_origin _ _

private theorem restart_conjugateMatterDerivative_origin
    (contact : BasePoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (completeJointGeneratedProfileRestartCurrent
          positiveSmoothUnifiedSource InputActual contact)
        0 direction =
      holonomicConjugateMatterDerivativeDual
        InputCartanActual contact direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
    completeJointGeneratedProfileRestartCurrent InputCartanActual
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  change
    matterDualOfCoordinates
        (fieldDirectionalDerivative
          ((fun point =>
            matterDualCoordinates (InputActual.conjugateMatter point)) ∘
              canonicalSpacetimeContactTranslation contact)
          0 direction) =
      matterDualOfCoordinates
        (fieldDirectionalDerivative
          (fun point =>
            matterDualCoordinates (InputActual.conjugateMatter point))
          contact direction)
  rw [fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation]
  simp [canonicalSpacetimeContactTranslation]

private theorem liveAdjointActionVelocity_primalWrite_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        configuration 0 := by
  apply liveCoframeActionVelocity_eq_of_pointData
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro direction
    rfl

private theorem restart_liveAdjointActionVelocity_origin
    (contact : BasePoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (completeJointGeneratedProfileRestartCurrent
          positiveSmoothUnifiedSource InputActual contact)
        0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        InputCartanActual contact := by
  apply liveCoframeActionVelocity_eq_of_pointData
  · exact restart_coframeFirstJet_origin contact
  · exact restart_connection_origin contact
  · exact restart_gaugeConnection_origin contact
  · exact restart_scalar_origin contact
  · exact restart_conjugateMatter_origin contact
  · exact restart_conjugateMatterDerivative_origin contact

private theorem profile_adjointVelocity_normalForm
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      positiveSmoothUnifiedSource InputActual contact).adjointVelocity =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        InputCartanActual contact := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    liveAdjointActionVelocity_primalWrite_origin,
    restart_liveAdjointActionVelocity_origin]

private theorem correction_normalForm
    (contact : BasePoint) :
    completeJointAdjointTemporalCoordinateCorrection
        positiveSmoothUnifiedSource InputActual contact =
      matterDualCoordinates
          (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
            InputCartanActual contact) -
        fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates InputActual)
          contact canonicalLorentzianTimeDirection := by
  unfold completeJointAdjointTemporalCoordinateCorrection
  rw [profile_adjointVelocity_normalForm]

theorem
    fixedP506L0FullOccurrenceAdjointTemporalCoordinateCorrection_contDiffAt_origin :
    ContDiffAt ℝ 1
      (completeJointAdjointTemporalCoordinateCorrection
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor)
      0 := by
  rw [show
    completeJointAdjointTemporalCoordinateCorrection
        positiveSmoothUnifiedSource InputActual =
      fun contact =>
        matterDualCoordinates
            (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
              InputCartanActual contact) -
          fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates InputActual)
            contact canonicalLorentzianTimeDirection by
    funext contact
    exact correction_normalForm contact]
  exact
    inputCartanActual_liveAdjointActionVelocity_coordinates_contDiffAt_origin.sub
      ((holonomicConjugateMatterDerivativeCoordinates_contDiff InputActual
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        canonicalLorentzianTimeDirection).contDiffAt.of_le (by decide))

theorem fixedP506L0FullOccurrenceAdjointTemporalPrimitive_hasFDerivAt_origin :
    HasFDerivAt
      (canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor))
      (_root_.SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual.canonicalTimeProjection.smulRight
        (completeJointAdjointTemporalCoordinateCorrection
          positiveSmoothUnifiedSource
          FixedP506FormNativeJointActionSolvedSuccessor 0))
      0 :=
  canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt
    (completeJointAdjointTemporalCoordinateCorrection
      positiveSmoothUnifiedSource InputActual)
    fixedP506L0FullOccurrenceAdjointTemporalCoordinateCorrection_contDiffAt_origin

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
