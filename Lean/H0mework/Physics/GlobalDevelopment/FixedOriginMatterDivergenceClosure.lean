import H0mework.Physics.GlobalDevelopment.FixedOriginAdjointDerivativeTransport

/-!
# Fixed P506/L0 global matter-divergence origin closure

This module consumes the generated adjoint first-germ comparison to identify
the complete matter momentum divergence at the fixed P506/L0 occurrence.
Together with the same-occurrence algebraic action data, it closes the matter
Euler reader on the source/current-only global actual.

The comparison is derivative-level action transport.  No residual value or
zero-fiber certificate is used to choose a field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeLocalDifferentiability
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginAdjointDerivativeTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- The kinetic matter momentum exposed on exactly the two primitive inputs
that can affect its first germ: the coframe and faithful adjoint coordinates.
This is an action-data carrier, not a residual or a write. -/
def matterMomentumCoframeAdjoint
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (joint : LorentzianCoframe × MatterCoordinateCarrier) : ℝ :=
  abs (Matrix.det joint.1) *
    ((matterDualOfCoordinates joint.2)
      ((liveCoframeMatterPrincipal joint.1 derivativeDirection)
        (matterCoordinateEquiv.symm direction))).re

theorem matterMomentumCoframeAdjoint_contDiffAt_one
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (coordinates : MatterCoordinateCarrier) :
    ContDiffAt ℝ ∞
      (matterMomentumCoframeAdjoint direction derivativeDirection)
      ((1 : LorentzianCoframe), coordinates) := by
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        abs (Matrix.det joint.1))
      ((1 : LorentzianCoframe), coordinates) :=
    (StageNineCoframeVariation.coframe_volume_contDiffAt
      (1 : LorentzianCoframe) (by simp)).comp
        ((1 : LorentzianCoframe), coordinates) contDiffAt_fst
  have gammaSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        inverseCoframeDiracGamma
          { coframe := joint.1, derivative := 0 } derivativeDirection)
      ((1 : LorentzianCoframe), coordinates) := by
    let gamma := fun candidate : LorentzianCoframe =>
      inverseCoframeDiracGamma
        { coframe := candidate, derivative := 0 } derivativeDirection
    have outer : ContDiffAt ℝ ∞ gamma (1 : LorentzianCoframe) :=
      inverseCoframeDiracGamma_contDiffAt
        (1 : LorentzianCoframe) (by simp) derivativeDirection
    change ContDiffAt ℝ ∞
      (gamma ∘
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          joint.1))
      ((1 : LorentzianCoframe), coordinates)
    exact outer.comp ((1 : LorentzianCoframe), coordinates) contDiffAt_fst
  have directionSmooth : ContDiffAt ℝ ∞
      (fun _ : LorentzianCoframe × MatterCoordinateCarrier =>
        matterCoordinateEquiv (matterCoordinateEquiv.symm direction))
      ((1 : LorentzianCoframe), coordinates) :=
    contDiffAt_const
  have gammaActionSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := joint.1, derivative := 0 } derivativeDirection)
            (matterCoordinateEquiv.symm direction)))
      ((1 : LorentzianCoframe), coordinates) := by
    have actual :=
      (StageNineCoframeScalarMatterRegularity.diracMatrixMatterCoordinateRealBilinear
        |>.toContinuousBilinearMap.contDiff.contDiffAt.comp
          ((1 : LorentzianCoframe), coordinates) gammaSmooth).clm_apply
        directionSmooth
    change ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := joint.1, derivative := 0 } derivativeDirection)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (matterCoordinateEquiv.symm direction)))))
      ((1 : LorentzianCoframe), coordinates) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have principalCarrierSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        matterCoordinateEquiv
          ((liveCoframeMatterPrincipal joint.1 derivativeDirection)
            (matterCoordinateEquiv.symm direction)))
      ((1 : LorentzianCoframe), coordinates) := by
    unfold liveCoframeMatterPrincipal
    simp only [LinearMap.smul_apply, map_smul]
    exact
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : LorentzianCoframe × MatterCoordinateCarrier =>
            (Complex.I : ℂ))
          ((1 : LorentzianCoframe), coordinates)).smul gammaActionSmooth
  have pairingSmooth : ContDiffAt ℝ ∞
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        (matterDualOfCoordinates joint.2)
          ((liveCoframeMatterPrincipal joint.1 derivativeDirection)
            (matterCoordinateEquiv.symm direction)))
      ((1 : LorentzianCoframe), coordinates) := by
    rw [show
      (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
        (matterDualOfCoordinates joint.2)
          ((liveCoframeMatterPrincipal joint.1 derivativeDirection)
            (matterCoordinateEquiv.symm direction))) =
      fun joint =>
        ∑ coordinate : MatterCoordinateIndex,
          matterCoordinateEquiv
              ((liveCoframeMatterPrincipal joint.1 derivativeDirection)
                (matterCoordinateEquiv.symm direction))
              coordinate *
            joint.2 coordinate by
      funext joint
      exact matterDualOfCoordinates_apply _ _]
    apply ContDiffAt.sum
    intro coordinate _
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj coordinate).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
    have principalCoordinateSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          matterCoordinateEquiv
              ((liveCoframeMatterPrincipal joint.1 derivativeDirection)
                (matterCoordinateEquiv.symm direction))
              coordinate)
        ((1 : LorentzianCoframe), coordinates) :=
      (projection.restrictScalars ℝ).contDiff.contDiffAt.comp
        ((1 : LorentzianCoframe), coordinates) principalCarrierSmooth
    have dualCoordinateSmooth : ContDiffAt ℝ ∞
        (fun joint : LorentzianCoframe × MatterCoordinateCarrier =>
          joint.2 coordinate)
        ((1 : LorentzianCoframe), coordinates) := by
      fun_prop
    exact principalCoordinateSmooth.mul dualCoordinateSmooth
  unfold matterMomentumCoframeAdjoint
  exact
    volumeSmooth.mul
      (Complex.reCLM.contDiff.contDiffAt.comp
        ((1 : LorentzianCoframe), coordinates) pairingSmooth)

theorem matterDifferentialMomentum_eq_coframeAdjoint
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource configuration
        direction derivativeDirection =
      matterMomentumCoframeAdjoint direction derivativeDirection ∘
        fun point =>
          (configuration.coframe point,
            holonomicConjugateMatterCoordinates configuration point) := by
  funext point
  unfold matterDifferentialMomentum matterMomentumCoframeAdjoint
    matterDifferentialVariationVector liveCoframeMatterPrincipal
    generatedVolumeDensity holonomicConjugateMatterCoordinates
  simp only [Function.comp_apply, toContinuumPointField]
  rw [matterDualOfCoordinates_surjective]
  simp only [LinearMap.smul_apply]

theorem newActual_matterMomentumDerivative_origin_eq_accepted
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource NewActual
          direction derivativeDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource AcceptedActual
          direction derivativeDirection)
        0 derivativeDirection := by
  let outer :=
    matterMomentumCoframeAdjoint direction derivativeDirection
  let newInner := fun point : BasePoint =>
    (NewActual.coframe point,
      holonomicConjugateMatterCoordinates NewActual point)
  let acceptedInner := fun point : BasePoint =>
    (AcceptedActual.coframe point,
      holonomicConjugateMatterCoordinates AcceptedActual point)
  have newCoframeDifferentiable : DifferentiableAt ℝ NewActual.coframe 0 := by
    have smooth : ContDiff ℝ ∞ NewActual.coframe := by
      apply contDiff_pi'
      intro internal
      apply contDiff_pi'
      intro coordinate
      exact
        fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_contDiff
          internal coordinate
    exact (smooth.differentiable (by simp)).differentiableAt
  have acceptedCoframeDifferentiable :
      DifferentiableAt ℝ AcceptedActual.coframe 0 :=
    ((fixedP506L0FinalCommonActionActual_coframe_contDiff 0).differentiable
      (by simp)).differentiableAt
  have acceptedConjugateDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates AcceptedActual) 0 :=
    by
      rw [show
        holonomicConjugateMatterCoordinates AcceptedActual =
          holonomicConjugateMatterCoordinates ProfileAdjointActual by
        unfold holonomicConjugateMatterCoordinates
        rw [acceptedActual_conjugateMatter_eq_profileAdjoint]]
      exact
        profileAdjoint_conjugateMatterCoordinates_differentiableAt_origin
  have newInnerDerivative :
      HasFDerivAt newInner
        ((fderiv ℝ NewActual.coframe 0).prod
          (fderiv ℝ (holonomicConjugateMatterCoordinates NewActual) 0))
        0 :=
    HasFDerivAt.prodMk newCoframeDifferentiable.hasFDerivAt
      newActual_conjugateMatterCoordinates_differentiableAt_origin.hasFDerivAt
  have acceptedInnerDerivative :
      HasFDerivAt acceptedInner
        ((fderiv ℝ AcceptedActual.coframe 0).prod
          (fderiv ℝ
            (holonomicConjugateMatterCoordinates AcceptedActual) 0))
        0 :=
    HasFDerivAt.prodMk acceptedCoframeDifferentiable.hasFDerivAt
      acceptedConjugateDifferentiable.hasFDerivAt
  have newInnerOrigin :
      newInner 0 =
        ((1 : LorentzianCoframe),
          holonomicConjugateMatterCoordinates AcceptedActual 0) := by
    unfold newInner
    apply Prod.ext
    · rw [newActual_coframe_origin_eq_accepted,
        fixedP506L0FinalCommonActionActual_coframe_origin]
    · unfold holonomicConjugateMatterCoordinates
      rw [newActual_conjugateMatter_origin_eq_accepted]
  have acceptedInnerOrigin :
      acceptedInner 0 =
        ((1 : LorentzianCoframe),
          holonomicConjugateMatterCoordinates AcceptedActual 0) := by
    unfold acceptedInner
    rw [fixedP506L0FinalCommonActionActual_coframe_origin]
  have innerDirectionalDerivative :
      ((fderiv ℝ newInner 0)
          (coordinateDirection derivativeDirection)) =
        (fderiv ℝ acceptedInner 0)
          (coordinateDirection derivativeDirection) := by
    rw [newInnerDerivative.fderiv, acceptedInnerDerivative.fderiv]
    apply Prod.ext
    · change
        (fderiv ℝ NewActual.coframe 0)
            (coordinateDirection derivativeDirection) =
          (fderiv ℝ AcceptedActual.coframe 0)
            (coordinateDirection derivativeDirection)
      rw [newActual_coframe_eq_accepted]
    · change
        fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates NewActual) 0
              derivativeDirection =
          fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates AcceptedActual) 0
              derivativeDirection
      exact
        newActual_conjugateMatterCoordinateDerivative_origin_eq_accepted
          derivativeDirection
  have outerDifferentiable : DifferentiableAt ℝ outer
      ((1 : LorentzianCoframe),
        holonomicConjugateMatterCoordinates AcceptedActual 0) :=
    (matterMomentumCoframeAdjoint_contDiffAt_one direction
      derivativeDirection
      (holonomicConjugateMatterCoordinates AcceptedActual 0)).differentiableAt
        (by simp)
  have outerAtNew : DifferentiableAt ℝ outer (newInner 0) := by
    rw [newInnerOrigin]
    exact outerDifferentiable
  have outerAtAccepted : DifferentiableAt ℝ outer (acceptedInner 0) := by
    rw [acceptedInnerOrigin]
    exact outerDifferentiable
  unfold fieldDirectionalDerivative
  rw [matterDifferentialMomentum_eq_coframeAdjoint,
    matterDifferentialMomentum_eq_coframeAdjoint]
  change
    (fderiv ℝ (outer ∘ newInner) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ (outer ∘ acceptedInner) 0)
        (coordinateDirection derivativeDirection)
  rw [fderiv_comp 0 outerAtNew newInnerDerivative.differentiableAt,
    fderiv_comp 0 outerAtAccepted acceptedInnerDerivative.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply]
  change
    (fderiv ℝ outer (newInner 0))
        ((fderiv ℝ newInner 0)
          (coordinateDirection derivativeDirection)) =
      (fderiv ℝ outer (acceptedInner 0))
        ((fderiv ℝ acceptedInner 0)
          (coordinateDirection derivativeDirection))
  rw [newInnerOrigin, acceptedInnerOrigin, innerDirectionalDerivative]

theorem newActual_matterDivergence_origin_eq_accepted
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource NewActual
        direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        AcceptedActual direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    newActual_matterMomentumDerivative_origin_eq_accepted direction
      derivativeDirection

theorem newActual_gaugeConnection_origin_eq_accepted :
    NewActual.gaugeConnection 0 =
      AcceptedActual.gaugeConnection 0 := by
  calc
    NewActual.gaugeConnection 0 =
        ProfileRestartActual.gaugeConnection 0 :=
      newActual_gaugeConnection_origin_eq_profileRestart
    _ = InputActual.gaugeConnection 0 :=
      congrFun profileRestartActual_gaugeConnection_eq_input 0
    _ = AcceptedActual.gaugeConnection 0 := by
      rw [fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved]

theorem newActual_scalarCovariantDerivative_origin_eq_accepted :
    holonomicScalarCovariantDerivative NewActual 0 =
      holonomicScalarCovariantDerivative AcceptedActual 0 :=
  newActual_scalarCovariantDerivative_eq_algebraic.trans
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_origin_eq_canonical.trans
      canonicalActual_scalarCovariantDerivative_eq_accepted)

theorem newActual_scalarAlgebraic_origin_eq_accepted
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        NewActual direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        AcceptedActual direction 0 := by
  have variationEquality :
      holonomicScalarVariationAlgebraicDirection NewActual direction 0 =
        holonomicScalarVariationAlgebraicDirection AcceptedActual direction
          0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [newActual_gaugeConnection_origin_eq_accepted]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [newActual_coframe_origin_eq_accepted,
    newActual_scalar_origin_eq_accepted,
    newActual_scalarCovariantDerivative_origin_eq_accepted,
    newActual_matter_origin_eq_accepted,
    newActual_conjugateMatter_origin_eq_accepted, variationEquality]

theorem newActual_chargedGaugeThreeForm_origin_eq_accepted :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField NewActual 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField AcceptedActual 0) := by
  apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
  · exact newActual_coframe_origin_eq_accepted
  · exact newActual_scalar_origin_eq_accepted
  · exact newActual_scalarCovariantDerivative_origin_eq_accepted
  · exact newActual_matter_origin_eq_accepted
  · exact newActual_conjugateMatter_origin_eq_accepted

theorem newCartanInput_coframe_eq_acceptedCartanInput :
    NewCartanInput.coframe = AcceptedCartanInput.coframe := by
  change NewActual.coframe = AcceptedActual.coframe
  exact newActual_coframe_eq_accepted

theorem newCartanInput_matter_origin_eq_acceptedCartanInput :
    NewCartanInput.matter 0 = AcceptedCartanInput.matter 0 := by
  change NewActual.matter 0 = AcceptedActual.matter 0
  exact newActual_matter_origin_eq_accepted

theorem newCartanInput_conjugateMatter_origin_eq_acceptedCartanInput :
    NewCartanInput.conjugateMatter 0 =
      AcceptedCartanInput.conjugateMatter 0 := by
  change NewActual.conjugateMatter 0 = AcceptedActual.conjugateMatter 0
  exact newActual_conjugateMatter_origin_eq_accepted

theorem newCartanInput_actionCartanConnection_origin_eq_accepted :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        NewCartanInput 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        AcceptedCartanInput 0 := by
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource NewCartanInput AcceptedCartanInput 0
      (congrFun newCartanInput_coframe_eq_acceptedCartanInput 0)
      newCartanInput_matter_origin_eq_acceptedCartanInput
      newCartanInput_conjugateMatter_origin_eq_acceptedCartanInput
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [newCartanInput_coframe_eq_acceptedCartanInput, spinEq]

theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection_origin_eq_accepted :
    NewActual.gravityConnection 0 =
      AcceptedActual.gravityConnection 0 := by
  calc
    NewActual.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource NewCartanInput 0 := by
      rfl
    _ = diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource AcceptedCartanInput 0 :=
      newCartanInput_actionCartanConnection_origin_eq_accepted
    _ = AcceptedCartanInput.gravityConnection 0 :=
      (fixedP506L0FinalCommonPreECActionActual_connection_selfGenerated_origin
        (0 : StageNineSpatialPoint)).symm
    _ = AcceptedActual.gravityConnection 0 :=
      (fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC
        (0 : StageNineSpatialPoint)).symm

theorem newActual_matterAlgebraic_origin_eq_accepted
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        NewActual direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        AcceptedActual direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection NewActual direction 0 =
        holonomicMatterVariationAlgebraicDirection AcceptedActual direction
          0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [
      fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection_origin_eq_accepted,
      newActual_gaugeConnection_origin_eq_accepted]
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [newActual_coframe_origin_eq_accepted,
    newActual_scalar_origin_eq_accepted,
    newActual_conjugateMatter_origin_eq_accepted, variationEquality]

theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_matter_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      NewActual 0).matter =
      0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
      positiveSmoothUnifiedSource NewActual direction 0 = 0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [newActual_matterAlgebraic_origin_eq_accepted,
    newActual_matterDivergence_origin_eq_accepted]
  exact
    fixedP506L0FinalCommonActionActual_matterEuler_origin_zero 0 direction

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginMatterDivergenceClosure
