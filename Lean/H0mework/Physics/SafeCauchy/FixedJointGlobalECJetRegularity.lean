import H0mework.Physics.SafeCauchy.FixedJointGlobalOriginResidualClosure
import H0mework.Physics.Source.RadialCurveIntegralSmoothRegularity

/-!
# Fixed Cauchy-safe global EC-jet regularity

The source/current-only temporal, constitutive, and P286 writes generate a
global `C¹` EC connection-jet profile.  This is the analytic authority needed
to inspect the already-emitted radial curvature assembly seam.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalTimePrimitiveSegmentRegularity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestartGlobalRegularity
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureTargetLocalRegularity
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativePointwiseP286RequiredExteriorProfileRegularity
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineLorentzConnectionVariation
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineConnectionSectorSourceBalance
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeGaugeWedge
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineRadialCurveIntegralFirstJet
open StageNineRadialCurveIntegralSmoothRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineGlobalIntegratedAction
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

local instance probeP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance probeP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance probeMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Current : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source
    Prepared

private abbrev GlobalTemporal : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalTemporalCurrent Source Current

private abbrev GlobalConstitutive : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalConstitutiveCurrent Source Current

private abbrev GlobalP286 : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalP286Current Source Current

private def GlobalP286ContactField (contact : BasePoint) :
    StageNineContinuumPointField :=
  diracDualFormNativeCoframeECContactField GlobalP286 contact

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

private theorem matterCorrection_contDiff :
    ContDiff ℝ ∞
      (completeJointMatterTemporalCoordinateCorrection Source Current) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact completeJointMatterTemporalCoordinateCorrection_contDiffAt Source
    Current current_smooth point (current_nondegenerate point)
      (current_noncharacteristic point)

private theorem adjointCorrection_contDiff :
    ContDiff ℝ ∞
      (completeJointAdjointTemporalCoordinateCorrection Source Current) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
    Source Current current_smooth point (current_nondegenerate point)
      (current_noncharacteristic point)

private theorem scalarAcceleration_contDiff :
    ContDiff ℝ ∞
      (completeJointCauchySafeScalarAccelerationProfile Source Current) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact completeJointCauchySafeScalarAccelerationProfile_contDiffAt Source
    Current current_smooth point (current_nondegenerate point)
      (scalarCoordinateTimePrincipalWeight_ne_zero Current point
        (current_nondegenerate point) (current_noncharacteristic point))

private theorem canonicalTimePrimitive_contDiff_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile) :
    ContDiff ℝ ∞ (canonicalTimePrimitive profile) := by
  rw [contDiff_infty]
  intro order
  rw [contDiff_iff_contDiffAt]
  intro point
  apply canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
    order profile Set.univ isOpen_univ
  · exact (regular.of_le
      (show ((((order + 1 : ℕ) : ℕ∞)) : ℕ∞ω) ≤
          ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)).contDiffOn
  · simp

private theorem canonicalTimeSecondPrimitive_contDiff_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile) :
    ContDiff ℝ ∞ (canonicalTimeSecondPrimitive profile) := by
  rw [contDiff_infty]
  intro order
  rw [contDiff_iff_contDiffAt]
  intro point
  apply canonicalTimeSecondPrimitive_contDiffAt_of_contDiffOn_segment_finite
    order profile Set.univ isOpen_univ
  · exact (regular.of_le
      (show ((((order + 2 : ℕ) : ℕ∞)) : ℕ∞ω) ≤
          ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)).contDiffOn
  · simp

private theorem globalTemporal_scalar_contDiff :
    ContDiff ℝ ∞ GlobalTemporal.scalar := by
  change ContDiff ℝ ∞ (Current.scalar +
    canonicalTimeSecondPrimitive
      (completeJointCauchySafeScalarAccelerationProfile Source Current))
  exact current_smooth.2.2.2.2.2.2.1.add
    (canonicalTimeSecondPrimitive_contDiff_of_contDiff _
      scalarAcceleration_contDiff)

private theorem globalTemporal_matterCoordinates_contDiff :
    ContDiff ℝ ∞
      (fun point => matterCoordinateEquiv (GlobalTemporal.matter point)) := by
  rw [show (fun point => matterCoordinateEquiv (GlobalTemporal.matter point)) =
      (fun point => matterCoordinateEquiv (Current.matter point)) +
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Current) by
    funext point
    simp [GlobalTemporal, cauchySafeJointGlobalTemporalCurrent,
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]]
  exact current_smooth.2.2.2.2.2.2.2.1.add
    (canonicalTimePrimitive_contDiff_of_contDiff _ matterCorrection_contDiff)

private theorem globalTemporal_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞ (holonomicConjugateMatterCoordinates GlobalTemporal) := by
  rw [show holonomicConjugateMatterCoordinates GlobalTemporal =
      holonomicConjugateMatterCoordinates Current +
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Current) by
    funext point
    simp [GlobalTemporal, cauchySafeJointGlobalTemporalCurrent,
      sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
      holonomicConjugateMatterCoordinates, matterDualCoordinates_add]]
  exact (holonomicConjugateMatterCoordinates_contDiff Current current_smooth).add
    (canonicalTimePrimitive_contDiff_of_contDiff _ adjointCorrection_contDiff)

private theorem globalTemporal_conjugateMatter_eq :
    GlobalTemporal.conjugateMatter = fun point =>
      Current.conjugateMatter point +
        matterDualOfCoordinates
          (canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection Source Current)
            point) := by
  change
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      Source Current).conjugateMatter = _
  rw [sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator_conjugateMatter,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter]

private theorem globalTemporal_smooth : GlobalTemporal.Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact current_smooth.1
  · exact current_smooth.2.1
  · exact current_smooth.2.2.1
  · exact current_smooth.2.2.2.1
  · exact current_smooth.2.2.2.2.1
  · exact current_smooth.2.2.2.2.2.1
  · exact globalTemporal_scalar_contDiff
  · exact globalTemporal_matterCoordinates_contDiff
  · intro index
    rw [globalTemporal_conjugateMatter_eq]
    let projection : MatterCoordinateCarrier →L[ℝ] ℂ :=
      ((ContinuousLinearMap.proj index).comp
        (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
      ).restrictScalars ℝ
    have primitiveRegular : ContDiff ℝ ∞ (fun point =>
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Current)
          point index) := by
      exact projection.contDiff.comp
        (canonicalTimePrimitive_contDiff_of_contDiff _
          adjointCorrection_contDiff)
    simpa only [Pi.add_apply, LinearMap.add_apply,
      matterDualOfCoordinates_basis_apply] using
      (current_smooth.2.2.2.2.2.2.2.2 index).add primitiveRegular

private theorem globalTemporal_nondegenerate : GlobalTemporal.Nondegenerate := by
  intro point
  change Matrix.det (Current.coframe point) ≠ 0
  exact current_nondegenerate point

private theorem globalConstitutive_auxiliaryCoordinate_eq :
    holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source) (GlobalTemporal.coframe point)
          (holonomicP286GaugeCurvatureCoordinate GlobalTemporal point) := by
  funext point pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [show GlobalConstitutive.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source GlobalTemporal by
    exact diracDualFormNativeConstitutiveWrittenCurrent_gaugeAuxiliary
      Source GlobalTemporal]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  unfold
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
    holonomicP286GaugeCurvatureCoordinate
  rw [show (fun pair => p286CoordinateEquiv
      (holonomicGaugeCurvature GlobalTemporal point pair)) =
      formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature GlobalTemporal point) by rfl,
    formNativeP286GaugeActual_coordinate_actual,
    formNativeP286GaugeActualToCoordinateLinear_apply]

private theorem globalConstitutive_auxiliary_contDiff :
    ∀ pair, ContDiff ℝ ∞ (fun point =>
      p286CoordinateEquiv (GlobalConstitutive.gaugeAuxiliary point pair)) := by
  intro pair
  rw [show (fun point =>
      p286CoordinateEquiv (GlobalConstitutive.gaugeAuxiliary point pair)) =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (GlobalTemporal.coframe point)
          (holonomicP286GaugeCurvatureCoordinate GlobalTemporal point) pair by
    funext point
    exact congrFun (congrFun globalConstitutive_auxiliaryCoordinate_eq point)
      pair]
  rw [contDiff_iff_contDiffAt]
  intro point
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings Source) (GlobalTemporal.coframe point)
      (globalTemporal_nondegenerate point)
      (holonomicP286GaugeCurvatureCoordinate GlobalTemporal point)
  have inner : ContDiffAt ℝ ∞ (fun candidate =>
      (GlobalTemporal.coframe candidate,
        holonomicP286GaugeCurvatureCoordinate GlobalTemporal candidate))
      point := by
    have curvatureRegular : ContDiff ℝ ∞
        (holonomicP286GaugeCurvatureCoordinate GlobalTemporal) := by
      apply contDiff_pi'
      intro curvaturePair
      exact holonomicGaugeCurvature_coordinate_contDiff GlobalTemporal
        globalTemporal_smooth curvaturePair
    exact (holonomicCoframe_contDiff GlobalTemporal globalTemporal_smooth
      ).contDiffAt.prodMk curvatureRegular.contDiffAt
  have composed := outer.comp point inner
  simpa only [Function.comp_apply] using
    contDiffAt_pi.mp composed pair

private theorem globalConstitutive_smooth : GlobalConstitutive.Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalTemporal_smooth.1
  · exact globalTemporal_smooth.2.1
  · exact globalTemporal_smooth.2.2.1
  · exact globalTemporal_smooth.2.2.2.1
  · exact globalTemporal_smooth.2.2.2.2.1
  · exact globalConstitutive_auxiliary_contDiff
  · exact globalTemporal_smooth.2.2.2.2.2.2.1
  · exact globalTemporal_smooth.2.2.2.2.2.2.2.1
  · exact globalTemporal_smooth.2.2.2.2.2.2.2.2

private theorem globalConstitutive_nondegenerate :
    GlobalConstitutive.Nondegenerate := by
  intro point
  change Matrix.det (GlobalTemporal.coframe point) ≠ 0
  exact globalTemporal_nondegenerate point

/-- Public regularity face of the exact constitutive stage consumed by both
the radial writer and the alternative Cauchy temporal P286 evaluator.  This
is a qualification of the already-generated stage, not a new current. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_smooth :
    GlobalConstitutive.Smooth :=
  globalConstitutive_smooth

/-- The same exact constitutive stage is nondegenerate everywhere. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_nondegenerate :
    GlobalConstitutive.Nondegenerate :=
  globalConstitutive_nondegenerate

private theorem chargedCoefficient_eq_currents
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (direction : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient source 0 point
        (toContinuumPointField configuration point) direction =
      p286ScalarCurrentCoefficient source configuration direction point +
        p286MatterCurrentCoefficient source configuration direction point := by
  unfold formNativeChargedGaugeFirstCoefficient
    p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point,
    pointwiseMatterP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point]
  ring

private theorem chargedThreeForm_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ (fun point =>
      formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField configuration point)) := by
  let basis := Module.finBasis ℝ P286GaugeOneForm
  let coordinates := fun point =>
    basis.dualBasis.equivFun
      (formNativeChargedGaugeFirstLinearMap source 0 point
        (toContinuumPointField configuration point))
  have coordinatesRegular : ContDiff ℝ ∞ coordinates := by
    apply contDiff_pi'
    intro index
    rw [show (fun point => coordinates point index) =
      fun point =>
        p286ScalarCurrentCoefficient source configuration (basis index) point +
          p286MatterCurrentCoefficient source configuration (basis index) point by
      funext point
      calc
        coordinates point index =
            formNativeChargedGaugeFirstLinearMap source 0 point
              (toContinuumPointField configuration point) (basis index) :=
          basis.dualBasis_equivFun _ index
        _ = formNativeChargedGaugeFirstCoefficient source 0 point
              (toContinuumPointField configuration point) (basis index) := rfl
        _ = _ := chargedCoefficient_eq_currents source configuration point
          (basis index)]
    exact
      (p286ScalarCurrentCoefficient_contDiff source configuration smooth
        nondegenerate (basis index)).add
      (p286MatterCurrentCoefficient_contDiff source configuration smooth
        nondegenerate (basis index))
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286GaugeThreeFormWedgeEquiv.symm
  let reconstructCLM :
      (Fin (Module.finrank ℝ P286GaugeOneForm) → ℝ) →L[ℝ]
        P286GaugeThreeForm :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  have reconstructedRegular : ContDiff ℝ ∞ (fun point =>
      reconstructCLM (coordinates point)) :=
    reconstructCLM.contDiff.comp coordinatesRegular
  rw [show (fun point =>
      formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField configuration point)) =
      fun point => reconstructCLM (coordinates point) by
    funext point
    change p286GaugeThreeFormWedgeEquiv.symm
        (formNativeChargedGaugeFirstLinearMap source 0 point
          (toContinuumPointField configuration point)) =
      reconstruct (coordinates point)
    unfold reconstruct coordinates
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]]
  exact reconstructedRegular

/-- Generic C-infinity regularity of the action-generated charged P286
three-form. -/
theorem formNativeChargedGaugeThreeForm_contDiff_of_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞ (fun point =>
      formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField configuration point)) :=
  chargedThreeForm_contDiff source configuration smooth nondegenerate

private theorem connectionExteriorAction_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ (fun point =>
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate configuration point)
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)) := by
  have connectionRegular : ContDiff ℝ ∞
      (holonomicP286GaugeConnectionCoordinate configuration) := by
    apply contDiff_pi'
    intro direction
    exact smooth.2.2.2.2.1 direction
  have auxiliaryRegular : ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate configuration) := by
    apply contDiff_pi'
    intro pair
    exact smooth.2.2.2.2.2.1 pair
  have adjointRegular (direction : LorentzianIndex) (pair : Fin 6) :
      ContDiff ℝ ∞ (fun point =>
        p286CoordinateLieBracket
          (holonomicP286GaugeConnectionCoordinate configuration point
            direction)
          (holonomicP286GaugeAuxiliaryCoordinate configuration point pair)) :=
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.contDiff.comp
      (contDiff_pi.mp connectionRegular direction)).clm_apply
        (contDiff_pi.mp auxiliaryRegular pair)
  have orderedRegular (direction first second : LorentzianIndex) :
      ContDiff ℝ ∞ (fun point =>
        orderedP286GaugeTwoFormComponent
          (p286GaugeTwoFormAdjoint
            (holonomicP286GaugeConnectionCoordinate configuration point
              direction)
            (holonomicP286GaugeAuxiliaryCoordinate configuration point))
          first second) := by
    unfold orderedP286GaugeTwoFormComponent p286GaugeTwoFormAdjoint
    apply ContDiff.sum
    intro pair _
    exact
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        (orientedLorentzBivectorBasisCoefficient pair first second : ℝ))).smul
          (adjointRegular direction pair)
  apply contDiff_pi'
  intro triple
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [Pi.zero_apply, zero_add]
  exact
    ((orderedRegular (threeFormFirst triple) (threeFormSecond triple)
      (threeFormThird triple)).add
      (orderedRegular (threeFormSecond triple) (threeFormThird triple)
        (threeFormFirst triple))).add
      (orderedRegular (threeFormThird triple) (threeFormFirst triple)
        (threeFormSecond triple))

/-- Generic C-infinity regularity of the algebraic connection action on the
primitive P286 auxiliary. -/
theorem pointwiseP286GaugeTwoFormConnectionExteriorAction_contDiff_of_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ (fun point =>
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate configuration point)
        (holonomicP286GaugeAuxiliaryCoordinate configuration point)) :=
  connectionExteriorAction_contDiff configuration smooth

private theorem requiredExterior_contDiff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞
      (pointwiseDirectP286RequiredExteriorDerivative source configuration) := by
  unfold pointwiseDirectP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm
  exact (chargedThreeForm_contDiff source configuration smooth nondegenerate
    ).neg.sub (connectionExteriorAction_contDiff configuration smooth)

/-- Generic global regularity of the current-computed direct P286 exterior
demand.  This exposes the already-proved action-read calculation for
downstream Cauchy homotopies; it constructs no response field. -/
theorem pointwiseDirectP286RequiredExteriorDerivative_contDiff_of_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    ContDiff ℝ ∞
      (pointwiseDirectP286RequiredExteriorDerivative source configuration) :=
  requiredExterior_contDiff source configuration smooth nondegenerate

private theorem globalConstitutive_constitutiveAt (point : BasePoint) :
    diracDualFormNativeConstitutiveAuxiliaryField Source
        GlobalConstitutive point =
      GlobalConstitutive.gaugeAuxiliary point := by
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [show GlobalConstitutive.coframe = GlobalTemporal.coframe by rfl,
    holonomicGaugeCurvature_eq_of_connection_eq
      GlobalConstitutive GlobalTemporal
      (diracDualFormNativeConstitutiveWrittenCurrent_gaugeConnection
        Source GlobalTemporal) point,
    show GlobalConstitutive.gaugeAuxiliary =
        diracDualFormNativeConstitutiveAuxiliaryField
          Source GlobalTemporal by
      exact diracDualFormNativeConstitutiveWrittenCurrent_gaugeAuxiliary
        Source GlobalTemporal]
  rfl

/-- The exact constitutive stage is literally the source/action constitutive
read at every point.  This public same-stage equality lets downstream
evaluators use required-profile naturality without replaying its proof. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_constitutiveAt
    (point : BasePoint) :
    diracDualFormNativeConstitutiveAuxiliaryField Source
        GlobalConstitutive point =
      GlobalConstitutive.gaugeAuxiliary point :=
  globalConstitutive_constitutiveAt point

private theorem globalConstitutive_requiredExterior_contDiff :
    ContDiff ℝ ∞
      (completeJointP286RequiredExteriorProfile Source GlobalConstitutive) := by
  rw [show completeJointP286RequiredExteriorProfile Source GlobalConstitutive =
      pointwiseDirectP286RequiredExteriorDerivative Source GlobalConstitutive by
    funext contact
    exact
      completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
        Source GlobalConstitutive contact
        (globalConstitutive_constitutiveAt contact)]
  exact requiredExterior_contDiff Source GlobalConstitutive
    globalConstitutive_smooth globalConstitutive_nondegenerate

/-- Global smoothness of the action-owned P286 exterior demand at the exact
SafeFinal constitutive stage.  It is the input regularity needed by a
source/current-only temporal homotopy; no equation or zero fibre is stored. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalConstitutive_requiredExterior_contDiff :
    ContDiff ℝ ∞
      (completeJointP286RequiredExteriorProfile Source GlobalConstitutive) :=
  globalConstitutive_requiredExterior_contDiff

private theorem globalP286JetCLM_contDiff :
    ContDiff ℝ ∞
      (cauchySafeJointGlobalP286JetCLM Source GlobalConstitutive) := by
  exact cauchySafeJointGlobalP286JetCLM_contDiff_of_required
    Source GlobalConstitutive globalConstitutive_requiredExterior_contDiff

/-- The complete source-owned P286 first-jet one-form is globally smooth on
the exact constitutive current used by the Cauchy-safe occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalP286JetCLM_contDiff :
    ContDiff ℝ ∞
      (cauchySafeJointGlobalP286JetCLM Source GlobalConstitutive) :=
  globalP286JetCLM_contDiff

private theorem globalP286_auxiliaryCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate GlobalP286) := by
  rw [show holonomicP286GaugeAuxiliaryCoordinate GlobalP286 =
      (fun _ => holonomicP286GaugeAuxiliaryCoordinate GlobalConstitutive 0) +
        cauchySafeJointGlobalP286RadialIncrement Source GlobalConstitutive by
    funext point
    change holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite
          Source GlobalConstitutive) point = _
    rw [sourceActionGeneratedDiracDualCauchySafeGlobalP286PathWrite_coordinate]
    rfl]
  exact contDiff_const.add
    (radialCurveIntegral_contDiff_infty_of_contDiff
      (cauchySafeJointGlobalP286JetCLM Source GlobalConstitutive)
      globalP286JetCLM_contDiff)

private theorem globalP286_coframe_contDiff :
    ContDiff ℝ ∞ GlobalP286.coframe := by
  change ContDiff ℝ ∞ GlobalConstitutive.coframe
  exact holonomicCoframe_contDiff GlobalConstitutive
    globalConstitutive_smooth

private theorem globalP286ContactField_coframe_contDiff :
    ContDiff ℝ ∞ (fun contact =>
      (GlobalP286ContactField contact).coframe) := by
  change ContDiff ℝ ∞ GlobalP286.coframe
  exact globalP286_coframe_contDiff

private theorem globalP286_gaugeParameter_contDiff :
    ContDiff ℝ ∞ (fun contact =>
      coframeGaugeActionParameterOfField
        (GlobalP286ContactField contact)) := by
  change ContDiff ℝ ∞ (fun contact =>
    (holonomicP286GaugeAuxiliaryCoordinate GlobalP286 contact,
      holonomicP286GaugeCurvatureCoordinate GlobalP286 contact))
  apply ContDiff.prodMk globalP286_auxiliaryCoordinate_contDiff
  rw [show holonomicP286GaugeCurvatureCoordinate GlobalP286 =
      holonomicP286GaugeCurvatureCoordinate GlobalConstitutive by rfl]
  apply contDiff_pi'
  intro pair
  exact holonomicGaugeCurvature_coordinate_contDiff GlobalConstitutive
    globalConstitutive_smooth pair

private theorem globalP286_matterParameter_contDiff :
    ContDiff ℝ ∞ (fun contact =>
      coframeMatterActionParameterOfField
        (GlobalP286ContactField contact)) := by
  change ContDiff ℝ ∞ (fun contact =>
    (GlobalP286.scalar contact,
      holonomicScalarCovariantDerivative GlobalP286 contact,
      matterCoordinateEquiv (GlobalP286.matter contact),
      (fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative GlobalP286 contact direction)),
      matterDualCoordinates (GlobalP286.conjugateMatter contact)))
  rw [show (fun contact =>
      (GlobalP286.scalar contact,
        holonomicScalarCovariantDerivative GlobalP286 contact,
        matterCoordinateEquiv (GlobalP286.matter contact),
        (fun direction => matterCoordinateEquiv
          (holonomicMatterCovariantDerivative GlobalP286 contact direction)),
        matterDualCoordinates (GlobalP286.conjugateMatter contact))) =
      fun contact =>
        (GlobalConstitutive.scalar contact,
          holonomicScalarCovariantDerivative GlobalConstitutive contact,
          matterCoordinateEquiv (GlobalConstitutive.matter contact),
          (fun direction => matterCoordinateEquiv
            (holonomicMatterCovariantDerivative GlobalConstitutive contact
              direction)),
          matterDualCoordinates
            (GlobalConstitutive.conjugateMatter contact)) by rfl]
  have scalarDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      holonomicScalarCovariantDerivative GlobalConstitutive contact := by
    apply contDiff_pi'
    intro direction
    exact holonomicScalarCovariantDerivative_contDiff_local
      GlobalConstitutive globalConstitutive_smooth direction
  have matterDerivativeRegular : ContDiff ℝ ∞ fun contact =>
      fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative GlobalConstitutive contact
          direction) := by
    apply contDiff_pi'
    intro direction
    exact holonomicMatterCovariantDerivative_coordinate_contDiff_local
      GlobalConstitutive globalConstitutive_smooth direction
  exact (globalConstitutive_smooth.2.2.2.2.2.2.1.prodMk
    (scalarDerivativeRegular.prodMk
      (globalConstitutive_smooth.2.2.2.2.2.2.2.1.prodMk
        (matterDerivativeRegular.prodMk
          (holonomicConjugateMatterCoordinates_contDiff
            GlobalConstitutive globalConstitutive_smooth))))
      )

private theorem globalP286_nondegenerate (point : BasePoint) :
    Matrix.det (GlobalP286.coframe point) ≠ 0 := by
  change Matrix.det (GlobalConstitutive.coframe point) ≠ 0
  exact globalConstitutive_nondegenerate point

private theorem globalP286ContactField_nondegenerate (point : BasePoint) :
    Matrix.det (GlobalP286ContactField point).coframe ≠ 0 := by
  change Matrix.det (GlobalP286.coframe point) ≠ 0
  exact globalP286_nondegenerate point

private theorem globalP286_gaugeEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ (fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (GlobalP286ContactField contact)
        (coframeCoordinateDirection row column)) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt_infty
    Source GlobalP286ContactField point
      globalP286_gaugeParameter_contDiff.contDiffAt
      globalP286ContactField_coframe_contDiff.contDiffAt
      (globalP286ContactField_nondegenerate point) row column

private theorem globalP286_matterEuler_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source contact
        (GlobalP286ContactField contact)
        (coframeCoordinateDirection row column)) := by
  rw [show (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source contact
        (GlobalP286ContactField contact)
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (GlobalP286ContactField contact)
          (coframeCoordinateDirection row column) by
    funext contact
    rw [diracDualFormNativeCoframeMatterEulerCovector_point_independent
      Source contact (GlobalP286ContactField contact)]]
  rw [contDiff_iff_contDiffAt]
  intro point
  exact diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt_infty
    Source 0 GlobalP286ContactField point
      globalP286_matterParameter_contDiff.contDiffAt
      globalP286ContactField_coframe_contDiff.contDiffAt
      (globalP286ContactField_nondegenerate point) row column

private theorem globalP286_coframeWedgeCurvature_contDiff :
    ContDiff ℝ ∞ (fun contact =>
      gravityInternalPairVarianceNormalization
        (coframeWedge (GlobalP286.coframe contact))) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  simp only [gravityInternalPairVarianceNormalization_apply]
  unfold coframeWedge
  have coframeComponent (row column : LorentzianIndex) :
      ContDiff ℝ ∞ (fun contact =>
        GlobalP286.coframe contact row column) :=
    contDiff_pi.mp
      (contDiff_pi.mp globalP286_coframe_contDiff row) column
  fun_prop

private theorem globalP286_load_coordinate_contDiff
    (row column : LorentzianIndex) :
    ContDiff ℝ ∞ (fun contact =>
      (-diracDualFormNativeCoframeECContactLoad Source GlobalP286 contact)
        (coframeCoordinateDirection row column)) := by
  unfold diracDualFormNativeCoframeECContactLoad
  simp only [neg_apply, add_apply]
  rw [contDiff_iff_contDiffAt]
  intro point
  apply ContDiffAt.neg
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · exact coframeDiracDualECCurvatureObservation_coordinate_contDiffAt
        GlobalP286.coframe
        (fun contact => gravityInternalPairVarianceNormalization
          (coframeWedge (GlobalP286.coframe contact))) point
        globalP286_coframe_contDiff.contDiffAt
        globalP286_coframeWedgeCurvature_contDiff.contDiffAt row column
    · exact (globalP286_gaugeEuler_coordinate_contDiff row column).contDiffAt
  · exact (globalP286_matterEuler_coordinate_contDiff row column).contDiffAt

private theorem globalP286_preparedCurvature_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ (fun contact =>
      holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual GlobalP286) contact
        internalPair spacetimePair) := by
  rw [show (fun contact =>
      holonomicGravityCurvature
        (diracDualFormNativeCoframeECContactPreparedActual GlobalP286) contact
        internalPair spacetimePair) =
      fun contact => holonomicGravityCurvature GlobalConstitutive contact
        internalPair spacetimePair by rfl]
  exact holonomicGravityCurvature_component_contDiff GlobalConstitutive
    globalConstitutive_smooth internalPair spacetimePair

private theorem globalP286_target_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ (fun contact =>
      diracDualFormNativeCoframeECContactCurvatureTarget Source GlobalP286
        contact internalPair spacetimePair) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  unfold diracDualFormNativeCoframeECContactCurvatureTarget
  apply coframeDiracDualECCurvatureTarget_component_contDiffAt (n := ∞)
  · exact globalP286_coframe_contDiff.contDiffAt
  · apply contDiffAt_pi'
    intro targetInternalPair
    apply contDiffAt_pi'
    intro targetSpacetimePair
    exact (globalP286_preparedCurvature_component_contDiff
      targetInternalPair targetSpacetimePair).contDiffAt
  · intro row column
    exact (globalP286_load_coordinate_contDiff row column).contDiffAt
  · apply coframeTwoFormWedgeScale_ne_zero
    rw [Matrix.det_transpose]
    exact globalP286_nondegenerate point

private theorem globalP286_normalizedDerivative_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ (fun contact =>
      normalizedDerivativeBivector
        (GlobalP286.gravityConnection contact)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          Source GlobalP286 contact)
        internalPair spacetimePair) := by
  unfold normalizedDerivativeBivector originLorentzBracketCurvature
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine contDiff_const.mul
    ((globalP286_target_component_contDiff
      internalPair spacetimePair).sub (contDiff_const.mul ?_))
  apply ContDiff.sum
  intro middle _
  have originComponent
      (formDirection internalOut internalIn : LorentzianIndex) :
      ContDiff ℝ ∞ (fun contact =>
        GlobalP286.gravityConnection contact formDirection
          internalOut internalIn) := by
    change ContDiff ℝ ∞ (fun contact =>
      GlobalConstitutive.gravityConnection contact formDirection
        internalOut internalIn)
    exact globalConstitutive_smooth.2.1 formDirection internalOut internalIn
  exact
    ((originComponent (pairFirst spacetimePair)
      (pairFirst internalPair) middle).mul
      (originComponent (pairSecond spacetimePair)
        middle (pairSecond internalPair))).sub
      ((originComponent (pairSecond spacetimePair)
        (pairFirst internalPair) middle).mul
        (originComponent (pairFirst spacetimePair)
          middle (pairSecond internalPair)))

private theorem loweredConnectionFirstJet_normalForm
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

private theorem jetOneForm_contDiff
    (derivativeDirection : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun contact =>
        cauchySafeJointGlobalECJetOneForm Source GlobalP286 contact
          derivativeDirection) := by
  apply contDiff_pi'
  intro formDirection
  apply contDiff_pi'
  intro internalPair
  unfold cauchySafeJointGlobalECJetOneForm
  rw [show
    (fun contact =>
      cauchySafeJointGlobalECLoweredConnectionFirstJet Source GlobalP286
        contact derivativeDirection formDirection internalPair) =
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
    exact loweredConnectionFirstJet_normalForm contact derivativeDirection
      formDirection internalPair]
  apply ContDiff.sum
  intro spacetimePair _
  exact
    (globalP286_normalizedDerivative_component_contDiff
      internalPair spacetimePair).mul contDiff_const

theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff :
    ContDiff ℝ ∞
      (cauchySafeJointGlobalECJetCLM Source GlobalP286) := by
  unfold cauchySafeJointGlobalECJetCLM
  apply ContDiff.sum
  intro derivativeDirection _
  have regular := jetOneForm_contDiff derivativeDirection
  fun_prop

private theorem globalP286_smooth : GlobalP286.Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalConstitutive_smooth.1
  · exact globalConstitutive_smooth.2.1
  · exact globalConstitutive_smooth.2.2.1
  · exact globalConstitutive_smooth.2.2.2.1
  · exact globalConstitutive_smooth.2.2.2.2.1
  · intro pair
    change ContDiff ℝ ∞ (fun point =>
      holonomicP286GaugeAuxiliaryCoordinate GlobalP286 point pair)
    exact contDiff_pi.mp globalP286_auxiliaryCoordinate_contDiff pair
  · exact globalConstitutive_smooth.2.2.2.2.2.2.1
  · exact globalConstitutive_smooth.2.2.2.2.2.2.2.1
  · exact globalConstitutive_smooth.2.2.2.2.2.2.2.2

private theorem globalECRadialIncrement_contDiff :
    ContDiff ℝ ∞
      (cauchySafeJointGlobalECRadialIncrement Source GlobalP286) :=
  radialCurveIntegral_contDiff_infty_of_contDiff
    (cauchySafeJointGlobalECJetCLM Source GlobalP286)
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff

private theorem globalECConnection_component_contDiff
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      (cauchySafeJointGlobalECPathCurrent Source Current).gravityConnection
        point direction internalOut internalIn) := by
  have liftedRegular : ContDiff ℝ ∞ (fun point =>
      radialLorentzConnectionLiftCLM
        (cauchySafeJointGlobalECRadialIncrement Source GlobalP286 point)) :=
    radialLorentzConnectionLiftCLM.contDiff.comp
      globalECRadialIncrement_contDiff
  have coordinateRegular : ContDiff ℝ ∞ (fun point =>
      radialLorentzConnectionCoordinateCLM direction internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement
            Source GlobalP286 point))) :=
    (radialLorentzConnectionCoordinateCLM direction internalOut internalIn
      ).contDiff.comp liftedRegular
  change ContDiff ℝ ∞ (fun point =>
    GlobalP286.gravityConnection 0 direction internalOut internalIn +
      radialLorentzConnectionCoordinateCLM direction internalOut internalIn
        (radialLorentzConnectionLiftCLM
          (cauchySafeJointGlobalECRadialIncrement Source GlobalP286 point)))
  exact contDiff_const.add coordinateRegular

/-- The exact post-EC current used by the canonical Galerkin action is a
single source-generated smooth spacetime configuration. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECPathCurrent_smooth :
    (cauchySafeJointGlobalECPathCurrent Source Current).Smooth := by
  have coframeRegular : ContDiff ℝ ∞ GlobalP286.coframe :=
    holonomicCoframe_contDiff GlobalP286 globalP286_smooth
  have auxiliaryRegular : ContDiff ℝ ∞ (fun point =>
      physicalIIPlusBivector (GlobalP286.coframe point)) :=
    StageNineIIPlusRestriction.physicalIIPlusBivector_contDiff.comp
      coframeRegular
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact globalP286_smooth.1
  · exact globalECConnection_component_contDiff
  · intro internalPair spacetimePair
    exact contDiff_pi.mp
      (contDiff_pi.mp auxiliaryRegular internalPair) spacetimePair
  · exact globalP286_smooth.2.2.2.1
  · exact globalP286_smooth.2.2.2.2.1
  · exact globalP286_smooth.2.2.2.2.2.1
  · exact globalP286_smooth.2.2.2.2.2.2.1
  · exact globalP286_smooth.2.2.2.2.2.2.2.1
  · exact globalP286_smooth.2.2.2.2.2.2.2.2

theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff_one :
    ContDiff ℝ 1
      (cauchySafeJointGlobalECJetCLM Source GlobalP286) :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff.of_le
    (by simp)

theorem
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiffAt_one_origin :
    ContDiffAt ℝ 1
      (cauchySafeJointGlobalECJetCLM Source GlobalP286) 0 := by
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECJetCLM_contDiff_one.contDiffAt

end
end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
