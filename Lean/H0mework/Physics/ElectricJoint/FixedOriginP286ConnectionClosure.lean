import H0mework.Physics.JointVariation.LiveElectricGlobalDevelopmentOperator
import H0mework.Physics.FixedJoint.FixedP286RequiredProfileMeasurableGerm

/-!
# Fixed P506/L0 live-electric origin P286 connection closure

This module discharges the analytic integration seam of the fixed
source/current-only live-electric P286 producer.  A globally strongly
measurable proof-side representative is generated for the local required
profile germ, transported through the canonical time primitive, and then
read back on the same final global actual.

The representative is never installed into a source or current.  No
residual coordinate, support branch, target field, regularity receipt, or
equation certificate enters the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginP286ConnectionClosure

open Asymptotics Filter MeasureTheory Set
open ComplexConjugate
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open PointwiseLorentzianCoframeJet
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceCompatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286ZeroSliceContinuity
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointP286RequiredExteriorProfileRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeFixedP506P286RequiredProfileMeasurableGerm
open StageNineCanonicalTimePrimitiveMeasurableGermCalculus
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDiracDualFormNativeSpinTorsionAcceptance
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeMatterSpinThreeFormRegularity
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionAlgebraicCurrentRegularity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineScalarPointwiseEquation
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Interval Matrix.Norms.Elementwise Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fixedTemporalPrimitiveP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance fixedTemporalPrimitiveP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance fixedTemporalPrimitiveP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

local instance fixedTemporalPrimitiveLorentzianCoframeMeasurableSpace :
    MeasurableSpace LorentzianCoframe :=
  borel LorentzianCoframe

local instance fixedTemporalPrimitiveLorentzianCoframeBorelSpace :
    BorelSpace LorentzianCoframe :=
  ⟨rfl⟩

local instance fixedTemporalPrimitivePhysicalBivectorThreeFormMeasurableSpace :
    MeasurableSpace PhysicalBivectorThreeForm :=
  borel PhysicalBivectorThreeForm

local instance fixedTemporalPrimitivePhysicalBivectorThreeFormBorelSpace :
    BorelSpace PhysicalBivectorThreeForm :=
  ⟨rfl⟩

local instance fixedTemporalPrimitiveMatterCoordinateMeasurableSpace :
    MeasurableSpace MatterCoordinateCarrier :=
  borel MatterCoordinateCarrier

local instance fixedTemporalPrimitiveMatterCoordinateBorelSpace :
    BorelSpace MatterCoordinateCarrier :=
  ⟨rfl⟩

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedAlgebraicCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedInput

private abbrev FixedZeroSliceAnchor : StageNineHolonomicConfiguration :=
  completeJointP286ZeroSliceAnchoredCurrent positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

private abbrev FixedCorrectionProfile : BasePoint → P286GaugeTwoForm :=
  completeJointP286TemporalCorrectionProfile positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

private abbrev FixedCorrectionPrimitive : BasePoint → P286GaugeTwoForm :=
  completeJointP286TemporalCorrectionPrimitive positiveSmoothUnifiedSource
    FixedAlgebraicCurrent

private abbrev FixedTemporalCurrent : StageNineHolonomicConfiguration :=
  completeJointGlobalP286Current positiveSmoothUnifiedSource FixedInput

private abbrev FixedLiveElectricBase : StageNineHolonomicConfiguration :=
  completeJointP286LiveElectricZeroSliceMagneticBase
    positiveSmoothUnifiedSource FixedAlgebraicCurrent

private abbrev FixedLiveElectricProfile : BasePoint → P286GaugeTwoForm :=
  completeJointP286LiveElectricActionTemporalWriteProfile
    positiveSmoothUnifiedSource FixedAlgebraicCurrent

private abbrev FixedLiveElectricPrimitive : BasePoint → P286GaugeTwoForm :=
  completeJointP286LiveElectricActionTemporalWritePrimitive
    positiveSmoothUnifiedSource FixedAlgebraicCurrent

private abbrev FixedLiveElectricCauchyCurrent :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
    positiveSmoothUnifiedSource FixedAlgebraicCurrent

private def FixedCartanActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource FixedInput

private abbrev FixedCanonicalInput : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalActionInput

private abbrev FixedCanonicalConnectionActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalConnectionCandidate
    fixedP506L0P286CanonicalGeneratedWrite

private abbrev FixedMatterTemporalPrimitive :
    BasePoint → MatterCoordinateCarrier :=
  canonicalTimePrimitive
    (completeJointMatterTemporalCoordinateCorrection
      positiveSmoothUnifiedSource FixedInput)

private abbrev FixedAdjointTemporalPrimitive :
    BasePoint → MatterCoordinateCarrier :=
  canonicalTimePrimitive
    (completeJointAdjointTemporalCoordinateCorrection
      positiveSmoothUnifiedSource FixedInput)

private abbrev FixedScalarSecondPrimitive :
    BasePoint → ScalarCoordinateCarrier :=
  canonicalTimeSecondPrimitive
    (completeJointScalarAccelerationProfile
      positiveSmoothUnifiedSource FixedInput)

/-- A proof-side carrier for measurable action data.  It is never installed
as a source or current; the unused point-field coordinates are set to zero. -/
private def fixedP506ActionDataSurrogate
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (scalarCovariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (matter conjugateMatter : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : StageNineContinuumPointField where
  coframe := FixedInput.coframe point
  gravityCurvature := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeCurvature := 0
  gaugeAuxiliary := 0
  scalar := scalar point
  scalarCovariantDerivative := scalarCovariantDerivative point
  matter := matterCoordinateEquiv.symm (matter point)
  matterCovariantDerivative := 0
  conjugateMatter := matterDualOfCoordinates (conjugateMatter point)

private def canonicalP286TemporalCorrectionLinear :
    P286GaugeThreeForm →ₗ[ℝ] P286GaugeTwoForm where
  toFun := fun target =>
    formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm target
      canonicalLorentzianTimeDirection
  map_add' := by
    intro first second
    funext pair
    fin_cases pair <;>
      simp [formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
        canonicalLorentzianTimeDirection]
    all_goals module
  map_smul' := by
    intro parameter target
    funext pair
    fin_cases pair <;>
      simp [formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
        canonicalLorentzianTimeDirection]

private def canonicalP286TemporalCorrectionCLM :
    P286GaugeThreeForm →L[ℝ] P286GaugeTwoForm :=
  canonicalP286TemporalCorrectionLinear.toContinuousLinearMap

private theorem canonicalP286TemporalCorrectionCLM_apply
    (target : P286GaugeThreeForm) :
    canonicalP286TemporalCorrectionCLM target =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm target
        canonicalLorentzianTimeDirection :=
  rfl

private theorem
    fixedP506L0CompleteJointP286LiveElectricBase_exteriorDerivative_stronglyMeasurable_probe :
    StronglyMeasurable
      (holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedLiveElectricBase) := by
  have derivativeMeasurable :
      StronglyMeasurable
        (fderiv ℝ
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedLiveElectricBase)) :=
    (measurable_fderiv ℝ
      (holonomicP286GaugeAuxiliaryCoordinate
        FixedLiveElectricBase)).stronglyMeasurable
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    fieldDirectionalDerivative
    orderedP286GaugeTwoFormComponent
  apply Measurable.stronglyMeasurable
  apply measurable_pi_iff.mpr
  intro triple
  fun_prop

private theorem
    exists_fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_stronglyMeasurable_germ_probe :
    ∃ representative : BasePoint → P286GaugeTwoForm,
      StronglyMeasurable representative ∧
      FixedLiveElectricProfile =ᶠ[𝓝 0] representative := by
  obtain ⟨requiredRepresentative, requiredRepresentativeMeasurable,
      requiredRepresentativeEventuallyEq⟩ :=
    exists_fixedP506L0CompleteJointP286RequiredExteriorProfile_stronglyMeasurable_germ
  let representative : BasePoint → P286GaugeTwoForm :=
    fun point =>
      canonicalP286TemporalCorrectionCLM
        (requiredRepresentative point -
          holonomicP286GaugeAuxiliaryExteriorDerivative
            FixedLiveElectricBase point)
  have differenceMeasurable :
      StronglyMeasurable fun point =>
        requiredRepresentative point -
          holonomicP286GaugeAuxiliaryExteriorDerivative
            FixedLiveElectricBase point :=
    requiredRepresentativeMeasurable.sub
      fixedP506L0CompleteJointP286LiveElectricBase_exteriorDerivative_stronglyMeasurable_probe
  have representativeMeasurable :
      StronglyMeasurable representative :=
    canonicalP286TemporalCorrectionCLM.continuous.stronglyMeasurable
      |>.comp_measurable differenceMeasurable.measurable
  refine ⟨representative, representativeMeasurable, ?_⟩
  filter_upwards [requiredRepresentativeEventuallyEq] with point requiredEq
  unfold FixedLiveElectricProfile
    completeJointP286LiveElectricActionTemporalWriteProfile representative
  rw [canonicalP286TemporalCorrectionCLM_apply, requiredEq]

private theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWritePrimitive_differentiableAt_origin_probe :
    DifferentiableAt ℝ FixedLiveElectricPrimitive 0 := by
  obtain ⟨representative, representativeMeasurable,
      profileEventuallyEq⟩ :=
    exists_fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_stronglyMeasurable_germ_probe
  apply differentiableAt_pi.mpr
  intro pair
  change
    DifferentiableAt ℝ
      (canonicalTimePrimitive
        (fun point => FixedLiveElectricProfile point pair))
      0
  have representativeCoordinateMeasurable :
      StronglyMeasurable fun point => representative point pair :=
    (continuous_apply pair).stronglyMeasurable.comp_measurable
      representativeMeasurable.measurable
  have coordinateEventuallyEq :
      (fun point => FixedLiveElectricProfile point pair) =ᶠ[𝓝 0]
        fun point => representative point pair :=
    profileEventuallyEq.mono fun point equality =>
      congrFun equality pair
  exact
    (canonicalTimePrimitive_hasFDerivAt_zero_of_continuousAt_of_eventuallyEq_stronglyMeasurable
      (fun point => FixedLiveElectricProfile point pair)
      (fun point => representative point pair)
      (continuousAt_pi.mp
        fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_continuousAt_origin
        pair)
      representativeCoordinateMeasurable
      coordinateEventuallyEq).differentiableAt

private theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_differentiableAt_origin_probe :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate
        FixedLiveElectricCauchyCurrent)
      0 := by
  have coordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent =
        holonomicP286GaugeAuxiliaryCoordinate
            FixedLiveElectricBase +
          FixedLiveElectricPrimitive := by
    funext point
    rw [
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_coordinate,
      ← completeJointP286LiveElectricZeroSliceMagneticBase_coordinate]
    simp only [Pi.add_apply]
  rw [coordinateEq]
  exact
    fixedP506L0CompleteJointP286LiveElectricZeroSliceMagneticBase_auxiliaryCoordinate_differentiableAt_origin.add
      fixedP506L0CompleteJointP286LiveElectricActionTemporalWritePrimitive_differentiableAt_origin_probe

private theorem canonicalCauchyTimeLine_zero_contDiff_probe :
    ContDiff ℝ ∞
      (fun candidateTime : ℝ =>
        canonicalCauchySlicePoint candidateTime
          (0 : StageNineSpatialPoint)) := by
  apply contDiff_piLp'
  intro direction
  fin_cases direction
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three, Function.id_def] using
      (contDiff_id : ContDiff ℝ ∞
        (fun candidateTime : ℝ => candidateTime))
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))
  · simpa [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

private theorem canonicalCauchySlicePoint_zero_zero_probe :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem stronglyMeasurableAtFilter_nhds_zero_of_eventuallyEq_probe
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field representative : ℝ → E)
    (representativeMeasurable : StronglyMeasurable representative)
    (eventuallyEq : field =ᶠ[𝓝 0] representative) :
    StronglyMeasurableAtFilter field (𝓝 0) MeasureTheory.volume := by
  obtain ⟨domain, domainSubset, domainOpen, zeroMem⟩ :=
    mem_nhds_iff.mp eventuallyEq
  refine
    ⟨domain, domainOpen.mem_nhds zeroMem, ?_⟩
  apply
    representativeMeasurable.aestronglyMeasurable.restrict.congr
  filter_upwards [ae_restrict_mem domainOpen.measurableSet] with point pointIn
  exact (domainSubset pointIn).symm

private theorem
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_probe
    (pair : Fin 6) :
    StronglyMeasurableAtFilter
      (fun candidateTime =>
        FixedLiveElectricProfile
          (canonicalCauchySlicePoint candidateTime 0) pair)
      (𝓝 0) MeasureTheory.volume := by
  obtain ⟨representative, representativeMeasurable,
      profileEventuallyEq⟩ :=
    exists_fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_stronglyMeasurable_germ_probe
  let timeLine : ℝ → BasePoint :=
    fun candidateTime =>
      canonicalCauchySlicePoint candidateTime
        (0 : StageNineSpatialPoint)
  have timeLineMeasurable : Measurable timeLine :=
    canonicalCauchyTimeLine_zero_contDiff_probe.continuous.measurable
  have representativeTimeLineMeasurable :
      StronglyMeasurable fun candidateTime =>
        representative (timeLine candidateTime) pair := by
    have coordinateMeasurable :
        StronglyMeasurable fun point => representative point pair :=
      (continuous_apply pair).stronglyMeasurable.comp_measurable
        representativeMeasurable.measurable
    exact coordinateMeasurable.comp_measurable timeLineMeasurable
  have timeLineTendsto :
      Tendsto timeLine (𝓝 0) (𝓝 0) := by
    have actual :
        Tendsto timeLine (𝓝 0) (𝓝 (timeLine 0)) :=
      canonicalCauchyTimeLine_zero_contDiff_probe.continuous.continuousAt
    rw [show timeLine 0 = 0 by
      exact canonicalCauchySlicePoint_zero_zero_probe] at actual
    exact actual
  have timeLineEventuallyEq :
      (fun candidateTime =>
        FixedLiveElectricProfile (timeLine candidateTime) pair) =ᶠ[𝓝 0]
        fun candidateTime =>
          representative (timeLine candidateTime) pair :=
    (timeLineTendsto.eventually profileEventuallyEq).mono
      fun candidateTime equality => congrFun equality pair
  exact
    stronglyMeasurableAtFilter_nhds_zero_of_eventuallyEq_probe
      (fun candidateTime =>
        FixedLiveElectricProfile (timeLine candidateTime) pair)
      (fun candidateTime =>
        representative (timeLine candidateTime) pair)
      representativeTimeLineMeasurable timeLineEventuallyEq

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin_noPremise :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedLiveElectricCauchyCurrent 0 =
      completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
        FixedAlgebraicCurrent 0 :=
  fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_exteriorDerivative_origin
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_differentiableAt_origin_probe
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_probe

theorem
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_connectionEquation_origin_noPremise :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedLiveElectricCauchyCurrent 0 =
      0 :=
  fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_connectionEquation_origin
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_auxiliaryCoordinate_differentiableAt_origin_probe
    fixedP506L0CompleteJointP286LiveElectricActionTemporalWriteProfile_timeLine_stronglyMeasurableAt_origin_probe

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_p286GaugeConnection_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0
      ).p286GaugeConnection =
      0 := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 = 0
  have coframeEq :
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.coframe =
        FixedLiveElectricCauchyCurrent.coframe := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent
  have connectionEq :
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gaugeConnection =
        FixedLiveElectricCauchyCurrent.gaugeConnection := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent
  have auxiliaryEq :
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gaugeAuxiliary =
        FixedLiveElectricCauchyCurrent.gaugeAuxiliary := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent
  have scalarEq :
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar =
        FixedLiveElectricCauchyCurrent.scalar := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent
  have matterEq :
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.matter =
        FixedLiveElectricCauchyCurrent.matter := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent
  have conjugateMatterEq :
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.conjugateMatter =
        FixedLiveElectricCauchyCurrent.conjugateMatter := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
        positiveSmoothUnifiedSource FixedLiveElectricCauchyCurrent
  have connectionCoordinateEq :
      holonomicP286GaugeConnectionCoordinate
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual =
        holonomicP286GaugeConnectionCoordinate
          FixedLiveElectricCauchyCurrent := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [connectionEq]
  have auxiliaryCoordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual =
        holonomicP286GaugeAuxiliaryCoordinate
          FixedLiveElectricCauchyCurrent := by
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [auxiliaryEq]
  have covariantDerivativeEq :
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          FixedLiveElectricCauchyCurrent 0 := by
    unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
      p286GaugeAuxiliaryDirectionalDerivative
      fieldDirectionalDerivative
    rw [connectionCoordinateEq, auxiliaryCoordinateEq]
  have scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0 =
        holonomicScalarCovariantDerivative
          FixedLiveElectricCauchyCurrent 0 := by
    unfold holonomicScalarCovariantDerivative fieldDirectionalDerivative
    rw [scalarEq, connectionEq]
  have chargedEq :
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual 0) =
        formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField FixedLiveElectricCauchyCurrent 0) := by
    apply formNativeChargedGaugeThreeForm_eq_of_pointActionData_eq
    · exact congrFun coframeEq 0
    · exact congrFun scalarEq 0
    · exact scalarCovariantDerivativeEq
    · exact congrFun matterEq 0
    · exact congrFun conjugateMatterEq 0
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [covariantDerivativeEq, chargedEq]
  exact
    fixedP506L0CompleteJointP286LiveElectricCauchyCurrent_connectionEquation_origin_noPremise

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginP286ConnectionClosure
