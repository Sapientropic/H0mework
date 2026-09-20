import H0mework.Physics.FixedJoint.FixedJointP286RequiredExteriorProfileRegularity
import H0mework.Physics.Jets.CanonicalTimePrimitiveMeasurableGermCalculus

/-!
# Fixed P506/L0 P286 required-profile measurable germ

This module builds a globally strongly measurable proof-side representative
for the fixed P506/L0 required P286 exterior-profile germ.  It combines the
same actual scalar, covariant scalar, matter, adjoint, connection, and
constitutive auxiliary action data.

The representative is never installed into the source or current and is not
a response, target field, branch, or equation receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286RequiredProfileMeasurableGerm

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
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointP286RequiredExteriorProfileRegularity
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
open StageNineCanonicalTimePrimitiveMeasurableGermCalculus
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
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

/-- The fixed full-occurrence matter action profile generates a temporal
primitive that is continuous on one spacetime neighborhood of the common
P506/L0 occurrence. -/
theorem
    fixedP506L0CompleteJointMatterTemporalPrimitive_contDiffAt_zero_origin :
    ContDiffAt ℝ 0
      (canonicalTimePrimitive
        (completeJointMatterTemporalCoordinateCorrection
          positiveSmoothUnifiedSource FixedInput))
      0 :=
  canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
    (completeJointMatterTemporalCoordinateCorrection
      positiveSmoothUnifiedSource FixedInput)
    (fixedP506L0FullOccurrenceMatterTemporalCoordinateCorrection_contDiffAt_origin.of_le
      (by norm_num))

/-- The same local primitive regularity holds for the independently generated
adjoint action profile; no global inverse-coframe branch is introduced. -/
theorem
    fixedP506L0CompleteJointAdjointTemporalPrimitive_contDiffAt_zero_origin :
    ContDiffAt ℝ 0
      (canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection
          positiveSmoothUnifiedSource FixedInput))
      0 :=
  canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
    (completeJointAdjointTemporalCoordinateCorrection
      positiveSmoothUnifiedSource FixedInput)
    (fixedP506L0FullOccurrenceAdjointTemporalCoordinateCorrection_contDiffAt_origin.of_le
      (by norm_num))

private theorem
    fixedP506L0CompleteJointScalarFirstPrimitive_contDiffAt_zero_origin :
    ContDiffAt ℝ 0
      (canonicalTimePrimitive
        (completeJointScalarAccelerationProfile
          positiveSmoothUnifiedSource FixedInput))
      0 :=
  canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
    (completeJointScalarAccelerationProfile
      positiveSmoothUnifiedSource FixedInput)
    (fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_origin.of_le
      (by norm_num))

/-- Iterating the local primitive theorem gives a genuine neighborhood
continuity statement for the fixed scalar second primitive. -/
theorem
    fixedP506L0CompleteJointScalarSecondPrimitive_contDiffAt_zero_origin :
    ContDiffAt ℝ 0
      (canonicalTimeSecondPrimitive
        (completeJointScalarAccelerationProfile
          positiveSmoothUnifiedSource FixedInput))
      0 := by
  have iteratedEq :
      canonicalTimeSecondPrimitive
        (completeJointScalarAccelerationProfile
          positiveSmoothUnifiedSource FixedInput) =
      canonicalTimePrimitive
        (canonicalTimePrimitive
          (completeJointScalarAccelerationProfile
            positiveSmoothUnifiedSource FixedInput)) := by
    funext point
    simp [canonicalTimeSecondPrimitive, canonicalTimePrimitive]
  rw [iteratedEq]
  exact
    canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
      (canonicalTimePrimitive
        (completeJointScalarAccelerationProfile
          positiveSmoothUnifiedSource FixedInput))
      fixedP506L0CompleteJointScalarFirstPrimitive_contDiffAt_zero_origin

private theorem fixedCanonicalConnectionActual_smooth_probe :
    FixedCanonicalConnectionActual.Smooth :=
  installP286HolonomicConnectionSecondJet_smooth FixedCanonicalInput
    (fixedP506L0FinalCommonActionActual_smooth 0)
    (p286CanonicalDiagonalResponseSecondJet
      fixedP506L0P286CanonicalGeneratedWrite) 1

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnectionCoordinate_stronglyMeasurable_probe :
    StronglyMeasurable
      (holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent) := by
  have coordinateEq :
      holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent =
      holonomicP286GaugeConnectionCoordinate
        FixedCanonicalConnectionActual := by
    funext point
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical,
      fixedP506L0P286CanonicalGeneratedActual_gaugeConnection]
  rw [coordinateEq]
  exact
    (holonomicP286GaugeConnectionCoordinate_contDiff
      FixedCanonicalConnectionActual
      fixedCanonicalConnectionActual_smooth_probe).continuous.stronglyMeasurable

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeAuxiliaryCoordinate_contDiffAt_zero_probe :
    ContDiffAt ℝ 0
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent) 0 := by
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical]
  change ContDiffAt ℝ 0
    (holonomicP286GaugeAuxiliaryCoordinate
      fixedP506L0P286CanonicalGeneratedActual) 0
  let domain : Set BasePoint :=
    { point |
      Matrix.det
          (fixedP506L0P286CanonicalGeneratedActual.coframe point) ≠
        0 }
  have coframeContinuous :
      Continuous fixedP506L0P286CanonicalGeneratedActual.coframe := by
    change Continuous FixedCanonicalInput.coframe
    exact
      (holonomicCoframe_contDiff FixedCanonicalInput
        (fixedP506L0FinalCommonActionActual_smooth 0)).continuous
  have domainOpen : IsOpen domain := by
    exact isOpen_ne_fun coframeContinuous.matrix_det continuous_const
  have zeroMem : (0 : BasePoint) ∈ domain := by
    dsimp [domain]
    rw [fixedP506L0P286CanonicalGeneratedActual_coframe_origin]
    norm_num
  rw [contDiffAt_zero]
  refine
    ⟨domain, domainOpen.mem_nhds zeroMem,
      continuousOn_of_forall_continuousAt ?_⟩
  intro point pointIn
  exact
    (fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_differentiableAt
      point pointIn).continuousAt

private theorem fieldDirectionalDerivative_measurable_probe
    {V : Type*}
    [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    [CompleteSpace V]
    [MeasurableSpace V]
    [BorelSpace V]
    (field : BasePoint → V)
    (direction : LorentzianIndex) :
    Measurable
      (fun point =>
        fieldDirectionalDerivative field point direction) := by
  unfold fieldDirectionalDerivative
  exact measurable_fderiv_apply_const ℝ field
    (coordinateDirection direction)

private theorem fixedInput_scalarDifferentialMomentumDivergence_measurable_probe
    (direction : ScalarCoordinateCarrier) :
    Measurable
      (scalarDifferentialMomentumDivergence
        positiveSmoothUnifiedSource FixedInput direction) := by
  unfold scalarDifferentialMomentumDivergence
  exact Finset.measurable_sum _ fun derivativeDirection _ =>
    fieldDirectionalDerivative_measurable_probe
      (scalarDifferentialMomentum positiveSmoothUnifiedSource FixedInput
        direction derivativeDirection)
      derivativeDirection

private theorem fixedInput_scalarAlgebraicKinetic_measurable_probe
    (direction : ScalarCoordinateCarrier) :
    Measurable fun point =>
      scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 point
        (toContinuumPointField FixedInput point)
        (holonomicScalarVariationAlgebraicDirection FixedInput direction
          point) := by
  have metricContinuous : Continuous fun point =>
      lorentzianMetricOfCoframe (FixedInput.coframe point) :=
    holonomicLorentzianMetric_continuous FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro first _
  apply Finset.measurable_sum
  intro second _
  have determinantInverseMeasurable : Measurable fun point =>
      (Matrix.det
        (lorentzianMetricOfCoframe (FixedInput.coframe point)))⁻¹ :=
    metricContinuous.matrix_det.measurable.inv
  have adjugateEntryMeasurable : Measurable fun point =>
      (lorentzianMetricOfCoframe
        (FixedInput.coframe point)).adjugate first second :=
    ((continuous_apply second).comp
      ((continuous_apply first).comp
        metricContinuous.matrix_adjugate)).measurable
  have metricEntryMeasurable : Measurable fun point =>
      (lorentzianMetricOfCoframe (FixedInput.coframe point))⁻¹
        first second := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul]
    change Measurable
      ((fun point =>
          (Matrix.det
            (lorentzianMetricOfCoframe (FixedInput.coframe point)))⁻¹) *
        fun point =>
          (lorentzianMetricOfCoframe
            (FixedInput.coframe point)).adjugate first second)
    exact determinantInverseMeasurable.mul adjugateEntryMeasurable
  have firstPairContinuous : Continuous fun point =>
      scalarCoordinatePairingRe
        (holonomicScalarVariationAlgebraicDirection FixedInput direction
          point first)
        (holonomicScalarCovariantDerivative FixedInput point second) :=
    scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarVariationAlgebraicDirection_continuous FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth direction first)
      (holonomicScalarCovariantDerivative_contDiff FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        second).continuous
  have secondPairContinuous : Continuous fun point =>
      scalarCoordinatePairingRe
        (holonomicScalarCovariantDerivative FixedInput point first)
        (holonomicScalarVariationAlgebraicDirection FixedInput direction
          point second) :=
    scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarCovariantDerivative_contDiff FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        first).continuous
      (holonomicScalarVariationAlgebraicDirection_continuous FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth direction second)
  exact metricEntryMeasurable.mul
    (firstPairContinuous.add secondPairContinuous).measurable

private theorem fixedInput_scalarEuler_measurable_probe
    (direction : ScalarCoordinateCarrier) :
    Measurable
      (diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction) := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  apply Measurable.sub
  · have coframeContinuous : Continuous FixedInput.coframe :=
      (holonomicCoframe_contDiff FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth).continuous
    have volumeMeasurable : Measurable fun point =>
        generatedVolumeDensity (toContinuumPointField FixedInput point) :=
      coframeContinuous.matrix_det.abs.measurable
    have potentialMeasurable : Measurable fun point =>
        scalarPotentialFirstVariation positiveSmoothUnifiedSource
          (toContinuumPointField FixedInput point) direction :=
      (scalarPotentialConstantDirection_continuous
        positiveSmoothUnifiedSource FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
        direction).measurable
    have yukawaMeasurable : Measurable fun point =>
        diracDualScalarYukawaFirstVariationDensity
          (toContinuumPointField FixedInput point) direction :=
      (diracDualScalarYukawaConstantDirectionDensity_continuous
        FixedInput fixedP506FormNativeJointActionSolvedSuccessor_smooth
        direction).measurable
    unfold diracDualScalarAlgebraicDirectionalCoefficient
    exact volumeMeasurable.mul
      ((fixedInput_scalarAlgebraicKinetic_measurable_probe direction).sub
        potentialMeasurable |>.add yukawaMeasurable)
  · exact
      fixedInput_scalarDifferentialMomentumDivergence_measurable_probe
        direction

private theorem genericRawTemporalDemand_eq_scalarEuler_origin_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    genericDiracDualScalarRawTemporalDemand source current direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction 0 := by
  unfold genericDiracDualScalarRawTemporalDemand
    genericDiracDualScalarRequiredPdot genericScalarCurrentPdot
    genericScalarSpatialMomentumDivergence
    diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  simp [Fin.sum_univ_four, Fin.sum_univ_three,
    canonicalLorentzianTimeDirection]
  ring

private theorem completeJointRepaired_matter_origin_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointRepairedConstitutiveCurrent source current).matter 0 =
      current.matter 0 := by
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]

private theorem completeJointRepaired_conjugateMatter_origin_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (completeJointRepairedConstitutiveCurrent source current
        ).conjugateMatter 0 =
      current.conjugateMatter 0 := by
  unfold completeJointRepairedConstitutiveCurrent
    diracDualFormNativeRepairedConstitutiveWrittenCurrent
    diracDualFormNativeRepairedMatterWrittenCurrent
    actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
  rfl

private theorem completeJointRepaired_scalarCovariantDerivative_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicScalarCovariantDerivative
        (completeJointRepairedConstitutiveCurrent source current) =
      holonomicScalarCovariantDerivative current := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [completeJointRepairedConstitutiveCurrent_gaugeConnection,
    completeJointRepairedConstitutiveCurrent_scalar]

private theorem completeJointRepaired_scalarMomentum_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (completeJointRepairedConstitutiveCurrent source current)
        direction derivativeDirection =
      scalarDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointRepairedConstitutiveCurrent_coframe,
    completeJointRepaired_scalarCovariantDerivative_eq_probe]

private theorem completeJointRepaired_scalarAlgebraic_origin_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (completeJointRepairedConstitutiveCurrent source current)
        direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient source current
        direction 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [completeJointRepairedConstitutiveCurrent_coframe,
    completeJointRepairedConstitutiveCurrent_gaugeConnection,
    completeJointRepairedConstitutiveCurrent_scalar,
    completeJointRepaired_scalarCovariantDerivative_eq_probe,
    completeJointRepaired_matter_origin_eq_probe,
    completeJointRepaired_conjugateMatter_origin_eq_probe]

private theorem completeJointRepaired_scalarEuler_origin_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (completeJointRepairedConstitutiveCurrent source current)
        direction 0 =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [completeJointRepaired_scalarAlgebraic_origin_eq_probe]
  simp_rw [completeJointRepaired_scalarMomentum_eq_probe]

private theorem cartanRestart_scalarCovariantDerivative_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) =
      holonomicScalarCovariantDerivative current := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]

private theorem cartanRestart_scalarMomentum_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        direction derivativeDirection =
      scalarDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    cartanRestart_scalarCovariantDerivative_eq_probe]

private theorem cartanRestart_scalarAlgebraic_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        direction =
      diracDualScalarAlgebraicDirectionalCoefficient source current
        direction := by
  funext point
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    cartanRestart_scalarCovariantDerivative_eq_probe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]

private theorem cartanRestart_scalarEuler_eq_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current)
        direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient source current
        direction := by
  funext point
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
    scalarDifferentialMomentumDivergence
  rw [congrFun
    (cartanRestart_scalarAlgebraic_eq_probe source current direction) point]
  simp_rw [cartanRestart_scalarMomentum_eq_probe]

private theorem fullOccurrenceRawTemporalDemand_eq_inputScalarEuler_probe
    (point : BasePoint)
    (direction : ScalarCoordinateCarrier) :
    genericDiracDualScalarRawTemporalDemand positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))
        direction =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction point := by
  rw [genericRawTemporalDemand_eq_scalarEuler_origin_probe,
    completeJointRepaired_scalarEuler_origin_eq_probe]
  unfold completeJointGeneratedProfileRestartCurrent
  rw [congrFun
    (cartanRestart_scalarEuler_eq_probe positiveSmoothUnifiedSource
      (fullyRecenterHolonomicConfiguration FixedInput point) direction) 0]
  have transported :=
    pointwiseJointResidual_fullyRecenter_origin positiveSmoothUnifiedSource
      FixedInput fixedP506FormNativeJointActionSolvedSuccessor_smooth point
  exact congrFun
    (congrArg
      StageNineDiracDualFormNativeJointResidualCarrier.DiracDualFormNativePointwiseJointResidualCarrier.scalar
      transported)
    direction

private theorem genericGeneratedAcceleration_eq_neg_coordinate_probe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    genericDiracDualScalarGeneratedAcceleration source current =
      -genericDiracDualScalarTemporalDemandCoordinate source current := by
  unfold genericDiracDualScalarGeneratedAcceleration scalarActionRealDual
  congr 1
  apply PiLp.ext
  intro index
  change
    ((genericDiracDualScalarTemporalDemandDual source current
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarTemporalDemandDual source current
          (scalarImaginaryBasis index) : ℂ) * Complex.I) =
    ((genericDiracDualScalarRawTemporalDemand source current
          (scalarRealBasis index) : ℂ) +
      (genericDiracDualScalarRawTemporalDemand source current
          (scalarImaginaryBasis index) : ℂ) * Complex.I)
  rw [genericDiracDualScalarTemporalDemandDual_realBasis,
    genericDiracDualScalarTemporalDemandDual_imaginaryBasis]

private theorem fullOccurrenceRawTemporalDemand_measurable_probe
    (direction : ScalarCoordinateCarrier) :
    Measurable fun point =>
      genericDiracDualScalarRawTemporalDemand positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))
        direction := by
  rw [show
    (fun point =>
      genericDiracDualScalarRawTemporalDemand positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))
        direction) =
      diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource FixedInput direction by
    funext point
    exact
      fullOccurrenceRawTemporalDemand_eq_inputScalarEuler_probe point
        direction]
  exact fixedInput_scalarEuler_measurable_probe direction

private theorem fullOccurrenceTemporalDemandCoordinate_measurable_probe :
    Measurable fun point =>
      genericDiracDualScalarTemporalDemandCoordinate
        positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point)) := by
  unfold genericDiracDualScalarTemporalDemandCoordinate
  apply (WithLp.measurable_toLp 2 (ScalarBasisIndex → ℂ)).comp
  apply measurable_pi_lambda
  intro index
  exact
    (Complex.measurable_ofReal.comp
      (fullOccurrenceRawTemporalDemand_measurable_probe
        (scalarRealBasis index))).add
      ((Complex.measurable_ofReal.comp
        (fullOccurrenceRawTemporalDemand_measurable_probe
          (scalarImaginaryBasis index))).mul_const Complex.I)

private theorem fixedP506L0CompleteJointScalarAccelerationProfile_measurable_probe :
    Measurable
      (completeJointScalarAccelerationProfile positiveSmoothUnifiedSource
        FixedInput) := by
  unfold completeJointScalarAccelerationProfile
  change Measurable fun point =>
    genericDiracDualScalarGeneratedAcceleration positiveSmoothUnifiedSource
      (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
        (completeJointGeneratedProfileRestartCurrent
          positiveSmoothUnifiedSource FixedInput point))
  rw [show
    (fun point =>
      genericDiracDualScalarGeneratedAcceleration positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput point))) =
      fun point =>
        -genericDiracDualScalarTemporalDemandCoordinate
          positiveSmoothUnifiedSource
          (completeJointRepairedConstitutiveCurrent
            positiveSmoothUnifiedSource
            (completeJointGeneratedProfileRestartCurrent
              positiveSmoothUnifiedSource FixedInput point)) by
    funext point
    exact genericGeneratedAcceleration_eq_neg_coordinate_probe _ _]
  exact fullOccurrenceTemporalDemandCoordinate_measurable_probe.neg

private theorem
    fixedP506L0CompleteJointScalarAccelerationProfile_stronglyMeasurable_probe :
    StronglyMeasurable
      (completeJointScalarAccelerationProfile positiveSmoothUnifiedSource
        FixedInput) :=
  fixedP506L0CompleteJointScalarAccelerationProfile_measurable_probe
    |>.stronglyMeasurable

private theorem continuous_real_matrix_inv_entry_measurable_probe
    {Domain Index : Type*}
    [TopologicalSpace Domain]
    [MeasurableSpace Domain]
    [BorelSpace Domain]
    [Fintype Index]
    [DecidableEq Index]
    (matrix : Domain → Matrix Index Index ℝ)
    (matrixContinuous : Continuous matrix)
    (row column : Index) :
    Measurable fun point => (matrix point)⁻¹ row column := by
  have determinantInverseMeasurable : Measurable fun point =>
      (Matrix.det (matrix point))⁻¹ :=
    matrixContinuous.matrix_det.measurable.inv
  have adjugateEntryMeasurable : Measurable fun point =>
      (matrix point).adjugate row column :=
    ((continuous_apply column).comp
      ((continuous_apply row).comp
        matrixContinuous.matrix_adjugate)).measurable
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul]
  change Measurable
    ((fun point => (Matrix.det (matrix point))⁻¹) *
      fun point => (matrix point).adjugate row column)
  exact determinantInverseMeasurable.mul adjugateEntryMeasurable

private theorem fixedInput_inverseCoframeDiracGamma_measurable_probe
    (direction : LorentzianIndex) :
    StronglyMeasurable fun point =>
      inverseCoframeDiracGamma
        { coframe := FixedInput.coframe point, derivative := 0 }
        direction := by
  unfold inverseCoframeDiracGamma
  have summandMeasurable (internal : LorentzianIndex) :
      StronglyMeasurable fun point =>
        ((FixedInput.coframe point)⁻¹ direction internal : ℂ) •
          diracGamma internal := by
    have inverseEntryMeasurable : Measurable fun point =>
        (FixedInput.coframe point)⁻¹ direction internal :=
      continuous_real_matrix_inv_entry_measurable_probe FixedInput.coframe
        (by
          apply continuous_pi
          intro row
          apply continuous_pi
          intro column
          exact
            (fixedP506FormNativeJointActionSolvedSuccessor_smooth.1
              row column).continuous)
        direction internal
    exact
      (Complex.measurable_ofReal.comp inverseEntryMeasurable
        |>.stronglyMeasurable).smul_const
        (diracGamma internal)
  rw [show
    (fun point =>
      ∑ internal,
        ((FixedInput.coframe point)⁻¹ direction internal : ℂ) •
          diracGamma internal) =
      ∑ internal, fun point =>
        ((FixedInput.coframe point)⁻¹ direction internal : ℂ) •
          diracGamma internal by
    funext point
    simp]
  exact
    Finset.stronglyMeasurable_sum Finset.univ fun internal _ =>
      summandMeasurable internal

private theorem
    fixedP506ActionDataSurrogate_chargedGaugeThreeForm_stronglyMeasurable_probe
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (scalarCovariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (matter conjugateMatter : BasePoint → MatterCoordinateCarrier)
    (scalarMeasurable : StronglyMeasurable scalar)
    (scalarCovariantDerivativeMeasurable :
      ∀ direction : LorentzianIndex,
        Measurable fun point =>
          scalarCovariantDerivative point direction)
    (matterMeasurable : StronglyMeasurable matter)
    (conjugateMatterMeasurable : StronglyMeasurable conjugateMatter) :
    StronglyMeasurable fun point =>
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (fixedP506ActionDataSurrogate scalar scalarCovariantDerivative
          matter conjugateMatter point) := by
  let basis := Module.finBasis ℝ P286GaugeOneForm
  let coordinates := fun point =>
    basis.dualBasis.equivFun
      (formNativeChargedGaugeFirstLinearMap positiveSmoothUnifiedSource 0
        point
        (fixedP506ActionDataSurrogate scalar scalarCovariantDerivative
          matter conjugateMatter point))
  have coefficientMeasurable (direction : P286GaugeOneForm) :
      Measurable fun point =>
        formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (fixedP506ActionDataSurrogate scalar scalarCovariantDerivative
            matter conjugateMatter point)
          direction := by
    unfold formNativeChargedGaugeFirstCoefficient
      generatedVolumeDensity
      scalarGaugeConnectionKineticFirstVariationDensity
      scalarFrameRelativeCovariantDerivative
      pointwiseScalarP286GaugeConnectionVariation
      pointwiseP286GaugeConnectionMotherVariation
      matterGaugeConnectionFirstVariationDensity
      matterGaugeConnectionVariationVector
      matterGaugeKineticSum
      matterDerivativeFrameRelative
      pointwiseMatterP286GaugeConnectionVariation
      fixedP506ActionDataSurrogate
    simp only [scalarFrameRelativeCoordinates_zeroChart,
      matterFrameRelative_zeroChart, matterDualFrameRelative_zeroChart]
    have coframeContinuous : Continuous FixedInput.coframe :=
      (holonomicCoframe_contDiff FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth).continuous
    have volumeMeasurable : Measurable fun point =>
        |Matrix.det (FixedInput.coframe point)| :=
      coframeContinuous.matrix_det.abs.measurable
    have metricContinuous : Continuous fun point =>
        lorentzianMetricOfCoframe (FixedInput.coframe point) :=
      holonomicLorentzianMetric_continuous FixedInput
        fixedP506FormNativeJointActionSolvedSuccessor_smooth
    have metricEntryMeasurable (first second : LorentzianIndex) :
        Measurable fun point =>
          (lorentzianMetricOfCoframe
              (FixedInput.coframe point))⁻¹ first second :=
      continuous_real_matrix_inv_entry_measurable_probe
        (fun point => lorentzianMetricOfCoframe (FixedInput.coframe point))
        metricContinuous first second
    have scalarActionMeasurable (formDirection : LorentzianIndex) :
        StronglyMeasurable fun point =>
          scalarMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (direction formDirection)))
            (scalar point) := by
      have actual :=
        StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
          |>.toContinuousBilinearMap
          |>.continuous₂
          |>.comp_stronglyMeasurable
            ((stronglyMeasurable_const :
              StronglyMeasurable fun _ : BasePoint =>
                direction formDirection).prodMk scalarMeasurable)
      exact actual
    have scalarDerivativeMeasurable (formDirection : LorentzianIndex) :
        StronglyMeasurable fun point =>
          scalarCovariantDerivative point formDirection :=
      (scalarCovariantDerivativeMeasurable formDirection).stronglyMeasurable
    have scalarPairingMeasurable
        (first second : BasePoint → ScalarCoordinateCarrier)
        (firstMeasurable : StronglyMeasurable first)
        (secondMeasurable : StronglyMeasurable second) :
        Measurable fun point =>
          scalarCoordinatePairingRe (first point) (second point) := by
      exact
        (StageNineP286GaugeConnectionVariationDensity.scalarCoordinatePairingReBilinear
          |>.toContinuousBilinearMap
          |>.continuous₂
          |>.comp_stronglyMeasurable
            (firstMeasurable.prodMk secondMeasurable)).measurable
    have scalarDensityMeasurable : Measurable fun point =>
        (1 / 2 : ℝ) *
          ∑ first : LorentzianIndex,
            ∑ second : LorentzianIndex,
              (lorentzianMetricOfCoframe
                    (FixedInput.coframe point))⁻¹ first second *
                (scalarCoordinatePairingRe
                    (scalarMotherLieAction
                      (p286LieBlockEmbed
                        (p286CoordinateEquiv.symm (direction first)))
                      (scalar point))
                    (scalarCovariantDerivative point second) +
                  scalarCoordinatePairingRe
                    (scalarCovariantDerivative point first)
                    (scalarMotherLieAction
                      (p286LieBlockEmbed
                        (p286CoordinateEquiv.symm (direction second)))
                      (scalar point))) := by
      apply measurable_const.mul
      apply Finset.measurable_sum
      intro first _
      apply Finset.measurable_sum
      intro second _
      exact
        (metricEntryMeasurable first second).mul
          ((scalarPairingMeasurable _ _
              (scalarActionMeasurable first)
              (scalarDerivativeMeasurable second)).add
            (scalarPairingMeasurable _ _
              (scalarDerivativeMeasurable first)
              (scalarActionMeasurable second)))
    have matterVariationMeasurable (formDirection : LorentzianIndex) :
        StronglyMeasurable fun point =>
          matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (pointwiseP286GaugeConnectionMotherVariation
                direction formDirection)
              (matterCoordinateEquiv.symm (matter point))) := by
      have actual :=
        StageNineP286GaugeConnectionVariationDensity.matterP286ActionCoordinateBilinear
          |>.toContinuousBilinearMap
          |>.continuous₂
          |>.comp_stronglyMeasurable
            ((stronglyMeasurable_const :
              StronglyMeasurable fun _ : BasePoint =>
                direction formDirection).prodMk matterMeasurable)
      exact actual
    have matterKineticMeasurable (formDirection : LorentzianIndex) :
        StronglyMeasurable fun point =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := FixedInput.coframe point, derivative := 0 }
                formDirection)
              (diracExteriorMotherLieAction
                (pointwiseP286GaugeConnectionMotherVariation
                  direction formDirection)
                (matterCoordinateEquiv.symm (matter point)))) := by
      have actual :=
        diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap
          |>.continuous₂
          |>.comp_stronglyMeasurable
            ((fixedInput_inverseCoframeDiracGamma_measurable_probe
              formDirection).prodMk
              (matterVariationMeasurable formDirection))
      change StronglyMeasurable fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := FixedInput.coframe point, derivative := 0 }
              formDirection)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (diracExteriorMotherLieAction
                  (pointwiseP286GaugeConnectionMotherVariation
                    direction formDirection)
                  (matterCoordinateEquiv.symm (matter point)))))) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    let kineticCoordinate
        (formDirection : LorentzianIndex)
        (point : BasePoint) : MatterCoordinateCarrier :=
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := FixedInput.coframe point, derivative := 0 }
            formDirection)
          (diracExteriorMotherLieAction
            (pointwiseP286GaugeConnectionMotherVariation
              direction formDirection)
            (matterCoordinateEquiv.symm (matter point))))
    have kineticCoordinateMeasurable (formDirection : LorentzianIndex) :
        StronglyMeasurable (kineticCoordinate formDirection) := by
      simpa only [kineticCoordinate] using
        matterKineticMeasurable formDirection
    let matterVector : BasePoint → DiracExteriorMatterCarrier :=
      fun point =>
        Complex.I •
          ∑ formDirection : LorentzianIndex,
            diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := FixedInput.coframe point, derivative := 0 }
                formDirection)
              (diracExteriorMotherLieAction
                (pointwiseP286GaugeConnectionMotherVariation
                  direction formDirection)
                (matterCoordinateEquiv.symm (matter point)))
    let matterVectorCoordinates : BasePoint → MatterCoordinateCarrier :=
      fun point => matterCoordinateEquiv (matterVector point)
    have matterVectorCoordinatesMeasurable :
        StronglyMeasurable matterVectorCoordinates := by
      have kineticFunctionSumMeasurable :
          StronglyMeasurable
            (∑ formDirection : LorentzianIndex,
              kineticCoordinate formDirection) := by
        exact Finset.stronglyMeasurable_sum Finset.univ
          fun formDirection _ => kineticCoordinateMeasurable formDirection
      have kineticPointwiseSumMeasurable :
          StronglyMeasurable fun point =>
            ∑ formDirection : LorentzianIndex,
              kineticCoordinate formDirection point := by
        have pointwiseEq :
            (fun point =>
              ∑ formDirection : LorentzianIndex,
                kineticCoordinate formDirection point) =
              ∑ formDirection : LorentzianIndex,
                kineticCoordinate formDirection := by
          funext point
          simp
        rw [pointwiseEq]
        exact kineticFunctionSumMeasurable
      have coordinateEq : matterVectorCoordinates =
          fun point =>
            Complex.I •
              ∑ formDirection : LorentzianIndex,
                kineticCoordinate formDirection point := by
        funext point
        simp [matterVectorCoordinates, matterVector, kineticCoordinate,
          map_smul, map_sum]
      rw [coordinateEq]
      exact
        (stronglyMeasurable_const :
          StronglyMeasurable fun _ : BasePoint => Complex.I).smul
          kineticPointwiseSumMeasurable
    have matterDensityMeasurable :
        Measurable fun point =>
          ((matterDualOfCoordinates (conjugateMatter point))
            (matterVector point)).re := by
      have densityEq :
        (fun point =>
          ((matterDualOfCoordinates (conjugateMatter point))
            (matterVector point)).re) =
        fun point =>
          (∑ index : MatterCoordinateIndex,
            matterCoordinateEquiv (matterVector point) index *
              conjugateMatter point index).re := by
        funext point
        rw [matterDualOfCoordinates_apply]
      rw [densityEq]
      apply Complex.measurable_re.comp
      apply Finset.measurable_sum
      intro index _
      exact
        ((PiLp.continuous_apply 2
            (fun _ : MatterCoordinateIndex => ℂ) index
          ).stronglyMeasurable.comp_measurable
            matterVectorCoordinatesMeasurable.measurable
          |>.measurable).mul
        ((PiLp.continuous_apply 2
            (fun _ : MatterCoordinateIndex => ℂ) index
          ).stronglyMeasurable.comp_measurable
            conjugateMatterMeasurable.measurable
          |>.measurable)
    change Measurable fun point =>
      |Matrix.det (FixedInput.coframe point)| *
        (_ +
          ((matterDualOfCoordinates (conjugateMatter point))
            (matterVector point)).re)
    exact volumeMeasurable.mul
      (scalarDensityMeasurable.add matterDensityMeasurable)
  have coordinatesMeasurable : Measurable coordinates := by
    apply measurable_pi_lambda
    intro index
    rw [show (fun point => coordinates point index) =
      fun point =>
        formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (fixedP506ActionDataSurrogate scalar scalarCovariantDerivative
            matter conjugateMatter point)
          (basis index) by
      funext point
      exact basis.dualBasis_equivFun _ index]
    exact coefficientMeasurable (basis index)
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286GaugeThreeFormWedgeEquiv.symm
  let reconstructCLM :
      (Fin (Module.finrank ℝ P286GaugeOneForm) → ℝ) →L[ℝ]
        P286GaugeThreeForm :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  have reconstructedMeasurable : StronglyMeasurable fun point =>
      reconstructCLM (coordinates point) :=
    reconstructCLM.continuous.stronglyMeasurable.comp_measurable
      coordinatesMeasurable
  have reconstructedEq :
    (fun point =>
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (fixedP506ActionDataSurrogate scalar scalarCovariantDerivative
          matter conjugateMatter point)) =
      fun point => reconstructCLM (coordinates point) := by
    funext point
    change
      p286GaugeThreeFormWedgeEquiv.symm
          (formNativeChargedGaugeFirstLinearMap positiveSmoothUnifiedSource 0
            point
            (fixedP506ActionDataSurrogate scalar scalarCovariantDerivative
              matter conjugateMatter point)) =
        reconstruct (coordinates point)
    unfold reconstruct coordinates
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [reconstructedEq]
  exact reconstructedMeasurable

private theorem
    fixedP506L0CompleteJointScalarSecondPrimitive_stronglyMeasurable_probe :
    StronglyMeasurable FixedScalarSecondPrimitive :=
  canonicalTimeSecondPrimitive_stronglyMeasurable_of_stronglyMeasurable
    (completeJointScalarAccelerationProfile
      positiveSmoothUnifiedSource FixedInput)
    fixedP506L0CompleteJointScalarAccelerationProfile_stronglyMeasurable_probe

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_stronglyMeasurable_probe :
    StronglyMeasurable FixedAlgebraicCurrent.scalar := by
  rw [show FixedAlgebraicCurrent.scalar =
      fun point => FixedInput.scalar point +
        FixedScalarSecondPrimitive point by
    funext point
    rfl]
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).2.2.2.2.2.2.1.continuous.stronglyMeasurable.add
        fixedP506L0CompleteJointScalarSecondPrimitive_stronglyMeasurable_probe

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnectionCoordinate_direction_stronglyMeasurable_probe
    (direction : LorentzianIndex) :
    StronglyMeasurable fun point =>
      holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent point
        direction :=
  (continuous_apply direction).stronglyMeasurable.comp_measurable
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnectionCoordinate_stronglyMeasurable_probe.measurable

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCoordinateAction_coordinate_stronglyMeasurable_probe
    (direction : LorentzianIndex) :
    StronglyMeasurable fun point =>
      StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          FixedAlgebraicCurrent point direction)
        (FixedAlgebraicCurrent.scalar point) := by
  let action :=
    StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
      |>.toContinuousBilinearMap
  have operatorMeasurable :
      StronglyMeasurable fun point =>
        action
          (holonomicP286GaugeConnectionCoordinate
            FixedAlgebraicCurrent point direction) :=
    action.continuous.comp_stronglyMeasurable
      (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnectionCoordinate_direction_stronglyMeasurable_probe
        direction)
  exact
    isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      (operatorMeasurable.prodMk
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_stronglyMeasurable_probe)

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarGaugeAction_coordinate_stronglyMeasurable_probe
    (direction : LorentzianIndex) :
    StronglyMeasurable fun point =>
      scalarMotherLieAction
        (p286LieBlockEmbed
          (FixedAlgebraicCurrent.gaugeConnection point direction))
        (FixedAlgebraicCurrent.scalar point) := by
  have actionEq :
      (fun point =>
        scalarMotherLieAction
          (p286LieBlockEmbed
            (FixedAlgebraicCurrent.gaugeConnection point direction))
          (FixedAlgebraicCurrent.scalar point)) =
        fun point =>
          StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear
            (holonomicP286GaugeConnectionCoordinate
              FixedAlgebraicCurrent point direction)
            (FixedAlgebraicCurrent.scalar point) := by
    funext point
    unfold holonomicP286GaugeConnectionCoordinate
    change
      scalarMotherLieAction
          (p286LieBlockEmbed
            (FixedAlgebraicCurrent.gaugeConnection point direction))
          (FixedAlgebraicCurrent.scalar point) =
        scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (FixedAlgebraicCurrent.gaugeConnection point direction))))
          (FixedAlgebraicCurrent.scalar point)
    rw [p286CoordinateEquiv.symm_apply_apply]
  rw [actionEq]
  exact
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCoordinateAction_coordinate_stronglyMeasurable_probe
      direction

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_coordinate_measurable_probe
    (direction : LorentzianIndex) :
    Measurable fun point =>
      holonomicScalarCovariantDerivative FixedAlgebraicCurrent point
        direction := by
  have derivativeMeasurable :
      Measurable fun point =>
        fieldDirectionalDerivative FixedAlgebraicCurrent.scalar point
          direction :=
    fieldDirectionalDerivative_measurable_probe
      FixedAlgebraicCurrent.scalar direction
  unfold holonomicScalarCovariantDerivative
  exact derivativeMeasurable.add
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarGaugeAction_coordinate_stronglyMeasurable_probe
      direction).measurable

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterCoordinate_contDiffAt_zero_probe :
    ContDiffAt ℝ 0
      (fun point =>
        matterCoordinateEquiv (FixedAlgebraicCurrent.matter point)) 0 := by
  have matterEq :
      (fun point =>
        matterCoordinateEquiv (FixedAlgebraicCurrent.matter point)) =
      (fun point => matterCoordinateEquiv (FixedInput.matter point)) +
        FixedMatterTemporalPrimitive := by
    funext point
    change
      matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            positiveSmoothUnifiedSource FixedInput).matter point) =
        matterCoordinateEquiv (FixedInput.matter point) +
          FixedMatterTemporalPrimitive point
    simp [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]
  rw [matterEq]
  exact
    ((fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).2.2.2.2.2.2.2.1.contDiffAt.of_le (by norm_num)).add
      fixedP506L0CompleteJointMatterTemporalPrimitive_contDiffAt_zero_origin

private theorem
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatterCoordinates_contDiffAt_zero_probe :
    ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates FixedAlgebraicCurrent) 0 := by
  have conjugateMatterEq :
      holonomicConjugateMatterCoordinates FixedAlgebraicCurrent =
        holonomicConjugateMatterCoordinates FixedInput +
          FixedAdjointTemporalPrimitive := by
    funext point
    change
      matterDualCoordinates
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            positiveSmoothUnifiedSource FixedInput).conjugateMatter point) =
        matterDualCoordinates (FixedInput.conjugateMatter point) +
          FixedAdjointTemporalPrimitive point
    simp [sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
      matterDualCoordinates_add]
  rw [conjugateMatterEq]
  exact
    ((holonomicConjugateMatterCoordinates_contDiff FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).contDiffAt.of_le (by norm_num)).add
      fixedP506L0CompleteJointAdjointTemporalPrimitive_contDiffAt_zero_origin

theorem formNativeChargedGaugeThreeForm_eq_of_pointActionData_eq
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (first second : StageNineContinuumPointField)
    (coframeEq : first.coframe = second.coframe)
    (scalarEq : first.scalar = second.scalar)
    (scalarCovariantDerivativeEq :
      first.scalarCovariantDerivative =
        second.scalarCovariantDerivative)
    (matterEq : first.matter = second.matter)
    (conjugateMatterEq :
      first.conjugateMatter = second.conjugateMatter) :
    formNativeChargedGaugeThreeForm source 0 point first =
      formNativeChargedGaugeThreeForm source 0 point second := by
  have volumeEq :
      generatedVolumeDensity first = generatedVolumeDensity second := by
    unfold generatedVolumeDensity
    rw [coframeEq]
  have scalarKineticEq
      (variation : LorentzianIndex → ScalarCoordinateCarrier) :
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
          first variation =
        scalarGaugeConnectionKineticFirstVariationDensity source 0 point
          second variation := by
    unfold scalarGaugeConnectionKineticFirstVariationDensity
    rw [coframeEq, scalarCovariantDerivativeEq]
  have scalarVariationEq (direction : P286GaugeOneForm) :
      pointwiseScalarP286GaugeConnectionVariation first direction =
        pointwiseScalarP286GaugeConnectionVariation second direction := by
    funext formDirection
    unfold pointwiseScalarP286GaugeConnectionVariation
    rw [scalarEq]
  have matterVariationEq (direction : P286GaugeOneForm) :
      pointwiseMatterP286GaugeConnectionVariation first direction =
        pointwiseMatterP286GaugeConnectionVariation second direction := by
    funext formDirection
    unfold pointwiseMatterP286GaugeConnectionVariation
    rw [matterEq]
  have matterKineticEq
      (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
      matterGaugeConnectionFirstVariationDensity source 0 point
          first variation =
        matterGaugeConnectionFirstVariationDensity source 0 point
          second variation := by
    unfold matterGaugeConnectionFirstVariationDensity
      matterGaugeConnectionVariationVector matterGaugeKineticSum
    rw [coframeEq, conjugateMatterEq]
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  simp only [formNativeChargedGaugeFirstLinearMap_apply]
  unfold formNativeChargedGaugeFirstCoefficient
  rw [volumeEq, scalarVariationEq, matterVariationEq,
    scalarKineticEq, matterKineticEq]

private def p286ConnectionExteriorActionBilinear :
    P286GaugeOneForm →ₗ[ℝ]
      P286GaugeTwoForm →ₗ[ℝ] P286GaugeThreeForm where
  toFun connection :=
    { toFun := fun auxiliary =>
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          connection auxiliary
      map_add' := by
        intro first second
        funext triple
        simp [pointwiseP286GaugeTwoFormConnectionExteriorAction,
          pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
          pointwiseP286GaugeTwoFormCovariantDerivative,
          p286GaugeTwoFormAdjoint,
          orderedP286GaugeTwoFormComponent,
          p286CoordinateLieBracket_add_right]
        simp only [Finset.sum_add_distrib]
        module
      map_smul' := by
        intro parameter auxiliary
        funext triple
        simp [pointwiseP286GaugeTwoFormConnectionExteriorAction,
          pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
          pointwiseP286GaugeTwoFormCovariantDerivative,
          p286GaugeTwoFormAdjoint,
          orderedP286GaugeTwoFormComponent,
          p286CoordinateLieBracket_smul_right,
          smul_add]
        simp [Finset.smul_sum, smul_smul, mul_comm] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro auxiliary
    funext triple
    simp [pointwiseP286GaugeTwoFormConnectionExteriorAction,
      pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
      pointwiseP286GaugeTwoFormCovariantDerivative,
      p286GaugeTwoFormAdjoint,
      orderedP286GaugeTwoFormComponent,
      p286CoordinateLieBracket_add_left]
    simp only [Finset.sum_add_distrib]
    module
  map_smul' := by
    intro parameter connection
    apply LinearMap.ext
    intro auxiliary
    funext triple
    simp [pointwiseP286GaugeTwoFormConnectionExteriorAction,
      pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
      pointwiseP286GaugeTwoFormCovariantDerivative,
      p286GaugeTwoFormAdjoint,
      orderedP286GaugeTwoFormComponent,
      p286CoordinateLieBracket_smul_left,
      smul_add]
    simp [Finset.smul_sum, smul_smul, mul_comm]

private theorem p286ConnectionExteriorAction_stronglyMeasurable
    (connection : BasePoint → P286GaugeOneForm)
    (auxiliary : BasePoint → P286GaugeTwoForm)
    (connectionMeasurable : StronglyMeasurable connection)
    (auxiliaryMeasurable : StronglyMeasurable auxiliary) :
    StronglyMeasurable fun point =>
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (connection point) (auxiliary point) := by
  let action := p286ConnectionExteriorActionBilinear.toContinuousBilinearMap
  have operatorMeasurable :
      StronglyMeasurable fun point => action (connection point) :=
    action.continuous.comp_stronglyMeasurable connectionMeasurable
  exact
    isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      (operatorMeasurable.prodMk auxiliaryMeasurable)

theorem
    exists_fixedP506L0CompleteJointP286RequiredExteriorProfile_stronglyMeasurable_germ :
    ∃ representative : BasePoint → P286GaugeThreeForm,
      StronglyMeasurable representative ∧
      completeJointP286RequiredExteriorProfile positiveSmoothUnifiedSource
          FixedAlgebraicCurrent =ᶠ[𝓝 0]
        representative := by
  obtain ⟨matterRepresentative, matterRepresentativeMeasurable,
      matterRepresentativeEventuallyEq⟩ :=
    exists_stronglyMeasurable_eventuallyEq_of_contDiffAt_zero
      (fun point =>
        matterCoordinateEquiv (FixedAlgebraicCurrent.matter point))
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matterCoordinate_contDiffAt_zero_probe
  obtain ⟨conjugateMatterRepresentative,
      conjugateMatterRepresentativeMeasurable,
      conjugateMatterRepresentativeEventuallyEq⟩ :=
    exists_stronglyMeasurable_eventuallyEq_of_contDiffAt_zero
      (holonomicConjugateMatterCoordinates FixedAlgebraicCurrent)
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatterCoordinates_contDiffAt_zero_probe
  obtain ⟨auxiliaryRepresentative, auxiliaryRepresentativeMeasurable,
      auxiliaryRepresentativeEventuallyEq⟩ :=
    exists_stronglyMeasurable_eventuallyEq_of_contDiffAt_zero
      (holonomicP286GaugeAuxiliaryCoordinate FixedAlgebraicCurrent)
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeAuxiliaryCoordinate_contDiffAt_zero_probe
  let chargedRepresentative : BasePoint → P286GaugeThreeForm :=
    fun point =>
      -formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (fixedP506ActionDataSurrogate FixedAlgebraicCurrent.scalar
          (holonomicScalarCovariantDerivative FixedAlgebraicCurrent)
          matterRepresentative conjugateMatterRepresentative point)
  let connectionRepresentative : BasePoint → P286GaugeThreeForm :=
    fun point =>
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent point)
        (auxiliaryRepresentative point)
  let representative : BasePoint → P286GaugeThreeForm :=
    fun point =>
      chargedRepresentative point - connectionRepresentative point
  have chargedRepresentativeMeasurable :
      StronglyMeasurable chargedRepresentative := by
    exact
      (fixedP506ActionDataSurrogate_chargedGaugeThreeForm_stronglyMeasurable_probe
        FixedAlgebraicCurrent.scalar
        (holonomicScalarCovariantDerivative FixedAlgebraicCurrent)
        matterRepresentative conjugateMatterRepresentative
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_stronglyMeasurable_probe
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_coordinate_measurable_probe
        matterRepresentativeMeasurable
        conjugateMatterRepresentativeMeasurable).neg
  have connectionRepresentativeMeasurable :
      StronglyMeasurable connectionRepresentative :=
    p286ConnectionExteriorAction_stronglyMeasurable
      (holonomicP286GaugeConnectionCoordinate FixedAlgebraicCurrent)
      auxiliaryRepresentative
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnectionCoordinate_stronglyMeasurable_probe
      auxiliaryRepresentativeMeasurable
  refine
    ⟨representative,
      chargedRepresentativeMeasurable.sub
        connectionRepresentativeMeasurable, ?_⟩
  filter_upwards [matterRepresentativeEventuallyEq,
      conjugateMatterRepresentativeEventuallyEq,
      auxiliaryRepresentativeEventuallyEq] with point matterEq
      conjugateMatterEq auxiliaryEq
  have matterFieldEq :
      FixedAlgebraicCurrent.matter point =
        matterCoordinateEquiv.symm (matterRepresentative point) := by
    apply matterCoordinateEquiv.injective
    simpa using matterEq
  have conjugateMatterFieldEq :
      FixedAlgebraicCurrent.conjugateMatter point =
        matterDualOfCoordinates (conjugateMatterRepresentative point) := by
    have coordinatesEq :
        matterDualCoordinates
            (FixedAlgebraicCurrent.conjugateMatter point) =
          conjugateMatterRepresentative point := by
      simpa [holonomicConjugateMatterCoordinates] using conjugateMatterEq
    calc
      FixedAlgebraicCurrent.conjugateMatter point =
          matterDualOfCoordinates
            (matterDualCoordinates
              (FixedAlgebraicCurrent.conjugateMatter point)) := by
        exact
          (matterDualOfCoordinates_surjective
            (FixedAlgebraicCurrent.conjugateMatter point)).symm
      _ =
          matterDualOfCoordinates
            (conjugateMatterRepresentative point) := by
        rw [coordinatesEq]
  have chargedEq :
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
          (toContinuumPointField FixedAlgebraicCurrent point) =
        formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
          (fixedP506ActionDataSurrogate FixedAlgebraicCurrent.scalar
            (holonomicScalarCovariantDerivative FixedAlgebraicCurrent)
            matterRepresentative conjugateMatterRepresentative point) := by
    apply formNativeChargedGaugeThreeForm_eq_of_pointActionData_eq
    · rfl
    · rfl
    · rfl
    · exact matterFieldEq
    · exact conjugateMatterFieldEq
  rw [
    completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
      positiveSmoothUnifiedSource FixedAlgebraicCurrent point
      (completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
        positiveSmoothUnifiedSource FixedInput point)]
  unfold pointwiseDirectP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm representative
    chargedRepresentative connectionRepresentative
  rw [chargedEq, auxiliaryEq]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286RequiredProfileMeasurableGerm
