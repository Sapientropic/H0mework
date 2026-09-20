import H0mework.Physics.FullOccurrence.FixedWriterPreECCongruence
import H0mework.Physics.Cauchy.CanonicalCauchyCoordinateProjection
import H0mework.Physics.ElectricEC.FixedTemporalScalarAmbientFirstJetRegularity
import H0mework.Physics.JointVariation.P286OccurrenceSecondJetGlobalInstallationBoundary
import H0mework.Physics.ScalarJets.FixedJointScalarSegmentRegularity
import H0mework.Physics.FixedJoint.FixedJointP286AlgebraicConnectionChangedRead
import H0mework.Physics.ActionForcing.FixedOccurrenceP286ZeroSliceActionProfile
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Fixed U6 occurrence matching-action-forcing bridge

This module isolates the producer-authority seam behind the fixed
P506/L0 occurrence P286 write.  It uses no residual coordinate, support
witness, or Euler zero receipt.

Five of the six action-data inputs are forced by the existing U5
field-preservation chain and by the canonical temporal primitives vanishing
at the recentered origin.  The general bridge isolates the remaining scalar
covariant first-jet identification; the fixed zero-slice specialization then
discharges it from the same mother-action temporal producer and identifies the
occurrence forcing with the matching global algebraic Euler form.

The resulting fixed U6 write is the radial-quadratic temporal profile selected
by the mother action.  The already generated radial-quartic global connection
has an actual Hessian whose response realizes this forcing.  No residual
coordinate, support witness, target jet, or zero-fiber receipt is consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ActionForcingBridge

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalWriterPreECCongruence
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECTemporalScalarAmbientFirstJetRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicConnectionChangedRead
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeCompleteJointP286OccurrenceSecondJetGlobalInstallationBoundary
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineP286GaugeConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286SpatialVolumeTemporalActionDuality
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev RecenteredU5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration U5 contact

private abbrev OccurrenceTemporal (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source (RecenteredU5 contact)

private abbrev RecenteredTemporal (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Temporal contact

/-! ## All-point action-owned forcing carrier -/

/-- The canonical occurrence with the same spatial coordinates and zero
canonical time.  It is fixed by the spacetime chart, not supplied as a
boundary datum. -/
def fixedP506L0P286ZeroTimeProjection (point : BasePoint) : BasePoint :=
  canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)

@[simp] theorem fixedP506L0P286ZeroTimeProjection_slice
    (time : ℝ) (space : StageNineSpatialPoint) :
    fixedP506L0P286ZeroTimeProjection
        (canonicalCauchySlicePoint time space) =
      canonicalCauchySlicePoint 0 space := by
  simp [fixedP506L0P286ZeroTimeProjection]

/-- The complete action-owned temporal support of the fixed Algebraic Euler
field relative to the same spatial occurrence.  This is a readout carrier;
it is never fed into a field constructor. -/
def fixedP506L0AlgebraicActionEulerTimeCorrection
    (point : BasePoint) : P286GaugeThreeForm :=
  holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point -
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
      (fixedP506L0P286ZeroTimeProjection point)

/-- Primitive-field expansion of the temporal support: exactly the canonical
`D_A B` change plus the same-source Temporal charged-current change. -/
def fixedP506L0AlgebraicCanonicalTemporalTimeCorrection
    (point : BasePoint) : P286GaugeThreeForm :=
  (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        fixedP506L0P286CanonicalGeneratedActual point -
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        fixedP506L0P286CanonicalGeneratedActual
        (fixedP506L0P286ZeroTimeProjection point)) +
    (formNativeChargedGaugeThreeForm Source 0 point
          (toContinuumPointField Temporal point) -
      formNativeChargedGaugeThreeForm Source 0
        (fixedP506L0P286ZeroTimeProjection point)
        (toContinuumPointField Temporal
          (fixedP506L0P286ZeroTimeProjection point)))

theorem fixedP506L0AlgebraicActionEulerTimeCorrection_eq_primitiveFields
    (point : BasePoint) :
    fixedP506L0AlgebraicActionEulerTimeCorrection point =
      fixedP506L0AlgebraicCanonicalTemporalTimeCorrection point := by
  unfold fixedP506L0AlgebraicActionEulerTimeCorrection
    fixedP506L0AlgebraicCanonicalTemporalTimeCorrection
  rw [
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_eq_canonicalExterior_add_temporalCharged,
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eulerThreeForm_eq_canonicalExterior_add_temporalCharged]
  abel_nf

@[simp] theorem fixedP506L0AlgebraicActionEulerTimeCorrection_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0AlgebraicActionEulerTimeCorrection
        (canonicalCauchySlicePoint 0 space) = 0 := by
  simp [fixedP506L0AlgebraicActionEulerTimeCorrection]

/-- Canonical-time extension of the action-generated radial zero-slice
profile. -/
def fixedP506L0RadialActionEulerField
    (point : BasePoint) : P286GaugeThreeForm :=
  p286SpatialRadiusSquared point •
    p286SpatialVolumeGaugeThreeForm
      fixedP506L0U6OccurrenceP286MotherActionCharge

private theorem p286SpatialRadiusSquared_zeroTimeProjection
    (point : BasePoint) :
    p286SpatialRadiusSquared (fixedP506L0P286ZeroTimeProjection point) =
      p286SpatialRadiusSquared point := by
  simp [p286SpatialRadiusSquared, p286SpatialMetricCovectorOperator,
    fixedP506L0P286ZeroTimeProjection, canonicalCauchySlicePoint,
    canonicalSpatialProjection, canonicalLorentzianTimeDirection,
    p286BaseCoordinate_apply, localBaseCoordinate_apply,
    Fin.sum_univ_three]

/-- Complete all-point Algebraic Euler normal form.  The first summand is
the already generated radial zero-slice action profile; the second is the
exhaustive temporal support defined above from the same Algebraic action
field. -/
theorem fixedP506L0_Algebraic_p286Euler_eq_radial_add_timeCorrection
    (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point =
      fixedP506L0RadialActionEulerField point +
        fixedP506L0AlgebraicActionEulerTimeCorrection point := by
  have zeroTimeProfile :
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (fixedP506L0P286ZeroTimeProjection point) =
        fixedP506L0RadialActionEulerField point := by
    rw [show fixedP506L0P286ZeroTimeProjection point =
        canonicalCauchySlicePoint 0 (canonicalSpatialProjection point) by
      rfl]
    rw [fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm]
    unfold fixedP506L0RadialActionEulerField
    rw [show
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point) =
        fixedP506L0P286ZeroTimeProjection point by rfl,
      p286SpatialRadiusSquared_zeroTimeProjection]
  unfold fixedP506L0AlgebraicActionEulerTimeCorrection
  rw [zeroTimeProfile]
  abel

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem algebraic_eq_zeroCandidate :
    Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source Temporal 0 :=
  fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate

private theorem u5_coframe_eq_temporal :
    U5.coframe = Temporal.coframe := by
  calc
    U5.coframe =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.coframe :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC
    _ = Algebraic.coframe :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
        Source FixedInput
    _ = Temporal.coframe := by
      rw [algebraic_eq_zeroCandidate]
      rfl

private theorem u5_gaugeConnection_eq_temporal :
    U5.gaugeConnection = Temporal.gaugeConnection := by
  calc
    U5.gaugeConnection =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gaugeConnection :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC
    _ = Algebraic.gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
        Source FixedInput
    _ = Temporal.gaugeConnection := by
      rw [algebraic_eq_zeroCandidate,
        diracDualFormNativeP286CanonicalJointCandidate,
        diracDualFormNativeP286CanonicalConnectionCandidate_zero]
      rfl

private theorem u5_scalar_eq_temporal :
    U5.scalar = Temporal.scalar := by
  calc
    U5.scalar =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC
    _ = Algebraic.scalar :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
        Source FixedInput
    _ = Temporal.scalar := by
      rw [algebraic_eq_zeroCandidate]
      rfl

private theorem u5_matter_eq_temporal :
    U5.matter = Temporal.matter := by
  calc
    U5.matter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.matter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC
    _ = Algebraic.matter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
        Source FixedInput
    _ = Temporal.matter := by
      rw [algebraic_eq_zeroCandidate]
      rfl

private theorem u5_conjugateMatter_eq_temporal :
    U5.conjugateMatter = Temporal.conjugateMatter := by
  calc
    U5.conjugateMatter =
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.conjugateMatter :=
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC
    _ = Algebraic.conjugateMatter :=
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
        Source FixedInput
    _ = Temporal.conjugateMatter := by
      rw [algebraic_eq_zeroCandidate]
      rfl

private theorem recentered_u5_coframe_eq_temporal (contact : BasePoint) :
    (RecenteredU5 contact).coframe =
      (RecenteredTemporal contact).coframe := by
  unfold RecenteredU5 RecenteredTemporal
  unfold fullyRecenterHolonomicConfiguration
  rw [u5_coframe_eq_temporal]

private theorem recentered_u5_gaugeConnection_eq_temporal
    (contact : BasePoint) :
    (RecenteredU5 contact).gaugeConnection =
      (RecenteredTemporal contact).gaugeConnection := by
  unfold RecenteredU5 RecenteredTemporal
  unfold fullyRecenterHolonomicConfiguration
  rw [u5_gaugeConnection_eq_temporal]

private theorem recentered_u5_scalar_eq_temporal (contact : BasePoint) :
    (RecenteredU5 contact).scalar =
      (RecenteredTemporal contact).scalar := by
  unfold RecenteredU5 RecenteredTemporal
  unfold fullyRecenterHolonomicConfiguration
  rw [u5_scalar_eq_temporal]

private theorem recentered_u5_matter_eq_temporal (contact : BasePoint) :
    (RecenteredU5 contact).matter =
      (RecenteredTemporal contact).matter := by
  unfold RecenteredU5 RecenteredTemporal
  unfold fullyRecenterHolonomicConfiguration
  rw [u5_matter_eq_temporal]

private theorem recentered_u5_conjugateMatter_eq_temporal
    (contact : BasePoint) :
    (RecenteredU5 contact).conjugateMatter =
      (RecenteredTemporal contact).conjugateMatter := by
  unfold RecenteredU5 RecenteredTemporal
  unfold fullyRecenterHolonomicConfiguration
  rw [u5_conjugateMatter_eq_temporal]

private theorem occurrenceTemporal_coframe_eq (contact : BasePoint) :
    (OccurrenceTemporal contact).coframe =
      (RecenteredTemporal contact).coframe := by
  exact recentered_u5_coframe_eq_temporal contact

private theorem occurrenceTemporal_gaugeConnection_eq
    (contact : BasePoint) :
    (OccurrenceTemporal contact).gaugeConnection =
      (RecenteredTemporal contact).gaugeConnection := by
  exact recentered_u5_gaugeConnection_eq_temporal contact

private theorem occurrenceTemporal_scalar_origin_eq (contact : BasePoint) :
    (OccurrenceTemporal contact).scalar 0 =
      (RecenteredTemporal contact).scalar 0 := by
  unfold OccurrenceTemporal completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  change
    (RecenteredU5 contact).scalar 0 +
        canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source
            (RecenteredU5 contact)) 0 =
      (RecenteredTemporal contact).scalar 0
  rw [congrFun (recentered_u5_scalar_eq_temporal contact) 0]
  simp [canonicalTimeSecondPrimitive]

private theorem recenteredTemporal_scalarDirectionalDerivative_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    let contact := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative (RecenteredTemporal contact).scalar
        0 direction =
      0 := by
  dsimp only
  let contact := canonicalCauchySlicePoint 0 space
  rw [← recentered_u5_scalar_eq_temporal contact]
  unfold fieldDirectionalDerivative
  rw [
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_hasFDerivAt
      space).fderiv,
    fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]
  change
    (fderiv ℝ (fun _ : BasePoint =>
      sourceGeneratedVacuumCoordinates Source) 0)
        (coordinateDirection direction) = 0
  simp only [fderiv_const_apply, zero_apply]

private theorem
    occurrenceTemporal_scalarDirectionalDerivative_eq_recenteredTemporal
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    let contact := canonicalCauchySlicePoint 0 space
    fieldDirectionalDerivative (OccurrenceTemporal contact).scalar
        0 direction =
      fieldDirectionalDerivative (RecenteredTemporal contact).scalar
        0 direction := by
  dsimp only
  let contact := canonicalCauchySlicePoint 0 space
  let input := RecenteredU5 contact
  by_cases generatedDifferentiable :
      DifferentiableAt ℝ (OccurrenceTemporal contact).scalar 0
  · have inputDifferentiable :
        DifferentiableAt ℝ input.scalar 0 := by
      change DifferentiableAt ℝ (RecenteredU5 contact).scalar 0
      simpa [RecenteredU5, U5, contact] using
        (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_recentered_scalar_differentiableAt
          space)
    have generatedDifferentiable' :
        DifferentiableAt ℝ
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source input).scalar 0 := by
      simpa [OccurrenceTemporal, completeJointGlobalTemporalCurrent, input,
        contact] using generatedDifferentiable
    have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        Source input 0
        (by simpa only [canonicalCauchySlicePoint_zero_zero_local] using
          inputDifferentiable)
        (by simpa only [canonicalCauchySlicePoint_zero_zero_local] using
          generatedDifferentiable')
        direction
    calc
      fieldDirectionalDerivative (OccurrenceTemporal contact).scalar
          0 direction =
        fieldDirectionalDerivative input.scalar 0 direction := by
          simpa [input, contact, OccurrenceTemporal,
            completeJointGlobalTemporalCurrent,
            canonicalCauchySlicePoint_zero_zero_local] using generated
      _ = fieldDirectionalDerivative (RecenteredTemporal contact).scalar
          0 direction := by
        rw [recentered_u5_scalar_eq_temporal contact]
  · have generatedDerivativeZero :
        fieldDirectionalDerivative (OccurrenceTemporal contact).scalar
            0 direction = 0 := by
      unfold fieldDirectionalDerivative
      rw [fderiv_zero_of_not_differentiableAt generatedDifferentiable]
      rfl
    rw [generatedDerivativeZero]
    exact
      (recenteredTemporal_scalarDirectionalDerivative_zero
        space direction).symm

/-- The source/action temporal producer preserves the scalar covariant
first jet at every fixed zero-slice occurrence.  The theorem consumes neither
the old U6h scalar relation nor a residual or zero-fiber receipt. -/
theorem fixedP506L0_occurrenceTemporal_scalarFirstJet_eq_recenteredTemporal
    (space : StageNineSpatialPoint) :
    let contact := canonicalCauchySlicePoint 0 space
    holonomicScalarCovariantDerivative (OccurrenceTemporal contact) 0 =
      holonomicScalarCovariantDerivative (RecenteredTemporal contact) 0 := by
  dsimp only
  let contact := canonicalCauchySlicePoint 0 space
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [
    occurrenceTemporal_scalarDirectionalDerivative_eq_recenteredTemporal
      space direction,
    congrFun (occurrenceTemporal_gaugeConnection_eq contact) 0,
    occurrenceTemporal_scalar_origin_eq contact]

/-- The same action-owned scalar first-jet seam at every contact in the
authoritative fixed P506/L0 domain.  The mother-action second primitive
preserves the recentered U5 first jet; the existing U5/Temporal field
equalities then identify the exact action data consumed by this occurrence.
No horizontal target relation or residual readout enters the proof. -/
theorem fixedP506L0_occurrenceTemporal_scalarFirstJet_eq_recenteredTemporal_inDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    let contact := canonicalCauchySlicePoint time space
    holonomicScalarCovariantDerivative (OccurrenceTemporal contact) 0 =
      holonomicScalarCovariantDerivative (RecenteredTemporal contact) 0 := by
  dsimp only
  let contact := canonicalCauchySlicePoint time space
  calc
    holonomicScalarCovariantDerivative (OccurrenceTemporal contact) 0 =
        holonomicScalarCovariantDerivative (RecenteredU5 contact) 0 :=
      fixedP506L0_U5_occurrenceTemporal_scalarFirstJet_eq_recentered
        time space inDomain
    _ = holonomicScalarCovariantDerivative (RecenteredTemporal contact) 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [recentered_u5_scalar_eq_temporal contact,
        recentered_u5_gaugeConnection_eq_temporal contact]

private theorem occurrenceTemporal_matter_origin_eq (contact : BasePoint) :
    (OccurrenceTemporal contact).matter 0 =
      (RecenteredTemporal contact).matter 0 := by
  unfold OccurrenceTemporal completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  change
    (RecenteredU5 contact).matter 0 +
        matterCoordinateEquiv.symm
          (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source
              (RecenteredU5 contact)) 0) =
      (RecenteredTemporal contact).matter 0
  rw [congrFun (recentered_u5_matter_eq_temporal contact) 0]
  simp [canonicalTimePrimitive]

private theorem occurrenceTemporal_conjugateMatter_origin_eq
    (contact : BasePoint) :
    (OccurrenceTemporal contact).conjugateMatter 0 =
      (RecenteredTemporal contact).conjugateMatter 0 := by
  unfold OccurrenceTemporal completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  change
    (RecenteredU5 contact).conjugateMatter 0 +
        StageNineConjugateMatterVariation.matterDualOfCoordinates
          (canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection Source
              (RecenteredU5 contact)) 0) =
      (RecenteredTemporal contact).conjugateMatter 0
  rw [congrFun (recentered_u5_conjugateMatter_eq_temporal contact) 0]
  simp [canonicalTimePrimitive]

private theorem algebraic_p286Euler_recenter_origin
    (contact : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        (fullyRecenterHolonomicConfiguration Algebraic contact) 0 =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic contact := by
  have residualEq :=
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      Source (fullyRecenterHolonomicConfiguration Algebraic contact) Algebraic
      0 contact
      (generatedActionJet_fullyRecenter_origin_unconditional Source Algebraic
        contact)
  exact congrArg
    (fun residual => residual.p286GaugeConnection) residualEq

/-- The exact producer/readout seam.  Every forcing input except the scalar
covariant first jet is discharged from existing source/current preservation.
The remaining premise is intentionally typed as action data, not as a
residual value or zero-fiber certificate. -/
theorem fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_of_scalarFirstJet
    (contact : BasePoint)
    (scalarFirstJetEq :
      holonomicScalarCovariantDerivative (OccurrenceTemporal contact) 0 =
        holonomicScalarCovariantDerivative (RecenteredTemporal contact) 0) :
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) =
      p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) := by
  calc
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (RecenteredTemporal contact) := by
      apply
        diracDualFormNativeP286CanonicalOriginActionForcing_eq_of_actionData_eq
      · exact occurrenceTemporal_coframe_eq contact
      · exact occurrenceTemporal_gaugeConnection_eq contact
      · exact occurrenceTemporal_scalar_origin_eq contact
      · exact scalarFirstJetEq
      · exact occurrenceTemporal_matter_origin_eq contact
      · exact occurrenceTemporal_conjugateMatter_origin_eq contact
    _ = p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0
          (fullyRecenterHolonomicConfiguration Algebraic contact) 0) := by
      unfold diracDualFormNativeP286CanonicalOriginActionForcing
        diracDualFormNativeP286CanonicalOriginActionDual
      rw [
        fixedP506L0_recenteredTemporal_zeroWriteCandidate_eq_recenteredAlgebraic]
    _ = p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) := by
      rw [algebraic_p286Euler_recenter_origin]

/-- On every authoritative spacetime occurrence, the U5 occurrence forcing is
the matching Algebraic Euler wedge dual.  The only former seam—the scalar
covariant first jet—is now generated by the same mother-action temporal
producer. -/
theorem fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_inDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    let contact := canonicalCauchySlicePoint time space
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) =
      p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) := by
  dsimp only
  exact
    fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_of_scalarFirstJet
      (canonicalCauchySlicePoint time space)
      (fixedP506L0_occurrenceTemporal_scalarFirstJet_eq_recenteredTemporal_inDomain
        time space inDomain)

/-- On the canonical zero slice the fixed source/action temporal producer
supplies the remaining scalar first-jet seam, so the U5 occurrence forcing is
unconditionally the matching global algebraic Euler wedge dual. -/
theorem fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_zeroSlice
    (space : StageNineSpatialPoint) :
    let contact := canonicalCauchySlicePoint 0 space
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) =
      p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) := by
  dsimp only
  exact
    fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_of_scalarFirstJet
      (canonicalCauchySlicePoint 0 space)
      (fixedP506L0_occurrenceTemporal_scalarFirstJet_eq_recenteredTemporal
        space)

/-- U6 has the same occurrence forcing as U5 by the already generated
action-data congruence.  This consumes the faithful pairing equality, not a
residual or a zero receipt. -/
theorem fixedP506L0_U6_occurrenceOriginActionForcing_eq_U5
    (contact : BasePoint) :
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration
            fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual
            contact)) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) := by
  have writeEq :=
    fixedP506L0_U6_U5_completeJointP286OccurrenceWriteProfile_eq contact
  have paired := congrArg p286GaugeOneFormPairingEquiv writeEq
  simpa [completeJointP286CanonicalOccurrenceWriteProfile,
    diracDualFormNativeP286CanonicalGeneratedWrite] using paired

/-- The faithful U6/U5 action-data handoff upgrades the all-contact U5 result
to the authoritative U6 occurrence.  The theorem reads the forcing selected
by the action; it does not construct a field from that readout. -/
theorem fixedP506L0_U6_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_inDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    let contact := canonicalCauchySlicePoint time space
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) =
      p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) := by
  dsimp only
  let contact := canonicalCauchySlicePoint time space
  calc
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) :=
      fixedP506L0_U6_occurrenceOriginActionForcing_eq_U5 contact
    _ = p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) :=
      fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_inDomain
        time space inDomain

/-- Final authoritative-domain forcing normal form.  The U6 occurrence
forcing is the wedge dual of the radial action profile plus the complete
same-source temporal support.  Both summands are action readouts; this theorem
does not use them as an instruction for constructing a successor. -/
theorem fixedP506L0_U6_occurrenceOriginActionForcing_eq_radial_add_timeCorrection_inDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    let contact := canonicalCauchySlicePoint time space
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) =
      p286GaugeThreeFormWedgeLinearDual
        (fixedP506L0RadialActionEulerField contact +
          fixedP506L0AlgebraicActionEulerTimeCorrection contact) := by
  dsimp only
  rw [
    fixedP506L0_U6_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_inDomain
      time space inDomain,
    fixedP506L0_Algebraic_p286Euler_eq_radial_add_timeCorrection]

/-- The two action-owned support channels after applying the faithful wedge
dual: radial zero-slice forcing and canonical temporal correction. -/
theorem fixedP506L0_U6_occurrenceOriginActionForcing_supportSplit_inDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    let contact := canonicalCauchySlicePoint time space
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) =
      p286GaugeThreeFormWedgeLinearDual
          (fixedP506L0RadialActionEulerField contact) +
        p286GaugeThreeFormWedgeLinearDual
          (fixedP506L0AlgebraicActionEulerTimeCorrection contact) := by
  dsimp only
  rw [
    fixedP506L0_U6_occurrenceOriginActionForcing_eq_radial_add_timeCorrection_inDomain
      time space inDomain]
  apply LinearMap.ext
  intro oneForm
  exact
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right oneForm
      (fixedP506L0RadialActionEulerField
        (canonicalCauchySlicePoint time space))
      (fixedP506L0AlgebraicActionEulerTimeCorrection
        (canonicalCauchySlicePoint time space))

/-- The faithful U6/U5 handoff preserves the same mother-action forcing on
the complete zero slice. -/
theorem fixedP506L0_U6_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_zeroSlice
    (space : StageNineSpatialPoint) :
    let contact := canonicalCauchySlicePoint 0 space
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) =
      p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) := by
  dsimp only
  let contact := canonicalCauchySlicePoint 0 space
  calc
    diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (OccurrenceTemporal contact) :=
      fixedP506L0_U6_occurrenceOriginActionForcing_eq_U5 contact
    _ = p286GaugeThreeFormWedgeLinearDual
        (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          contact) :=
      fixedP506L0_U5_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_zeroSlice
        space

/-- Exact zero-slice occurrence-write normal form generated by the fixed
mother action.  Its charge is read at `e0`; neither a residual coordinate nor
any target write enters the constructor. -/
theorem fixedP506L0_U6_occurrenceWriteProfile_zeroSlice_radialTemporal
    (space : StageNineSpatialPoint) :
    let contact := canonicalCauchySlicePoint 0 space
    completeJointP286CanonicalOccurrenceWriteProfile Source U6 contact =
      p286SpatialRadiusSquared contact •
        p286TemporalGaugeOneForm
          fixedP506L0U6OccurrenceP286MotherActionCharge := by
  dsimp only
  let contact := canonicalCauchySlicePoint 0 space
  unfold completeJointP286CanonicalOccurrenceWriteProfile
    diracDualFormNativeP286CanonicalGeneratedWrite
  rw [
    fixedP506L0_U6_occurrenceOriginActionForcing_eq_globalAlgebraicEulerWedgeDual_zeroSlice
      space,
    fixedP506L0_Algebraic_p286Euler_zeroSlice_spatialVolumeNormalForm]
  change
    p286GaugeOneFormPairingEquiv.symm
        (p286GaugeThreeFormWedgeDualOperator
          (p286SpatialRadiusSquared contact •
            p286SpatialVolumeGaugeThreeForm
              fixedP506L0U6OccurrenceP286MotherActionCharge)) = _
  rw [map_smul, map_smul, p286GaugeThreeFormWedgeDualOperator_apply,
    p286PairingInverse_spatialVolumeWedgeDual]

/-- The actual Hessian of the global radial-quartic connection generates the
authoritative fixed-U6 mother-action forcing on every point of the zero slice.
This is the positive action-owned replacement for the diagnostic U6h
cancellation. -/
theorem fixedP506L0_U6_radialQuarticActionPrincipal_response_eq_occurrenceForcing_zeroSlice
    (space : StageNineSpatialPoint) :
    let contact := canonicalCauchySlicePoint 0 space
    p286HolonomicSecondJetEulerLagrangeResponse
        (p286RadialQuarticTemporalSecondJet
          fixedP506L0U6OccurrenceP286MotherActionCharge contact) =
      diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) := by
  dsimp only
  let contact := canonicalCauchySlicePoint 0 space
  calc
    p286HolonomicSecondJetEulerLagrangeResponse
        (p286RadialQuarticTemporalSecondJet
          fixedP506L0U6OccurrenceP286MotherActionCharge contact) =
      p286GaugeOneFormPairingDual
        (completeJointP286CanonicalOccurrenceWriteProfile Source U6
          contact) := by
      rw [p286RadialQuarticTemporalSecondJet_response,
        fixedP506L0_U6_occurrenceWriteProfile_zeroSlice_radialTemporal]
    _ = diracDualFormNativeP286CanonicalOriginActionForcing Source
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U6 contact)) :=
      completeJointP286CanonicalOccurrenceWriteProfile_pairingDual_eq_actionForcing
        Source U6 contact

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ActionForcingBridge
