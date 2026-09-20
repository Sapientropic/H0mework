import H0mework.Physics.JointVariation.TemporalDevelopmentOperator
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.TimePrimitive.SecondAmbientJetRegularity
import H0mework.Physics.QuarticDynamics.FixedScalarMomentumCarry
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality

/-!
# Fixed P506/L0 coupled temporal development after the radial P286 write

The established complete-joint temporal producer is restarted on the fixed
radial-plus-scalar-momentum current.  It recomputes the scalar acceleration,
primal matter velocity, and adjoint matter velocity from the same
source/current occurrence profile and integrates all three on the canonical
Cauchy foliation.

The constructor consumes no residual, support coordinate, target derivative,
branch, or equation receipt.  In particular, the historical post-A/B P286
read is not an input.  The radial P286 fields and the carried scalar first jet
enter only through the already action-selected current.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticCoupledTemporalDevelopment

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticActionSelection
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

local instance coupledTemporalP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance coupledTemporalP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance coupledTemporalP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Charge : P286CoordinateCarrier :=
  fixedP506L0U6OccurrenceP286MotherActionCharge

private abbrev Restart : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source Current 0

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- One source/current-only global write for the coupled scalar, primal, and
adjoint temporal action channels. -/
def fixedP506L0U6RadialQuarticCoupledTemporalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    Source Current

/-! ## Exact retention of the six untouched primitive fields -/

@[simp] theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_coframe :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.coframe =
      Current.coframe :=
  rfl

@[simp] theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_gravityConnection :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.gravityConnection =
      Current.gravityConnection :=
  rfl

@[simp] theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_gravityAuxiliary :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.gravityAuxiliary =
      Current.gravityAuxiliary :=
  rfl

@[simp] theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_gravitySimplicityMultiplier :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.gravitySimplicityMultiplier =
      Current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_gaugeConnection :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.gaugeConnection =
      Current.gaugeConnection :=
  rfl

@[simp] theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_gaugeAuxiliary :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.gaugeAuxiliary =
      Current.gaugeAuxiliary :=
  rfl

/-! ## Common Cauchy anchor of the three written fields -/

@[simp] theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_scalar_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.scalar
        (canonicalCauchySlicePoint 0 space) =
      Current.scalar (canonicalCauchySlicePoint 0 space) :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
    Source Current space

@[simp] theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_matter_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.matter
        (canonicalCauchySlicePoint 0 space) =
      Current.matter (canonicalCauchySlicePoint 0 space) :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
    Source Current space

@[simp] theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatter_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticCoupledTemporalActual.conjugateMatter
        (canonicalCauchySlicePoint 0 space) =
      Current.conjugateMatter (canonicalCauchySlicePoint 0 space) :=
  sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
    Source Current space

/-- The complete temporal write remains on the fixed P506/L0 source lineage. -/
theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSuccessor_exactLineage

/-- The coupled temporal producer consumes the radial connection selected by
the fixed mother-action occurrence, rather than a caller-supplied forcing. -/
theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_eq_actionSelected :
    fixedP506L0U6RadialQuarticCoupledTemporalActual =
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        Source
        (scalarActionTemporalMomentumCarryCauchyDevelopmentOperator Source
          (completeJointGlobalP286AlgebraicCurrent Source
            FixedP506FormNativeJointActionSolvedSuccessor)
          fixedP506L0U6ActionSelectedRadialQuarticConstitutiveActual) := by
  exact congrArg
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source)
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_eq_actionSelected

/-! ## Action-profile regularity at the fixed common occurrence -/

private theorem current_coframe_eq_fixedInput :
    Current.coframe = FixedInput.coframe := by
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_eq_algebraic]
  simp [completeJointGlobalP286AlgebraicCurrent,
    completeJointGlobalTemporalCurrent]

private theorem u5_matter_eq_algebraic :
    U5.matter = Algebraic.matter := by
  exact
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC.trans
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
        Source FixedInput))

private theorem u5_conjugateMatter_eq_algebraic :
    U5.conjugateMatter = Algebraic.conjugateMatter := by
  exact
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC.trans
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
        Source FixedInput))

private theorem current_matter_eq_u5 :
    Current.matter = U5.matter :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic.trans
    u5_matter_eq_algebraic.symm

private theorem current_conjugateMatter_eq_u5 :
    Current.conjugateMatter = U5.conjugateMatter :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic.trans
    u5_conjugateMatter_eq_algebraic.symm

private theorem algebraic_gaugeConnection_eq_fixedInput :
    Algebraic.gaugeConnection = FixedInput.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source
        (completeJointGlobalTemporalCurrent Source FixedInput) 0 by
    exact fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem current_coframe_contDiffAt_infty
    (point : BasePoint) :
    ContDiffAt ℝ ∞ Current.coframe point := by
  rw [current_coframe_eq_fixedInput]
  exact
    (StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
      FixedInput fixedP506FormNativeJointActionSolvedSuccessor_smooth
      ).contDiffAt

private theorem current_coframe_contDiffAt_two_origin :
    ContDiffAt ℝ 2 Current.coframe 0 :=
  (current_coframe_contDiffAt_infty 0).of_le (by decide)

private theorem current_coframe_contDiffAt_one_origin :
    ContDiffAt ℝ 1 Current.coframe 0 :=
  current_coframe_contDiffAt_two_origin.of_le (by norm_num)

private theorem current_scalar_contDiffAt_infty
    (point : BasePoint) :
    ContDiffAt ℝ ∞ Current.scalar point :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_contDiff
    |>.contDiffAt

private theorem current_scalar_contDiffAt_zero_origin :
    ContDiffAt ℝ 0 Current.scalar 0 :=
  (current_scalar_contDiffAt_infty 0).of_le (by norm_num)

private theorem current_matterCoordinates_contDiffAt_infty_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (fun point => matterCoordinateEquiv (Current.matter point))
      (canonicalCauchySlicePoint 0 space) := by
  rw [current_matter_eq_u5]
  exact
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matterCoordinates_contDiffAt
      0 space (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space))

private theorem current_conjugateMatterCoordinates_contDiffAt_infty_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞ (holonomicConjugateMatterCoordinates Current)
      (canonicalCauchySlicePoint 0 space) := by
  unfold holonomicConjugateMatterCoordinates
  rw [current_conjugateMatter_eq_u5]
  exact
    (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatterCoordinates_contDiffAt
      0 space (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space))

private theorem current_matterCoordinates_contDiffAt_infty_origin :
    ContDiffAt ℝ ∞
      (fun point => matterCoordinateEquiv (Current.matter point)) 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact current_matterCoordinates_contDiffAt_infty_zeroSlice 0

private theorem current_conjugateMatterCoordinates_contDiffAt_infty_origin :
    ContDiffAt ℝ ∞ (holonomicConjugateMatterCoordinates Current) 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact current_conjugateMatterCoordinates_contDiffAt_infty_zeroSlice 0

private theorem current_gaugeConnectionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Current.gaugeConnection point direction) := by
  rw [show
    (fun point =>
      p286CoordinateEquiv (Current.gaugeConnection point direction)) =
      fun point =>
        p286CoordinateEquiv (FixedInput.gaugeConnection point direction) +
          p286RadialQuarticTemporalConnection Charge point direction by
    funext point
    rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeConnection_normalForm,
      map_add, p286CoordinateEquiv.apply_symm_apply,
      congrFun algebraic_gaugeConnection_eq_fixedInput point]]
  exact
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.1
      direction).add
      (contDiff_pi.mp (p286RadialQuarticTemporalConnection_contDiff Charge)
        direction)

private theorem canonicalSpacetimeContactTranslation_contDiff
    (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

private theorem current_coframe_nondegenerate_zeroSlice
    (space : StageNineSpatialPoint) :
    Matrix.det
        (Current.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0 := by
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_zeroSlice]
  norm_num

private theorem current_scalarAccelerationProfile_contDiffAt_infty_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (completeJointScalarAccelerationProfile Source Current)
      (canonicalCauchySlicePoint 0 space) := by
  exact completeJointScalarAccelerationProfile_contDiffAt_of_local
    Source Current (canonicalCauchySlicePoint 0 space)
    (current_coframe_nondegenerate_zeroSlice space)
    (current_coframe_contDiffAt_infty _)
    (current_scalar_contDiffAt_infty _)
    (current_matterCoordinates_contDiffAt_infty_zeroSlice space)
    (current_conjugateMatterCoordinates_contDiffAt_infty_zeroSlice space)
    (fun direction =>
      (current_gaugeConnectionCoordinate_contDiff direction).contDiffAt)

private theorem current_scalarAccelerationProfile_recentered_contDiffAt_one
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source Current ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have profileAtTranslated : ContDiffAt ℝ 1
      (completeJointScalarAccelerationProfile Source Current)
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa [point, canonicalSpacetimeContactTranslation] using
      (current_scalarAccelerationProfile_contDiffAt_infty_zeroSlice space
        ).of_le (by norm_num)
  exact profileAtTranslated.comp 0
    ((canonicalSpacetimeContactTranslation_contDiff point).contDiffAt.of_le
      (by norm_num))

private theorem coupledScalarSecondPrimitive_recentered_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Current) ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space))
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
  rw [
    canonicalTimeSecondPrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice]
  exact canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
    (completeJointScalarAccelerationProfile Source Current ∘
      canonicalSpacetimeContactTranslation
        (canonicalCauchySlicePoint 0 space))
    (current_scalarAccelerationProfile_recentered_contDiffAt_one space)

private theorem coupledRecentered_scalar_eq_add_secondPrimitive
    (space : StageNineSpatialPoint) :
    (fullyRecenterHolonomicConfiguration
        fixedP506L0U6RadialQuarticCoupledTemporalActual
        (canonicalCauchySlicePoint 0 space)).scalar =
      (fullyRecenterHolonomicConfiguration Current
          (canonicalCauchySlicePoint 0 space)).scalar +
        (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Current) ∘
            canonicalSpacetimeContactTranslation
              (canonicalCauchySlicePoint 0 space)) := by
  funext point
  unfold fullyRecenterHolonomicConfiguration
    fixedP506L0U6RadialQuarticCoupledTemporalActual
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  rfl

private theorem recenteredCurrent_scalar_differentiableAt
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (fullyRecenterHolonomicConfiguration Current
        (canonicalCauchySlicePoint 0 space)).scalar 0 := by
  change DifferentiableAt ℝ
    (Current.scalar ∘
      canonicalSpacetimeContactTranslation
        (canonicalCauchySlicePoint 0 space)) 0
  exact
    (fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_contDiff.comp
      (canonicalSpacetimeContactTranslation_contDiff
        (canonicalCauchySlicePoint 0 space))).differentiable
      (by simp) |>.differentiableAt

/-- The coupled second-order scalar leg has zero ambient first jet on the
canonical zero slice.  Hence it preserves the complete scalar covariant first
jet carried through the radial P286 write. -/
theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_scalarCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6RadialQuarticCoupledTemporalActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative Current
        (canonicalCauchySlicePoint 0 space) := by
  let contact := canonicalCauchySlicePoint 0 space
  let generatedRecentered :=
    fullyRecenterHolonomicConfiguration
      fixedP506L0U6RadialQuarticCoupledTemporalActual contact
  let currentRecentered := fullyRecenterHolonomicConfiguration Current contact
  have primitiveDerivative :=
    coupledScalarSecondPrimitive_recentered_hasFDerivAt space
  have primitiveDerivative' :
      HasFDerivAt
        (canonicalTimeSecondPrimitive
            (completeJointScalarAccelerationProfile Source Current) ∘
          canonicalSpacetimeContactTranslation contact)
        (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) 0 := by
    simpa [contact] using primitiveDerivative
  have currentDifferentiable :
      DifferentiableAt ℝ currentRecentered.scalar 0 := by
    simpa [currentRecentered, contact] using
      recenteredCurrent_scalar_differentiableAt space
  have primitiveValueZero :
      (canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source Current) ∘
        canonicalSpacetimeContactTranslation contact) 0 = 0 := by
    change canonicalTimeSecondPrimitive
      (completeJointScalarAccelerationProfile Source Current)
      (canonicalSpacetimeContactTranslation contact 0) = 0
    rw [canonicalSpacetimeContactTranslation_zero]
    exact canonicalTimeSecondPrimitive_zeroSlice
      (completeJointScalarAccelerationProfile Source Current) space
  have scalarDerivativeEq (direction : LorentzianIndex) :
      fieldDirectionalDerivative generatedRecentered.scalar 0 direction =
        fieldDirectionalDerivative currentRecentered.scalar 0 direction := by
    unfold fieldDirectionalDerivative
    rw [show generatedRecentered.scalar =
        currentRecentered.scalar +
          (canonicalTimeSecondPrimitive
              (completeJointScalarAccelerationProfile Source Current) ∘
            canonicalSpacetimeContactTranslation contact) by
      simpa [generatedRecentered, currentRecentered, contact] using
        coupledRecentered_scalar_eq_add_secondPrimitive space]
    rw [fderiv_add currentDifferentiable
      primitiveDerivative'.differentiableAt, add_apply,
      primitiveDerivative'.fderiv, zero_apply, add_zero]
  have scalarValueEq : generatedRecentered.scalar 0 =
      currentRecentered.scalar 0 := by
    rw [show generatedRecentered.scalar =
        currentRecentered.scalar +
          (canonicalTimeSecondPrimitive
              (completeJointScalarAccelerationProfile Source Current) ∘
            canonicalSpacetimeContactTranslation contact) by
      simpa [generatedRecentered, currentRecentered, contact] using
        coupledRecentered_scalar_eq_add_secondPrimitive space]
    rw [Pi.add_apply, primitiveValueZero, add_zero]
  have gaugeConnectionEq (direction : LorentzianIndex) :
      generatedRecentered.gaugeConnection 0 direction =
        currentRecentered.gaugeConnection 0 direction := by
    rfl
  rw [←
    fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
      fixedP506L0U6RadialQuarticCoupledTemporalActual contact,
    ←
    fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
      Current contact]
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [scalarDerivativeEq direction, gaugeConnectionEq direction,
    scalarValueEq]

/-- The charged action read is unchanged on the zero slice because the
coupled temporal write preserves precisely the five action-data fields read by
that three-form. -/
theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_chargedGaugeThreeForm_zeroSlice_eq_current
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField
          fixedP506L0U6RadialQuarticCoupledTemporalActual
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Current
          (canonicalCauchySlicePoint 0 space)) := by
  exact formNativeChargedGaugeThreeForm_eq_of_actionData_eq Source
    fixedP506L0U6RadialQuarticCoupledTemporalActual Current
    (canonicalCauchySlicePoint 0 space)
    (congrFun fixedP506L0U6RadialQuarticCoupledTemporalActual_coframe _)
    (fixedP506L0U6RadialQuarticCoupledTemporalActual_scalar_zeroSlice space)
    (fixedP506L0U6RadialQuarticCoupledTemporalActual_scalarCovariantDerivative_zeroSlice
      space)
    (fixedP506L0U6RadialQuarticCoupledTemporalActual_matter_zeroSlice space)
    (fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatter_zeroSlice
      space)

private theorem coupledP286Geometric_eq_current
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        fixedP506L0U6RadialQuarticCoupledTemporalActual point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Current point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [fixedP506L0U6RadialQuarticCoupledTemporalActual_gaugeConnection,
    fixedP506L0U6RadialQuarticCoupledTemporalActual_gaugeAuxiliary]

/-- P286 read-after-write soundness for the complete coupled temporal leg.
The same transported U6 producer responsibility remains settled on every
zero-slice occurrence; this does not mint an independent constraint debt. -/
theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_p286Euler123_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        fixedP506L0U6RadialQuarticCoupledTemporalActual
        (canonicalCauchySlicePoint 0 space) 3 = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [coupledP286Geometric_eq_current,
    fixedP506L0U6RadialQuarticCoupledTemporalActual_chargedGaugeThreeForm_zeroSlice_eq_current]
  exact
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_p286Euler123_zeroSlice
      space

private theorem current_coframe_origin : Current.coframe 0 = 1 := by
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact
    (fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_zeroSlice 0)

private theorem current_nondegenerate_origin :
    Matrix.det (Current.coframe 0) ≠ 0 := by
  rw [current_coframe_origin]
  norm_num

private theorem current_noncharacteristic_origin :
    coframeTemporalPrincipalScalar (Current.coframe 0) ≠ 0 := by
  rw [current_coframe_origin, coframeTemporalPrincipalScalar_one]
  norm_num

private theorem restart_coframe_origin : Restart.coframe 0 = 1 := by
  simp [Restart, completeJointGeneratedProfileRestartCurrent,
    current_coframe_origin]

private theorem restart_noncharacteristic_origin :
    coframeTemporalPrincipalScalar (Restart.coframe 0) ≠ 0 := by
  rw [restart_coframe_origin, coframeTemporalPrincipalScalar_one]
  norm_num

private theorem restart_nondegenerate_origin :
    Matrix.det (Restart.coframe 0) ≠ 0 := by
  rw [restart_coframe_origin]
  norm_num

private theorem fixedCoupledMatterCorrection_contDiffAt_origin :
    ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection Source Current) 0 := by
  exact completeJointMatterTemporalCoordinateCorrection_contDiffAt_of_local
    Source Current 0 current_nondegenerate_origin
    current_noncharacteristic_origin current_coframe_contDiffAt_one_origin
    current_scalar_contDiffAt_zero_origin
    (current_matterCoordinates_contDiffAt_infty_origin.of_le (by norm_num))
    (current_conjugateMatterCoordinates_contDiffAt_infty_origin.of_le
      (by norm_num))
    (fun direction =>
      (current_gaugeConnectionCoordinate_contDiff direction).contDiffAt.of_le
        (by norm_num))

private theorem fixedCoupledAdjointCorrection_contDiffAt_origin :
    ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection Source Current) 0 := by
  exact completeJointAdjointTemporalCoordinateCorrection_contDiffAt_of_local
    Source Current 0 current_nondegenerate_origin
    current_noncharacteristic_origin current_coframe_contDiffAt_two_origin
    current_scalar_contDiffAt_zero_origin
    (current_matterCoordinates_contDiffAt_infty_origin.of_le (by norm_num))
    (current_conjugateMatterCoordinates_contDiffAt_infty_origin.of_le
      (by norm_num))
    (fun direction =>
      (current_gaugeConnectionCoordinate_contDiff direction).contDiffAt.of_le
        (by norm_num))

/-- The profile velocity itself is certified by the repaired primal
mother-action law on the exact recentered Cartan restart occurrence from
which it was generated. -/
theorem fixedP506L0U6RadialQuarticCoupledTemporalProfile_primalActionLaw :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw Restart 0
      ((sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
          ).matterVelocity +
        holonomicMatterConnectionAction Restart 0
          canonicalLorentzianTimeDirection) := by
  have generated :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      Restart 0 restart_noncharacteristic_origin
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  change
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw Restart 0
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
          Restart 0 +
        holonomicMatterConnectionAction Restart 0
          canonicalLorentzianTimeDirection)
  convert generated using 1
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
  abel

/-- The independently generated adjoint profile is certified by the live-
coframe mother-action law on that same recentered restart occurrence.  The
intermediate primal write changes no point data read by this adjoint law at
the common origin. -/
theorem fixedP506L0U6RadialQuarticCoupledTemporalProfile_adjointActionLaw :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw Restart 0
      (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).adjointVelocity := by
  have generated :=
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_satisfies
      Restart 0 restart_nondegenerate_origin restart_noncharacteristic_origin
  have velocityEquality :
      (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).adjointVelocity =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity Restart 0 := by
    rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
    apply
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro direction
      rfl
  rw [velocityEquality]
  exact generated

/-- Full ambient first-jet realization of the same generated primal profile
on the single coupled output actual. -/
theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_matterCoordinates_hasFDerivAt_origin :
    HasFDerivAt
      (fun point =>
        matterCoordinateEquiv
          (fixedP506L0U6RadialQuarticCoupledTemporalActual.matter point))
      ((fderiv ℝ (fun point => matterCoordinateEquiv (Current.matter point)) 0) +
        canonicalTimeProjection.smulRight
          (completeJointMatterTemporalCoordinateCorrection Source Current 0))
      0 := by
  exact completeJointTemporalMatterCoordinates_hasFDerivAt_zero_of_contDiffAt
    Source Current
    (current_matterCoordinates_contDiffAt_infty_origin.differentiableAt
      (by norm_num))
    fixedCoupledMatterCorrection_contDiffAt_origin

/-- The new common actual realizes the source/current action-generated primal
matter velocity in its full ambient Frechet derivative at the fixed
occurrence. -/
theorem fixedP506L0U6RadialQuarticCoupledTemporalActual_matterTemporalDerivative_origin :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            (fixedP506L0U6RadialQuarticCoupledTemporalActual.matter point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
          ).matterVelocity := by
  exact completeJointGlobalTemporalCurrent_matterTimeDerivative_zero
    Source Current
    (current_matterCoordinates_contDiffAt_infty_origin.differentiableAt
      (by norm_num))
    fixedCoupledMatterCorrection_contDiffAt_origin

/-- Full ambient first-jet realization of the independently generated
adjoint profile on the same coupled output actual. -/
theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatterCoordinates_hasFDerivAt_origin :
    HasFDerivAt
      (holonomicConjugateMatterCoordinates
        fixedP506L0U6RadialQuarticCoupledTemporalActual)
      ((fderiv ℝ (holonomicConjugateMatterCoordinates Current) 0) +
        canonicalTimeProjection.smulRight
          (completeJointAdjointTemporalCoordinateCorrection Source Current 0))
      0 := by
  have currentDerivative :=
    (current_conjugateMatterCoordinates_contDiffAt_infty_origin.differentiableAt
      (by norm_num)).hasFDerivAt
  have primitiveDerivative :=
    canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
      (completeJointAdjointTemporalCoordinateCorrection Source Current)
      fixedCoupledAdjointCorrection_contDiffAt_origin
  have totalDerivative := currentDerivative.add primitiveDerivative
  rw [show
    holonomicConjugateMatterCoordinates
        fixedP506L0U6RadialQuarticCoupledTemporalActual =
      holonomicConjugateMatterCoordinates Current +
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Current) by
    funext point
    unfold holonomicConjugateMatterCoordinates
      fixedP506L0U6RadialQuarticCoupledTemporalActual
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
    simp only [Pi.add_apply, matterDualCoordinates_add,
      matterDualCoordinates_matterDualOfCoordinates]]
  exact totalDerivative

/-- The same output actual realizes the source/current-selected adjoint
velocity in its ordinary ambient temporal derivative. -/
theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatterTemporalDerivative_origin :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          fixedP506L0U6RadialQuarticCoupledTemporalActual)
        0 canonicalLorentzianTimeDirection =
      matterDualCoordinates
        (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
          ).adjointVelocity := by
  unfold fieldDirectionalDerivative
  rw [
    fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatterCoordinates_hasFDerivAt_origin.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  have timeProjection :
      canonicalTimeProjection
          (coordinateDirection canonicalLorentzianTimeDirection) = 1 := by
    simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection, localBaseCoordinate_apply]
  rw [timeProjection, one_smul]
  unfold completeJointAdjointTemporalCoordinateCorrection
    fieldDirectionalDerivative
  module

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticCoupledTemporalDevelopment
