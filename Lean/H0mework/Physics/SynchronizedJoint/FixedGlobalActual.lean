import H0mework.Physics.JointVariation.SectionCartanECSynchronizedGlobalOperator
import H0mework.Physics.JointVariation.SectionFixedGlobalRegularity
import H0mework.Physics.FixedJoint.FixedCartanECSynchronizedGlobalActual

/-!
# Fixed P506/L0 smooth synchronized spacetime-section actual

The globally smooth complete-joint P506/L0 spacetime section is fed directly
into one source-owned synchronized Cartan--EC leg.  The two writes are the
exact legs of one source/current-indexed occurrence.  The fixed source data
force the synchronized coframe jet to `(I,0)`, so the emitted coframe is the
global identity field and is nondegenerate everywhere.

The constructor consumes no residual, support, target jet, completed actual,
selector, branch, zero-fiber witness, or free coefficient.  Its all-point
joint residual remains a downstream readout.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanContorsionTorsionEquiv
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506CartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

local instance fixedSynchronizedP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fixedSynchronizedP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance fixedSynchronizedP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Base : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

/-- The exact two-leg occurrence producing the fixed common actual. -/
def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence :
    CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
      Source Input :=
  sourceActionGeneratedCompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
    Source Input

/-- The one global output of the exact occurrence. -/
def fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence.finalActual

@[simp] theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence_after_spacetimeSection :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence.after
        .spacetimeSection =
      Base :=
  rfl

@[simp] theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence_before_cartan :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence.before
        .cartanECSynchronized =
      Base :=
  rfl

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual =
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
        Source Base 0 :=
  rfl

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem canonicalSpatialProjection_zero_local :
    canonicalSpatialProjection (0 : BasePoint) = 0 := by
  exact map_zero canonicalSpatialProjection

private theorem completeJointActionMatchingContactPoint_zero_local :
    completeJointActionMatchingContactPoint 0 = 0 := by
  unfold completeJointActionMatchingContactPoint
  rw [map_zero, canonicalCauchySlicePoint_zero_zero_local]

/-! ## Exact fixed-origin normal form -/

theorem fixedP506L0CompleteJointActionSpacetimeSection_coframe_origin :
    Base.coframe 0 = 1 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      Source Input).coframe 0 = 1
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_coframe_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact 0).coframe
        (completeJointActionMatchingContactPoint 0) = 1
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon,
    canonicalSpatialProjection_zero_local,
    completeJointActionMatchingContactPoint_zero_local,
    fixedP506L0FinalCommonActionActual_coframe_origin]

theorem fixedP506L0CompleteJointActionSpacetimeSection_matter_origin :
    Base.matter 0 = diracSpinTwoMatterProbe := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      Source Input).matter 0 = diracSpinTwoMatterProbe
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_matter_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact 0).matter
        (completeJointActionMatchingContactPoint 0) = diracSpinTwoMatterProbe
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon,
    canonicalSpatialProjection_zero_local,
    completeJointActionMatchingContactPoint_zero_local,
    fixedP506L0FinalCommonActionActual_matter_origin]

theorem fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_origin :
    Base.conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      Source Input).conjugateMatter 0 = diracSpinZeroMatterCoordinate
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_conjugateMatter_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact 0).conjugateMatter
        (completeJointActionMatchingContactPoint 0) =
      diracSpinZeroMatterCoordinate
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon,
    canonicalSpatialProjection_zero_local,
    completeJointActionMatchingContactPoint_zero_local,
    fixedP506L0FinalCommonActionActual_conjugateMatter_origin]

theorem
    fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_origin :
    Base.gravityConnection 0 = fixedActionCartanConnection := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
      Source Input).gravityConnection 0 = fixedActionCartanConnection
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gravityConnection_at]
  change
    (fixedP506L0CompleteJointActionMatchingContact 0).gravityConnection
        (completeJointActionMatchingContactPoint 0) = fixedActionCartanConnection
  rw [fixedP506L0CompleteJointActionMatchingContact_eq_finalCommon,
    canonicalSpatialProjection_zero_local,
    completeJointActionMatchingContactPoint_zero_local,
    fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_jointAction]
  exact fixedP506JointActual_connection_origin_eq_fixedAction

private abbrev SynchronizedEC : StageNineHolonomicConfiguration :=
  diracDualFormNativeCartanECSynchronizedECActual Source Base 0

private theorem synchronizedEC_coframe_origin_eq_reference :
    SynchronizedEC.coframe 0 = positiveSourceTargetMatterActual.coframe 0 := by
  rw [show SynchronizedEC.coframe 0 = Base.coframe 0 by rfl,
    fixedP506L0CompleteJointActionSpacetimeSection_coframe_origin]
  rfl

private theorem synchronizedEC_matter_origin_eq_reference :
    SynchronizedEC.matter 0 = positiveSourceTargetMatterActual.matter 0 := by
  rw [show SynchronizedEC.matter 0 = Base.matter 0 by rfl,
    fixedP506L0CompleteJointActionSpacetimeSection_matter_origin]
  calc
    diracSpinTwoMatterProbe =
        positiveSourceTargetMatterCauchyState.matter 0 :=
      positiveSourceTargetMatterCauchyState_matter.symm
    _ = positiveSourceTargetMatterActual.matter 0 :=
      (sourceActionGeneratedJointLocalActualLift_initialMatter
        Source positiveSourceTargetMatterCauchyState 0).symm

private theorem synchronizedEC_conjugateMatter_origin_eq_reference :
    SynchronizedEC.conjugateMatter 0 =
      positiveSourceTargetMatterActual.conjugateMatter 0 := by
  rw [show SynchronizedEC.conjugateMatter 0 = Base.conjugateMatter 0 by rfl,
    fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_origin]
  calc
    diracSpinZeroMatterCoordinate =
        positiveSourceTargetMatterCauchyState.conjugateMatter 0 :=
      positiveSourceTargetMatterCauchyState_conjugate.symm
    _ = positiveSourceTargetMatterActual.conjugateMatter 0 :=
      (sourceActionGeneratedJointLocalActualLift_initialConjugateMatter
        Source positiveSourceTargetMatterCauchyState 0).symm

private theorem synchronizedEC_spinResponse_origin_eq_fixed :
    diracDualFormNativeActionSpinResponseAt Source SynchronizedEC 0 =
      fixedActionSpinResponse := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
  · exact synchronizedEC_coframe_origin_eq_reference
  · exact synchronizedEC_matter_origin_eq_reference
  · exact synchronizedEC_conjugateMatter_origin_eq_reference

private theorem synchronizedEC_actionTorsion_origin_eq_normalForm :
    diracDualFormNativeActionCartanTorsionAt Source SynchronizedEC 0 =
      positiveDiracDualCartanTorsionNormalForm := by
  unfold diracDualFormNativeActionCartanTorsionAt
  rw [synchronizedEC_coframe_origin_eq_reference,
    synchronizedEC_spinResponse_origin_eq_fixed]
  exact fixedActionCartanTorsion_eq_positiveNormalForm

theorem fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedCoframeFirstJet_origin :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Base 0 =
      identityECZeroCoframeFirstJet := by
  apply coframeJet_eq_of_fields_eq
  · rw [show
      (diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Base 0
        ).coframe = SynchronizedEC.coframe 0 by rfl,
      synchronizedEC_coframe_origin_eq_reference]
    rfl
  · funext derivativeDirection internal coordinate
    fin_cases derivativeDirection <;> fin_cases internal <;>
      fin_cases coordinate <;>
      simp [diracDualFormNativeCartanECSynchronizedCoframeFirstJet,
        identityECZeroCoframeFirstJet,
        synchronizedEC_actionTorsion_origin_eq_normalForm,
        fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_origin,
        fixedP506L0CompleteJointActionSpacetimeSection_coframe_origin,
        fixedActionCartanConnection_eq_positiveNormalForm,
        positiveDiracDualCartanTorsionNormalForm,
        positiveDiracDualCartanContorsionNormalForm,
        coframeConnectionAction, lorentzSkewConnectionOfBivectorOneForm,
        loweredLorentzBivectorMatrix, orderedCartanTorsionComponent,
        orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
        Fin.sum_univ_six, Matrix.one_apply] <;>
      norm_num

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.coframe
        0 = identityECZeroCoframeFirstJet := by
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframeFirstJet_contact,
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedCoframeFirstJet_origin]

/-- The exact occurrence integrates its generated `(I,0)` first jet into one
global identity coframe. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.coframe =
      fun _ => (1 : LorentzianCoframe) := by
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite]
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Base 0) =
      _
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedCoframeFirstJet_origin]
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        identityCoframeMatterGeometry = _
  funext point
  simp [cartanECSynchronizedCenteredAffineCoframeField]

/-- The one emitted coframe is nondegenerate at every spacetime point. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_nondegenerate :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.Nondegenerate := by
  intro point
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_coframe_eq_one]
  norm_num

/-! ## Global nine-field regularity -/

/-- The exact two-leg P506/L0 occurrence emits one globally smooth
nine-field actual. -/
theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_smooth :
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.Smooth := by
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_smooth_of_preCartan_smooth
      Source Input
      fixedP506L0CompleteJointActionSpacetimeSection_smooth

theorem
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual := by
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_simplicity
      Source Input

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
