import H0mework.Physics.SynchronizedJoint.CoframeContactLorentzClosure
import H0mework.Physics.ElectricJoint.ElectricCartanECSynchronizedGlobalOperator
import H0mework.Physics.ConstrainedCauchy.FixedECFullCauchyLiveStressSpatialRegularity
import H0mework.Physics.ActualGerms.FixedFirstGerm
import H0mework.Physics.QuarticDynamics.FixedScalarMomentumCarry
import H0mework.Physics.IdentityGerms.IdentityECNonlinearLeviCivitaFirstGerm
import H0mework.Physics.FullOccurrence.FixedLorentzClosure
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Fixed P506/L0 synchronized Cartan--EC global actual

This module replaces the old separate Cartan and Einstein--Cartan tail by the
single synchronized contact-native action write:

```text
(source, current)
  -> temporal matter/scalar/adjoint write
  -> P286 algebraic and live-electric writes
  -> one synchronized Cartan--EC coframe/connection write at the canonical
     source occurrence
  -> one global affine-coframe/affine-connection actual.
```

The public operator accepts only `(source,current)`.  The canonical origin is
fixed by the existing spacetime carrier; no residual coordinate, support,
target jet, branch, zero-fiber witness, or free coefficient is accepted.  The
result is one global configuration, not a diagonal of contact-wise worlds.

The fixed specialization consumes the source-generated radial-plus-scalar
current.  At the canonical occurrence its final actual simultaneously closes
the Lorentz equation, the complete coframe equation, and simplicity.  The
all-point whole residual remains a downstream readout and is exposed through
exact spacetime recentering without being fed back into the constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECSynchronizedGlobalActual

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLorentzClosure
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalNaturality
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalLorentzClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginPhysicalRetention
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualFirstGerm
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceGeneratedMatterSpinActionUpdate
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Fixed P506/L0 specialization -/

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

/-- The exact post-MSA/post-P286-live input of the new synchronized tail. -/
def fixedP506L0CartanECSynchronizedPreCartanCurrent :
    StageNineHolonomicConfiguration :=
  completeJointLiveElectricCartanECSynchronizedPreCartanCurrent
    Source Current

/-- The new branch-free common global actual. -/
def fixedP506L0CartanECSynchronizedGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator
    Source Current

theorem fixedP506L0CartanECSynchronizedGlobalActual_eq_actionWrite :
    fixedP506L0CartanECSynchronizedGlobalActual =
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
        Source fixedP506L0CartanECSynchronizedPreCartanCurrent 0 :=
  rfl

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem fixedP506L0CartanECSynchronizedPreCartanCurrent_coframe_origin :
    fixedP506L0CartanECSynchronizedPreCartanCurrent.coframe 0 = 1 := by
  rw [show fixedP506L0CartanECSynchronizedPreCartanCurrent.coframe =
      Current.coframe by rfl]
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_zeroSlice 0

theorem fixedP506L0CartanECSynchronizedPreCartanCurrent_nondegenerate_origin :
    Matrix.det
        (fixedP506L0CartanECSynchronizedPreCartanCurrent.coframe 0) ≠ 0 := by
  rw [fixedP506L0CartanECSynchronizedPreCartanCurrent_coframe_origin]
  norm_num

private theorem u5_coframe_origin : U5.coframe 0 = 1 := by
  rw [fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_zeroSlice 0

theorem fixedP506L0CartanECSynchronizedPreCartanCurrent_connection_skew_origin :
    LorentzSkew
      (fixedP506L0CartanECSynchronizedPreCartanCurrent.gravityConnection 0) := by
  rw [show fixedP506L0CartanECSynchronizedPreCartanCurrent.gravityConnection =
      Current.gravityConnection by rfl,
    show Current.gravityConnection = U6.gravityConnection by rfl]
  change LorentzSkew
    ((sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source U5).gravityConnection 0)
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
      Source U5,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  apply diracDualFormNativeActionCartanConnectionAt_lorentzSkew
  rw [u5_coframe_origin]
  norm_num

/-! ## Exact fixed-lineage coframe first-jet normal form -/

private abbrev SynchronizedEC : StageNineHolonomicConfiguration :=
  diracDualFormNativeCartanECSynchronizedECActual Source
    fixedP506L0CartanECSynchronizedPreCartanCurrent 0

private theorem synchronizedPreCartan_matter_origin_eq_current :
    fixedP506L0CartanECSynchronizedPreCartanCurrent.matter 0 =
      Current.matter 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero]
  change
    (completeJointGlobalTemporalCurrent Source Current).matter
        (canonicalCauchySlicePoint 0 0) =
      Current.matter (canonicalCauchySlicePoint 0 0)
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source Current 0

private theorem synchronizedPreCartan_conjugateMatter_origin_eq_current :
    fixedP506L0CartanECSynchronizedPreCartanCurrent.conjugateMatter 0 =
      Current.conjugateMatter 0 := by
  rw [← canonicalCauchySlicePoint_zero_zero]
  change
    (completeJointGlobalTemporalCurrent Source Current).conjugateMatter
        (canonicalCauchySlicePoint 0 0) =
      Current.conjugateMatter (canonicalCauchySlicePoint 0 0)
  exact
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source Current 0

private theorem synchronizedEC_coframe_origin_eq_reference :
    SynchronizedEC.coframe 0 = positiveSourceTargetMatterActual.coframe 0 := by
  rw [show SynchronizedEC.coframe 0 =
      fixedP506L0CartanECSynchronizedPreCartanCurrent.coframe 0 by rfl,
    fixedP506L0CartanECSynchronizedPreCartanCurrent_coframe_origin]
  rfl

private theorem synchronizedEC_matter_origin_eq_reference :
    SynchronizedEC.matter 0 = positiveSourceTargetMatterActual.matter 0 := by
  rw [show SynchronizedEC.matter 0 =
      fixedP506L0CartanECSynchronizedPreCartanCurrent.matter 0 by rfl,
    synchronizedPreCartan_matter_origin_eq_current,
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic,
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matter_origin_eq_canonical]
  change fixedP506L0P286CanonicalGeneratedActual.matter 0 =
    positiveSourceTargetMatterActual.matter 0
  rw [canonicalGeneratedActual_matter]
  change (fixedP506L0FinalCommonActionActual 0).matter 0 =
    positiveSourceTargetMatterActual.matter 0
  rw [fixedP506L0FinalCommonActionActual_matter_origin]
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
  rw [show SynchronizedEC.conjugateMatter 0 =
      fixedP506L0CartanECSynchronizedPreCartanCurrent.conjugateMatter 0 by rfl,
    synchronizedPreCartan_conjugateMatter_origin_eq_current,
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic,
    fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatter_origin_eq_canonical]
  change fixedP506L0P286CanonicalGeneratedActual.conjugateMatter 0 =
    positiveSourceTargetMatterActual.conjugateMatter 0
  rw [canonicalGeneratedActual_conjugateMatter]
  change (fixedP506L0FinalCommonActionActual 0).conjugateMatter 0 =
    positiveSourceTargetMatterActual.conjugateMatter 0
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter_origin]
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

theorem fixedP506L0CartanECSynchronizedPreCartanCurrent_connection_origin_eq_fixedAction :
    fixedP506L0CartanECSynchronizedPreCartanCurrent.gravityConnection 0 =
      fixedActionCartanConnection := by
  rw [show fixedP506L0CartanECSynchronizedPreCartanCurrent.gravityConnection =
      U6.gravityConnection by rfl]
  rw [
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gravityConnection_eq_preEC,
    ← fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_preEC,
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gravityConnection_origin_eq_jointAction,
    fixedP506JointActionSuccessor_gravityConnection]
  exact fixedP506JointActual_connection_origin_eq_fixedAction

/-- At the exact fixed source occurrence, the synchronized Cartan torsion and
the retained action-generated connection cancel in the canonical coframe
right inverse.  Thus the written affine coframe has the authoritative
identity first jet rather than a new freely selected germ. -/
theorem fixedP506L0CartanECSynchronizedCoframeFirstJet_origin :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source
        fixedP506L0CartanECSynchronizedPreCartanCurrent 0 =
      identityECZeroCoframeFirstJet := by
  apply coframeJet_eq_of_fields_eq
  · rw [show
      (diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source
        fixedP506L0CartanECSynchronizedPreCartanCurrent 0).coframe =
          SynchronizedEC.coframe 0 by rfl,
      synchronizedEC_coframe_origin_eq_reference]
    rfl
  · funext derivativeDirection internal coordinate
    fin_cases derivativeDirection <;> fin_cases internal <;>
      fin_cases coordinate <;>
      simp [diracDualFormNativeCartanECSynchronizedCoframeFirstJet,
        identityECZeroCoframeFirstJet,
        synchronizedEC_actionTorsion_origin_eq_normalForm,
        fixedP506L0CartanECSynchronizedPreCartanCurrent_connection_origin_eq_fixedAction,
        fixedP506L0CartanECSynchronizedPreCartanCurrent_coframe_origin,
        fixedActionCartanConnection_eq_positiveNormalForm,
        positiveDiracDualCartanTorsionNormalForm,
        positiveDiracDualCartanContorsionNormalForm,
        coframeConnectionAction, lorentzSkewConnectionOfBivectorOneForm,
        loweredLorentzBivectorMatrix, orderedCartanTorsionComponent,
        orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
        Fin.sum_univ_six, Matrix.one_apply] <;>
      norm_num

/-- The first jet read from the one generated global actual is exactly the
same fixed-lineage normal form. -/
theorem fixedP506L0CartanECSynchronizedGlobalActual_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt
        fixedP506L0CartanECSynchronizedGlobalActual.coframe 0 =
      identityECZeroCoframeFirstJet := by
  rw [fixedP506L0CartanECSynchronizedGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframeFirstJet_contact,
    fixedP506L0CartanECSynchronizedCoframeFirstJet_origin]

/-- The synchronized origin jet is integrated by the source/current-only
global writer itself.  Because that generated jet is `(I, 0)`, the resulting
primitive coframe is the identity field on all spacetime, not a contact-wise
family or a supplied global extension. -/
theorem fixedP506L0CartanECSynchronizedGlobalActual_coframe_eq_one :
    fixedP506L0CartanECSynchronizedGlobalActual.coframe =
      fun _ => (1 : LorentzianCoframe) := by
  rw [fixedP506L0CartanECSynchronizedGlobalActual_eq_actionWrite]
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet
          Source fixedP506L0CartanECSynchronizedPreCartanCurrent 0) = _
  rw [fixedP506L0CartanECSynchronizedCoframeFirstJet_origin]
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        identityCoframeMatterGeometry = _
  funext point
  simp [cartanECSynchronizedCenteredAffineCoframeField]

theorem fixedP506L0CartanECSynchronizedGlobalActual_coframe_contDiff :
    ContDiff ℝ ∞ fixedP506L0CartanECSynchronizedGlobalActual.coframe := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricCartanECSynchronizedGlobalOperator_coframe_contDiff
      Source Current

/-- Positive same-actual closure at the exact canonical source occurrence. -/
theorem fixedP506L0CartanECSynchronizedGlobalActual_jointCartanECClosure_origin :
    holonomicFormNativeLorentzEulerThreeForm Source 0
          fixedP506L0CartanECSynchronizedGlobalActual 0 = 0 ∧
      diracDualFormNativeCoframeEulerCovector Source 0
          (toContinuumPointField
            fixedP506L0CartanECSynchronizedGlobalActual 0) = 0 ∧
        FormNativeGravitySimplicityEquation
          fixedP506L0CartanECSynchronizedGlobalActual := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_jointCartanECClosure_contact
      Source fixedP506L0CartanECSynchronizedPreCartanCurrent 0
      fixedP506L0CartanECSynchronizedPreCartanCurrent_connection_skew_origin
      fixedP506L0CartanECSynchronizedPreCartanCurrent_nondegenerate_origin

theorem fixedP506L0CartanECSynchronizedGlobalActual_gravityMultiplierResidual_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source
      fixedP506L0CartanECSynchronizedGlobalActual point).gravityMultiplier =
        0 := by
  exact
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
      (fixedP506L0CartanECSynchronizedGlobalActual_jointCartanECClosure_origin.2.2
        point)

theorem fixedP506L0CartanECSynchronizedGlobalActual_lorentzResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source
      fixedP506L0CartanECSynchronizedGlobalActual 0).lorentzConnection = 0 :=
  fixedP506L0CartanECSynchronizedGlobalActual_jointCartanECClosure_origin.1

theorem fixedP506L0CartanECSynchronizedGlobalActual_coframeResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source
      fixedP506L0CartanECSynchronizedGlobalActual 0).coframe = 0 :=
  fixedP506L0CartanECSynchronizedGlobalActual_jointCartanECClosure_origin.2.1

/-! ## One all-point residual readout -/

/-- The complete residual of the one global actual read at each exact
spacetime occurrence through the canonical translated origin. -/
def fixedP506L0CartanECSynchronizedRecenteredWholeResidual
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativePointwiseJointResidual Source
    (fullyRecenterHolonomicConfiguration
      fixedP506L0CartanECSynchronizedGlobalActual point)
    0

theorem fixedP506L0CartanECSynchronizedGlobalActual_actionJet_recenter
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet Source
        (fullyRecenterHolonomicConfiguration
          fixedP506L0CartanECSynchronizedGlobalActual point)
        0 =
      generatedDiracDualFormNativePointwiseActionJet Source
        fixedP506L0CartanECSynchronizedGlobalActual point := by
  exact generatedActionJet_fullyRecenter_origin_unconditional Source
    fixedP506L0CartanECSynchronizedGlobalActual point

theorem fixedP506L0CartanECSynchronizedRecenteredWholeResidual_eq
    (point : BasePoint) :
    fixedP506L0CartanECSynchronizedRecenteredWholeResidual point =
      diracDualFormNativePointwiseJointResidual Source
        fixedP506L0CartanECSynchronizedGlobalActual point := by
  exact pointwiseJointResidual_fullyRecenter_origin_unconditional Source
    fixedP506L0CartanECSynchronizedGlobalActual point

/-- The global hard gate is exactly one all-point read of the same generated
actual.  No matching-contact candidate or assembly certificate is supplied. -/
theorem
    fixedP506L0CartanECSynchronizedGlobalActual_zeroFiber_iff_recenteredWholeResidual
    :
    DiracDualFormNativeJointZeroFiber Source
        fixedP506L0CartanECSynchronizedGlobalActual ↔
      ∀ point,
        fixedP506L0CartanECSynchronizedRecenteredWholeResidual point = 0 := by
  rw [diracDualFormNativeJointZeroFiber_iff_pointwise]
  unfold OnDiracDualFormNativePointwiseJointZeroFiber
  constructor
  · intro zero point
    rw [fixedP506L0CartanECSynchronizedRecenteredWholeResidual_eq]
    exact zero point
  · intro zero point
    rw [← fixedP506L0CartanECSynchronizedRecenteredWholeResidual_eq]
    exact zero point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECSynchronizedGlobalActual
