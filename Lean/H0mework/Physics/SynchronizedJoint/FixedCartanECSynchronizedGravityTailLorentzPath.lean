import H0mework.Physics.SynchronizedJoint.GravityTailLorentzPathOperator
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorCoframeReadback

/-!
# Fixed P506/L0 action-selected gravity-tail specialization

The action-selected scalar/matter/P286 current already carries the fixed
P506/L0 matter content and the primitive Cartan connection value at the
canonical origin.  This module identifies those exact occurrence data with
the earlier synchronized Cartan--EC producer and reuses its generated
`(I,0)` coframe first jet.

The resulting gravity-only three-leg occurrence therefore preserves the
already closed non-gravity fields while generating one global identity
coframe, a radial Lorentz path, and its live reaction.  No residual,
completed target, support coordinate, branch, or coefficient enters the
constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath

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
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev LegacyBase : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev LegacyEC : StageNineHolonomicConfiguration :=
  diracDualFormNativeCartanECSynchronizedECActual Source LegacyBase 0

private abbrev CoupledEC : StageNineHolonomicConfiguration :=
  diracDualFormNativeCartanECSynchronizedECActual Source Coupled 0

private abbrev GravityBase : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Coupled

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-! ## Exact inherited origin data -/

private theorem current_matter_eq_legacyBase :
    Current.matter = LegacyBase.matter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
      Source Input).matter = LegacyBase.matter
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_matter,
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_matter]
  rfl

private theorem current_conjugateMatter_eq_legacyBase :
    Current.conjugateMatter = LegacyBase.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
      Source Input).conjugateMatter = LegacyBase.conjugateMatter
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_conjugateMatter,
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathBase,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_conjugateMatter]
  rfl

private theorem current_gravityConnection_origin_eq_legacyBase :
    Current.gravityConnection 0 = LegacyBase.gravityConnection 0 := by
  calc
    Current.gravityConnection 0 =
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.gravityConnection
          0 :=
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_connection_zero
    _ = LegacyBase.gravityConnection 0 := by
      rw [
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual_eq_actionWrite,
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_connection,
        sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]

private theorem coupled_coframe_eq_one :
    Coupled.coframe = fun _ => (1 : LorentzianCoframe) := by
  calc
    Coupled.coframe = Carry.coframe :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe
        Source Carry
    _ = fun _ => (1 : LorentzianCoframe) :=
      actionSelectedCarry_coframe_eq_one

private theorem coupled_coframe_origin_eq_legacyBase :
    Coupled.coframe 0 = LegacyBase.coframe 0 := by
  calc
    Coupled.coframe 0 = 1 := congrFun coupled_coframe_eq_one 0
    _ = LegacyBase.coframe 0 :=
      fixedP506L0CompleteJointActionSpacetimeSection_coframe_origin.symm

private theorem coupled_gravityConnection_origin_eq_legacyBase :
    Coupled.gravityConnection 0 = LegacyBase.gravityConnection 0 := by
  change Current.gravityConnection 0 = LegacyBase.gravityConnection 0
  exact current_gravityConnection_origin_eq_legacyBase

private theorem coupled_matter_origin_eq_legacyBase :
    Coupled.matter 0 = LegacyBase.matter 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at zeroSlice
  calc
    Coupled.matter 0 = Carry.matter 0 := zeroSlice
    _ = Current.matter 0 := by rfl
    _ = LegacyBase.matter 0 := congrFun current_matter_eq_legacyBase 0

private theorem coupled_conjugateMatter_origin_eq_legacyBase :
    Coupled.conjugateMatter 0 = LegacyBase.conjugateMatter 0 := by
  have zeroSlice :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source Carry (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero_local] at zeroSlice
  calc
    Coupled.conjugateMatter 0 = Carry.conjugateMatter 0 := zeroSlice
    _ = Current.conjugateMatter 0 := by rfl
    _ = LegacyBase.conjugateMatter 0 :=
      congrFun current_conjugateMatter_eq_legacyBase 0

/-! ## Synchronized first-jet reuse -/

private theorem coupledEC_coframe_origin_eq_legacyEC :
    CoupledEC.coframe 0 = LegacyEC.coframe 0 := by
  change Coupled.coframe 0 = LegacyBase.coframe 0
  exact coupled_coframe_origin_eq_legacyBase

private theorem coupledEC_connection_origin_eq_legacyEC :
    CoupledEC.gravityConnection 0 = LegacyEC.gravityConnection 0 := by
  rw [
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]
  exact coupled_gravityConnection_origin_eq_legacyBase

private theorem coupledEC_matter_origin_eq_legacyEC :
    CoupledEC.matter 0 = LegacyEC.matter 0 := by
  change Coupled.matter 0 = LegacyBase.matter 0
  exact coupled_matter_origin_eq_legacyBase

private theorem coupledEC_conjugateMatter_origin_eq_legacyEC :
    CoupledEC.conjugateMatter 0 = LegacyEC.conjugateMatter 0 := by
  change Coupled.conjugateMatter 0 = LegacyBase.conjugateMatter 0
  exact coupled_conjugateMatter_origin_eq_legacyBase

private theorem coupledEC_spinResponse_origin_eq_legacyEC :
    diracDualFormNativeActionSpinResponseAt Source CoupledEC 0 =
      diracDualFormNativeActionSpinResponseAt Source LegacyEC 0 := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
  · exact coupledEC_coframe_origin_eq_legacyEC
  · exact coupledEC_matter_origin_eq_legacyEC
  · exact coupledEC_conjugateMatter_origin_eq_legacyEC

private theorem coupledEC_actionTorsion_origin_eq_legacyEC :
    diracDualFormNativeActionCartanTorsionAt Source CoupledEC 0 =
      diracDualFormNativeActionCartanTorsionAt Source LegacyEC 0 := by
  unfold diracDualFormNativeActionCartanTorsionAt
  rw [coupledEC_coframe_origin_eq_legacyEC,
    coupledEC_spinResponse_origin_eq_legacyEC]

/-- The new gravity tail starts from the exact fixed synchronized `(I,0)`
coframe jet.  This is inherited by equality of the complete action data at
the same canonical occurrence, not by copying a stored jet certificate. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailCoframeFirstJet_origin :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Coupled 0 =
      identityECZeroCoframeFirstJet := by
  calc
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Coupled 0 =
        diracDualFormNativeCartanECSynchronizedCoframeFirstJet
          Source LegacyBase 0 := by
      apply coframeJet_eq_of_fields_eq
      · exact coupledEC_coframe_origin_eq_legacyEC
      · funext derivativeDirection internal coordinate
        simp only [diracDualFormNativeCartanECSynchronizedCoframeFirstJet]
        rw [coupledEC_connection_origin_eq_legacyEC,
          coupledEC_coframe_origin_eq_legacyEC,
          coupledEC_actionTorsion_origin_eq_legacyEC]
    _ = identityECZeroCoframeFirstJet :=
      fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedCoframeFirstJet_origin

/-! ## One global generated gravity-tail actual -/

/-- The unique fixed-lineage gravity-tail occurrence. -/
def fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathOccurrence :
    CartanECSynchronizedGravityTailOccurrence Source Coupled :=
  sourceActionGeneratedCartanECSynchronizedGravityTailOccurrence Source Coupled

/-- One global gravity-only continuation of the exact action-selected
P506/L0 current. -/
def fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathOccurrence.finalActual

theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual_eq_actionWrite :
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual =
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
        Source Coupled :=
  rfl

theorem fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one :
    GravityBase.coframe = fun _ => (1 : LorentzianCoframe) := by
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet
          Source Coupled 0) = _
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailCoframeFirstJet_origin]
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        identityCoframeMatterGeometry = _
  funext point
  simp [cartanECSynchronizedCenteredAffineCoframeField]

/-- At the emitted source occurrence the synchronized gravity prefix keeps
the primitive connection value of the coupled action current.  Only its
generated first jet is changed downstream. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_coupled :
    GravityBase.gravityConnection 0 = Coupled.gravityConnection 0 := by
  change CoupledEC.gravityConnection 0 = Coupled.gravityConnection 0
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact
      Source Coupled 0

/-- The retained primitive value is the fixed source/action Cartan
connection already emitted by the complete-joint spacetime section. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_fixedAction :
    GravityBase.gravityConnection 0 = fixedActionCartanConnection := by
  calc
    GravityBase.gravityConnection 0 = Coupled.gravityConnection 0 :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_gravityConnection_origin_eq_coupled
    _ = LegacyBase.gravityConnection 0 :=
      coupled_gravityConnection_origin_eq_legacyBase
    _ = fixedActionCartanConnection :=
      fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_origin

/-- The public three-leg gravity tail emits one global identity coframe while
retaining the already generated non-gravity fields. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one :
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual.coframe =
      fun _ => (1 : LorentzianCoframe) := by
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_coframe]
  exact
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one

private theorem coupled_gravityConnection_origin_lorentzSkew :
    LorentzSkew (Coupled.gravityConnection 0) := by
  rw [coupled_gravityConnection_origin_eq_legacyBase,
    fixedP506L0CompleteJointActionSpacetimeSection_gravityConnection_origin,
    fixedActionCartanConnection_eq_positiveNormalForm]
  exact lorentzSkewConnectionOfBivectorOneForm_lorentzSkew _

theorem fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_connection_lorentzSkew
    (point : BasePoint) :
    LorentzSkew (GravityBase.gravityConnection point) := by
  change LorentzSkew
    ((diracDualFormNativeCartanECSynchronizedECActual
      Source Coupled 0).gravityConnection point)
  change LorentzSkew
    (coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
      (Coupled.gravityConnection 0)
      (diracDualFormNativeCoframeECContactCurvatureTarget
        Source Coupled 0) point)
  simpa [coframeECContactCenteredNormalizedAffineLorentzConnectionField] using
    normalizedAffineLorentzConnectionField_lorentzSkew
      (Coupled.gravityConnection 0)
      (diracDualFormNativeCoframeECContactCurvatureTarget Source Coupled 0)
      coupled_gravityConnection_origin_lorentzSkew point

/-- Every profile contact sampled by the global path compiler is the native
joint Cartan--EC action output and lies in the local Lorentz/coframe/
simplicity zero fiber. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailProfile_jointClosure
    (contact : BasePoint) :
    let final :=
      cartanECSynchronizedGravityTailProfileContact Source Coupled contact
    holonomicFormNativeLorentzEulerThreeForm Source 0 final 0 = 0 ∧
      diracDualFormNativeCoframeEulerCovector Source 0
          (toContinuumPointField final 0) = 0 ∧
        FormNativeGravitySimplicityEquation final := by
  apply cartanECSynchronizedGravityTailProfileContact_jointClosure
  · exact
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_connection_lorentzSkew
        contact
  · rw [
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_coframe_eq_one]
    norm_num

/-- All nine final projections come from the one exact fixed occurrence. -/
theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_fieldInventory :
    let output :=
      fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual
    output.coframe = GravityBase.coframe ∧
      output.gravityConnection =
        cartanECSynchronizedGravityTailPathConnectionField Source Coupled ∧
      output.gravityAuxiliary = GravityBase.gravityAuxiliary ∧
      output.gravitySimplicityMultiplier =
        formNativeGravityReactionField
          (cartanECSynchronizedGravityTailConnectedActual Source Coupled) ∧
      output.gaugeConnection = Coupled.gaugeConnection ∧
      output.gaugeAuxiliary = Coupled.gaugeAuxiliary ∧
      output.scalar = Coupled.scalar ∧
      output.matter = Coupled.matter ∧
      output.conjugateMatter = Coupled.conjugateMatter := by
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual_eq_actionWrite]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_fieldInventory
      Source Coupled

theorem
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_nondegenerate :
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPathGlobalActual.Nondegenerate := by
  intro point
  rw [
    fixedP506L0ActionSelectedCartanECSynchronizedGravityTailLorentzPath_coframe_eq_one]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedCartanECSynchronizedGravityTailLorentzPath
