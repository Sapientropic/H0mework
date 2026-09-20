import H0mework.Physics.SynchronizedJoint.GravityTailJointPathOperator
import H0mework.Physics.SynchronizedJoint.GravityTailJointPathRadialFirstJet
import H0mework.Physics.SynchronizedJoint.GravityTailLorentzPathRadialFirstJet
import H0mework.Physics.SynchronizedJoint.GravityTailProfileLocalRegularity
import H0mework.Physics.ConstrainedCauchy.FixedOriginJointResidual

/-!
# Fixed P506/L0 gravity-tail successor of the constraint+Cauchy current

The already generated constraint+Cauchy current enters the existing
source/current-only Cartan--EC joint path occurrence.  One occurrence emits
the coframe and connection paths, recomputes `B = II+(e)`, and installs the
live reaction.  Its constructor receives no residual, support, target field,
branch, completion payload, or free coefficient.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyOriginJointResidual
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineRadialCurveIntegralFirstJet
open StageNineResidualLinearPlebanskiTorsionReduction
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance gravityTailP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance gravityTailP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance gravityTailP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev GravityBase : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Current

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

/-- The synchronized gravity prefix is seeded by the complete identity
coframe germ already emitted by the constraint/Cauchy current. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeFirstJet_origin :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Current 0 =
      identityCoframeMatterGeometry := by
  apply coframeJet_eq_of_fields_eq
  · unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
    dsimp only
    rw [
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin]
    rfl
  · funext derivativeDirection internal coordinate
    unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
    dsimp only
    have currentNondegenerate : Matrix.det (Current.coframe 0) ≠ 0 := by
      rw [fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin]
      norm_num
    have spinEq :
        diracDualFormNativeActionSpinResponseAt Source
            (diracDualFormNativeCartanECSynchronizedECActual
              Source Current 0) 0 =
          diracDualFormNativeActionSpinResponseAt Source Current 0 := by
      apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      · rw [
          sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe]
      · rfl
      · rfl
    have torsionEq :
        diracDualFormNativeActionCartanTorsionAt Source
            (diracDualFormNativeCartanECSynchronizedECActual
              Source Current 0) 0 =
          diracDualFormNativeActionCartanTorsionAt Source Current 0 := by
      unfold diracDualFormNativeActionCartanTorsionAt
      rw [
        sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
        spinEq]
    have actualTorsion :=
      diracDualFormNativeActionCartanConnectionAt_actualTorsion
        Source Current 0 currentNondegenerate
    rw [
      ← fixedP506L0CartanECConstraintCauchyGlobalActual_gravityConnection_origin_selfGenerated,
      fixedP506L0CartanECConstraintCauchyGlobalActual_coframeFirstJet_origin]
      at actualTorsion
    have actualTorsionEq :
        actualPointwiseCartanTorsionTwoForm identityCoframeMatterGeometry
            (Current.gravityConnection 0) =
          diracDualFormNativeActionCartanTorsionAt Source
            (diracDualFormNativeCartanECSynchronizedECActual
              Source Current 0) 0 :=
      actualTorsion.trans torsionEq.symm
    rw [
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact,
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin,
      ← actualTorsionEq,
      fixedP506L0CartanECConstraintCauchyGlobalActual_gravityConnection_origin_eq_fixedAction]
    fin_cases derivativeDirection <;> fin_cases internal <;>
      fin_cases coordinate <;>
      simp [identityCoframeMatterGeometry, orderedCartanTorsionComponent,
        actualPointwiseCartanTorsionTwoForm, pointwiseCartanTorsion,
        pointwiseCoframeCovariantDerivative, coframeConnectionAction,
        fixedActionCartanConnection_eq_positiveNormalForm,
        positiveDiracDualCartanContorsionNormalForm,
        lorentzSkewConnectionOfBivectorOneForm,
        loweredLorentzBivectorMatrix,
        orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
        Fin.sum_univ_six, Matrix.one_apply] <;>
      norm_num

/-- The fixed-lineage synchronized prefix has the explicit global identity
coframe normal form; no generic regularity theory is needed downstream. -/
theorem fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one :
    GravityBase.coframe = fun _ => (1 : LorentzianCoframe) := by
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet
          Source Current 0) = _
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeFirstJet_origin]
  funext point
  simp [cartanECSynchronizedCenteredAffineCoframeField]

private theorem gravityBase_coframe_contDiff :
    ContDiff ℝ ∞ GravityBase.coframe :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
    Source Current 0

private theorem gravityBase_connection_component_contDiff
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      GravityBase.gravityConnection point direction internalOut internalIn := by
  change ContDiff ℝ ∞ fun point =>
    coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
      _ _ point direction internalOut internalIn
  simpa [coframeECContactCenteredNormalizedAffineLorentzConnectionField] using
    normalizedAffineLorentzConnectionField_smooth _ _
      direction internalOut internalIn

private theorem gravityBase_auxiliary_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      GravityBase.gravityAuxiliary point internalPair spacetimePair := by
  have allCoordinates : ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector (GravityBase.coframe point) :=
    physicalIIPlusBivector_contDiff.comp gravityBase_coframe_contDiff
  exact contDiff_pi.mp
    (contDiff_pi.mp allCoordinates internalPair) spacetimePair

private theorem gravityBase_multiplier_component_contDiff
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      GravityBase.gravitySimplicityMultiplier point
        internalPair spacetimePair := by
  change ContDiff ℝ ∞ fun point =>
    formNativeGravityReactionField
      (StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift.diracDualFormNativeCartanECSynchronizedCoframePreparedActual
        Source Current 0)
      point internalPair spacetimePair
  apply formNativeGravityReactionField_component_contDiff
  · intro direction internalOut internalIn
    exact gravityBase_connection_component_contDiff
      direction internalOut internalIn
  · intro first second
    exact gravityBase_auxiliary_component_contDiff first second

@[simp] theorem
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_zero :
    GravityBase.coframe 0 = (1 : LorentzianCoframe) := by
  unfold GravityBase cartanECSynchronizedGravityTailBase
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  exact fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin

/-- The action prefix consumed by the joint path is one genuine smooth
nine-field actual; no regularity proxy replaces its live reaction. -/
theorem fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth :
    GravityBase.Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact contDiff_pi.mp (contDiff_pi.mp gravityBase_coframe_contDiff row)
      column
  · exact gravityBase_connection_component_contDiff
  · exact gravityBase_auxiliary_component_contDiff
  · exact gravityBase_multiplier_component_contDiff
  · intro direction
    change ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Prepared.gaugeConnection point direction)
    exact fixedP506L0CartanECConstraintPreparedActual_smooth.2.2.2.2.1
      direction
  · intro pair
    change ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv (Prepared.gaugeAuxiliary point pair)
    exact fixedP506L0CartanECConstraintPreparedActual_smooth.2.2.2.2.2.1
      pair
  · change ContDiff ℝ ∞ Prepared.scalar
    exact fixedP506L0CartanECConstraintPreparedActual_smooth.2.2.2.2.2.2.1
  · change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (Prepared.matter point)
    exact fixedP506L0CartanECConstraintPreparedActual_smooth.2.2.2.2.2.2.2.1
  · intro index
    rw [show GravityBase.conjugateMatter = Current.conjugateMatter by
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_conjugateMatter
          Source Current 0]
    rw [fixedP506L0CartanECConstraintCauchyGlobalActual_conjugateMatter_eq_prepared]
    exact
      fixedP506L0CartanECConstraintPreparedActual_smooth.2.2.2.2.2.2.2.2
        index

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiffAt_origin :
    ContDiffAt ℝ 0
      (cartanECSynchronizedGravityTailJetCLM Source Current) 0 :=
  (cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt
    Source Current
    fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth 0 (by simp)
    ).of_le (by norm_num)

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiffAt_origin
    (internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current contact internal coordinate) 0 :=
  (cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    Source Current
    fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth 0 (by simp)
    internal coordinate).of_le (by norm_num)

/-- Fixed-lineage all-point regularity follows directly from the explicit
identity-coframe normal form. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ 1 fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current contact internal coordinate := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    Source Current
    fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth
    contact (by
      rw [
        fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
      norm_num)
    internal coordinate

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiff :
    ContDiff ℝ 1
      (cartanECSynchronizedGravityTailJetCLM Source Current) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact cartanECSynchronizedGravityTailLorentzJetCLM_contDiffAt
    Source Current
    fixedP506L0CartanECConstraintCauchyGravityTailBase_smooth
    contact (by
      rw [
        fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
      norm_num)

/-! ## Fixed Cauchy-slice coframe potential realization -/

private theorem gravityTailCanonicalSlice_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem gravityTailCanonicalSlice_zero_smul
    (scale : ℝ) (space : StageNineSpatialPoint) :
    scale • canonicalCauchySlicePoint 0 space =
      canonicalCauchySlicePoint 0 (scale • space) := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem gravityTailCurrent_matter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    Current.matter (canonicalCauchySlicePoint 0 space) =
      diracSpinTwoMatterProbe := by
  change
    fixedP506L0CartanECCauchyTemporalInput.matter
        (canonicalCauchySlicePoint 0 space) = _
  exact
    fixedP506L0ActionSelectedGravityTailBase_matter_zeroSlice_constant space

private theorem gravityTailCurrent_conjugateMatter_zeroSlice_constant
    (space : StageNineSpatialPoint) :
    Current.conjugateMatter (canonicalCauchySlicePoint 0 space) =
      diracSpinZeroMatterCoordinate := by
  change
    fixedP506L0CartanECCauchyTemporalInput.conjugateMatter
        (canonicalCauchySlicePoint 0 space) = _
  exact
    fixedP506L0ActionSelectedGravityTailBase_conjugateMatter_zeroSlice_constant
      space

private theorem gravityTailBase_spinResponse_zeroSlice_eq_origin
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionSpinResponseAt Source GravityBase
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionSpinResponseAt Source GravityBase 0 := by
  apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
  · rw [
      fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
  · change
      Current.matter (canonicalCauchySlicePoint 0 space) = Current.matter 0
    rw [gravityTailCurrent_matter_zeroSlice_constant]
    rw [← gravityTailCanonicalSlice_zero_zero]
    rw [gravityTailCurrent_matter_zeroSlice_constant]
  · change
      Current.conjugateMatter (canonicalCauchySlicePoint 0 space) =
        Current.conjugateMatter 0
    rw [gravityTailCurrent_conjugateMatter_zeroSlice_constant]
    rw [← gravityTailCanonicalSlice_zero_zero]
    rw [gravityTailCurrent_conjugateMatter_zeroSlice_constant]

private theorem gravityTailBase_actionTorsion_zeroSlice_eq_origin
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanTorsionAt Source GravityBase
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionCartanTorsionAt Source GravityBase 0 := by
  unfold diracDualFormNativeActionCartanTorsionAt
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one,
    gravityTailBase_spinResponse_zeroSlice_eq_origin]

/-- The exact constraint/Cauchy gravity base carries one constant
source-generated Cartan torsion along the complete initial slice. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailBase_actionCartanTorsion_zeroSlice_eq_origin
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanTorsionAt
        positiveSmoothUnifiedSource
        (cartanECSynchronizedGravityTailBase positiveSmoothUnifiedSource
          fixedP506L0CartanECConstraintCauchyGlobalActual)
        (canonicalCauchySlicePoint 0 space) =
      diracDualFormNativeActionCartanTorsionAt
        positiveSmoothUnifiedSource
        (cartanECSynchronizedGravityTailBase positiveSmoothUnifiedSource
          fixedP506L0CartanECConstraintCauchyGlobalActual)
        0 := by
  simpa [Source, Current, GravityBase] using
    gravityTailBase_actionTorsion_zeroSlice_eq_origin space

private theorem gravityTailProfileCoframeFirstJet_origin_derivative_zero
    (derivativeDirection internal coordinate : LorentzianIndex) :
    (cartanECSynchronizedGravityTailProfileCoframeFirstJet
      Source Current 0).derivative derivativeDirection internal coordinate =
      0 := by
  rw [
    cartanECSynchronizedGravityTailProfileCoframeFirstJet_zero_eq_baseFirstJet]
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
  simp [holonomicCoframeFirstJetAt]

private theorem gravityTailProfileCoframeFirstJet_zeroSlice_row
    (scale : ℝ)
    (space : StageNineSpatialPoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    (cartanECSynchronizedGravityTailProfileCoframeFirstJet
        Source Current
        (scale • canonicalCauchySlicePoint 0 space)).derivative
        derivativeDirection internal coordinate =
      -(GravityBase.gravityConnection
          (scale • canonicalCauchySlicePoint 0 space)
          derivativeDirection internal coordinate -
        GravityBase.gravityConnection 0
          derivativeDirection internal coordinate) := by
  have torsionEq :=
    gravityTailBase_actionTorsion_zeroSlice_eq_origin (scale • space)
  rw [← gravityTailCanonicalSlice_zero_smul] at torsionEq
  rw [
    cartanECSynchronizedGravityTailProfileCoframeFirstJet_derivative_normalForm,
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one,
    torsionEq]
  have originZero :=
    gravityTailProfileCoframeFirstJet_origin_derivative_zero
      derivativeDirection internal coordinate
  rw [
    cartanECSynchronizedGravityTailProfileCoframeFirstJet_derivative_normalForm,
    fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
      at originZero
  simp [coframeConnectionAction, Matrix.one_apply]
      at originZero ⊢
  linarith

/-- The fixed synchronized gravity base carries exactly the normalized-affine
connection generated from the current's origin value and its source-native
origin EC target. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine :
    GravityBase.gravityConnection =
      normalizedAffineLorentzConnectionField
        (Current.gravityConnection 0)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          Source Current 0) := by
  funext point formDirection internalOut internalIn
  simp [GravityBase, cartanECSynchronizedGravityTailBase,
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift,
    diracDualFormNativeCartanECSynchronizedCoframePreparedActual,
    diracDualFormNativeCartanECSynchronizedECActual,
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift,
    diracDualFormNativeCoframeECContactConnectedActual,
    diracDualFormNativeCoframeECContactPreparedActual,
    coframeECContactCenteredNormalizedAffineLorentzConnectionField]

/-- Recentring does not introduce a second target: the occurrence profile
target is exactly the source-native EC target recomputed from the generated
gravity base at the sampled contact. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailProfileTarget_eq_baseContactTarget
    (contact : BasePoint) :
    cartanECSynchronizedGravityTailProfileTarget Source Current contact =
      diracDualFormNativeCoframeECContactCurvatureTarget
        Source GravityBase contact := by
  unfold cartanECSynchronizedGravityTailProfileTarget
    diracDualFormNativeCoframeECContactCurvatureTarget
    diracDualFormNativeCoframeECContactLoad
  rw [cartanECSynchronizedGravityTailProfilePreparedCurvature_eq_base]
  rw [cartanECSynchronizedGravityTailProfileField_eq_base]
  rw [show
      (cartanECSynchronizedGravityTailProfileInput Source Current contact
        ).coframe 0 = GravityBase.coframe contact by
    exact fullyRecenterHolonomicConfiguration_coframe_origin
      GravityBase contact]
  rw [diracDualFormNativeCoframeMatterEulerCovector_point_independent
    Source contact]

private theorem gravityTailBase_connection_origin_eq_current :
    GravityBase.gravityConnection 0 = Current.gravityConnection 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]
  exact normalizedAffineLorentzConnectionField_zero _ _

private theorem normalizedAffineConnection_scaled_radial_increment_zero
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (scale : ℝ)
    (point : BasePoint)
    (internal coordinate : LorentzianIndex) :
    (∑ direction : LorentzianIndex,
      (normalizedAffineLorentzConnectionField omega0 target (scale • point)
          direction internal coordinate -
        omega0 direction internal coordinate) * point direction) = 0 := by
  fin_cases internal <;> fin_cases coordinate <;>
    simp [normalizedAffineLorentzConnectionField,
      normalizedAffineBivectorOneForm,
      normalizedAffineBivectorComponentLinear,
      normalizedDerivativeBivector,
      originLorentzBracketCurvature,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, baseCoordinate,
      Fin.sum_univ_four, Fin.sum_univ_six] <;>
    ring

private theorem gravityTailCoframeJetCoordinateCLM_zeroSlice_radial
    (scale : ℝ)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current (scale • canonicalCauchySlicePoint 0 space)
        internal coordinate (canonicalCauchySlicePoint 0 space) = 0 := by
  have radial :=
    normalizedAffineConnection_scaled_radial_increment_zero
      (Current.gravityConnection 0)
      (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0)
      scale (canonicalCauchySlicePoint 0 space) internal coordinate
  rw [←
    fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]
      at radial
  rw [← gravityTailBase_connection_origin_eq_current] at radial
  unfold cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
    cartanECSynchronizedGravityTailCoframeJetOneForm
  simp only [Fin.sum_univ_four, add_apply,
    ContinuousLinearMap.smulRight_apply, baseCoordinate_apply]
  rw [gravityTailProfileCoframeFirstJet_zeroSlice_row,
    gravityTailProfileCoframeFirstJet_zeroSlice_row,
    gravityTailProfileCoframeFirstJet_zeroSlice_row,
    gravityTailProfileCoframeFirstJet_zeroSlice_row]
  rw [Fin.sum_univ_four] at radial
  linear_combination -radial

/-- On the complete initial Cauchy slice, the fixed synchronized coframe
one-form has zero radial integral.  This is the coframe half of the
source-native radial-potential realization, derived from the actual
zero-slice matter fields and the generated normalized-affine connection. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialIncrement_zeroSlice
    (space : StageNineSpatialPoint) :
    cartanECSynchronizedGravityTailCoframeRadialIncrement
        Source Current (canonicalCauchySlicePoint 0 space) = 0 := by
  funext internal coordinate
  simp [cartanECSynchronizedGravityTailCoframeRadialIncrement,
    curveIntegral_segment, AffineMap.lineMap_apply,
    gravityTailCoframeJetCoordinateCLM_zeroSlice_radial]

private theorem gravityTailCoframePath_coordinate_spatialDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (internal coordinate : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          cartanECSynchronizedGravityTailCoframePathField
            Source Current point internal coordinate)
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  let field : BasePoint → ℝ := fun point =>
    cartanECSynchronizedGravityTailCoframePathField
      Source Current point internal coordinate
  have fieldDifferentiable : DifferentiableAt ℝ field
      (canonicalCauchySlicePoint 0 space) :=
    (cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_of_contDiff
      Source Current internal coordinate
      (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
        internal coordinate)
      (canonicalCauchySlicePoint 0 space)).differentiableAt
  have sliceDerivative :=
    fieldDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt 0 space)
  have sliceConstant :
      field ∘ canonicalCauchySlicePoint 0 =
        Function.const StageNineSpatialPoint
          ((1 : LorentzianCoframe) internal coordinate) := by
    funext candidate
    change
      ((GravityBase.coframe 0 +
          cartanECSynchronizedGravityTailCoframeRadialIncrement
            Source Current (canonicalCauchySlicePoint 0 candidate))
        internal coordinate) =
        (1 : LorentzianCoframe) internal coordinate
    rw [
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialIncrement_zeroSlice,
      fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_eq_one]
    simp
  have sliceFderivZero :
      fderiv ℝ (field ∘ canonicalCauchySlicePoint 0) space = 0 := by
    rw [sliceConstant]
    simp
  rw [sliceDerivative.fderiv] at sliceFderivZero
  have applied := congrArg
    (fun derivative : StageNineSpatialPoint →L[ℝ] ℝ =>
      derivative (canonicalSpatialCoordinateDirection axis))
    sliceFderivZero
  unfold fieldDirectionalDerivative
  simpa [field, ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection] using applied

/-- On the complete initial slice, the emitted coframe value is already
constant, so every transverse first-jet defect is exactly the corresponding
displacement of the same generated normalized-affine Base connection. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDerivativeDefect_zeroSlice_eq_baseConnectionDisplacement
    (space : StageNineSpatialPoint)
    (axis : Fin 3)
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDerivativeDefect
        Source Current (canonicalCauchySlicePoint 0 space)
        axis.succ internal coordinate =
      GravityBase.gravityConnection (canonicalCauchySlicePoint 0 space)
          axis.succ internal coordinate -
        GravityBase.gravityConnection 0 axis.succ internal coordinate := by
  have emittedDerivative :
      (cartanECSynchronizedGravityTailCoframeRadialFirstJet
          Source Current (canonicalCauchySlicePoint 0 space)).derivative
          axis.succ internal coordinate = 0 := by
    change
      cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
          Source Current (canonicalCauchySlicePoint 0 space)
          internal coordinate (coordinateDirection axis.succ) = 0
    have pathDerivative :=
      gravityTailCoframePath_coordinate_spatialDerivative_zeroSlice
        space axis internal coordinate
    unfold fieldDirectionalDerivative at pathDerivative
    rw [
      (cartanECSynchronizedGravityTailCoframePathField_coordinate_hasFDerivAt_of_contDiff
        Source Current internal coordinate
        (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
          internal coordinate)
        (canonicalCauchySlicePoint 0 space)).fderiv]
      at pathDerivative
    exact pathDerivative
  rw [
    cartanECSynchronizedGravityTailCoframeRadialFirstJet_derivative_eq_profile_add_defect]
      at emittedDerivative
  have profileRow :=
    gravityTailProfileCoframeFirstJet_zeroSlice_row
      (scale := 1) (space := space) axis.succ internal coordinate
  simp only [one_smul] at profileRow
  rw [profileRow] at emittedDerivative
  linarith

/-! ## Fixed all-point connection-potential normal form -/

private def gravityTailOriginLorentzJetOneForm
    (derivativeDirection : LorentzianIndex) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    ∑ spacetimePair : Fin 6,
      normalizedDerivativeBivector
          (Current.gravityConnection 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget
            Source Current 0)
          internalPair spacetimePair *
        orientedLorentzBivectorBasisCoefficient spacetimePair
          derivativeDirection formDirection

private def gravityTailOriginLorentzJetCLM :
    BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∑ derivativeDirection : LorentzianIndex,
    (baseCoordinate derivativeDirection).smulRight
      (gravityTailOriginLorentzJetOneForm derivativeDirection)

private theorem gravityTailOriginLorentzJetCLM_apply
    (point : BasePoint) :
    gravityTailOriginLorentzJetCLM point =
      normalizedAffineBivectorOneForm
        (Current.gravityConnection 0)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          Source Current 0)
        point := by
  ext formDirection internalPair
  unfold gravityTailOriginLorentzJetCLM
    gravityTailOriginLorentzJetOneForm
    normalizedAffineBivectorOneForm
    normalizedAffineBivectorComponentLinear
  simp [Fin.sum_univ_four, Fin.sum_univ_six,
    ContinuousLinearMap.smulRight_apply, baseCoordinate_apply]
  ring

/-- Typed physical residual between the local source-generated Cartan--EC
profile derivative and the derivative already fixed at the initial
occurrence.  It receives only the contact; both normalized derivatives are
recomputed from the fixed source/current. -/
def
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
    (contact : BasePoint) : PhysicalBivector :=
  normalizedDerivativeBivector
      (cartanECSynchronizedGravityTailProfileOrigin Source Current contact)
      (cartanECSynchronizedGravityTailProfileTarget Source Current contact) -
    normalizedDerivativeBivector
      (Current.gravityConnection 0)
      (diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0)

/-- Exact Stage-9 producer contract for the typed drift.  Vanishing is
equivalent to propagation of the fixed source-native Cartan--EC target by the
actual connection-bracket change; neither side is accepted as an input to the
writer. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift_zero_iff_target_eq_originTarget_add_bracketDrift
    (contact : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
          contact = 0 ↔
      cartanECSynchronizedGravityTailProfileTarget Source Current contact =
        diracDualFormNativeCoframeECContactCurvatureTarget Source Current 0 -
          originLorentzBracketCurvature (Current.gravityConnection 0) +
          originLorentzBracketCurvature
            (cartanECSynchronizedGravityTailProfileOrigin
              Source Current contact) := by
  constructor
  · intro driftZero
    funext internalPair spacetimePair
    have coordinateZero :=
      congrFun (congrFun driftZero internalPair) spacetimePair
    unfold
      fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
      normalizedDerivativeBivector at coordinateZero
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] at coordinateZero
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith
  · intro targetPropagation
    funext internalPair spacetimePair
    have coordinatePropagation :=
      congrFun (congrFun targetPropagation internalPair) spacetimePair
    simp only [Pi.sub_apply, Pi.add_apply] at coordinatePropagation
    unfold
      fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
      normalizedDerivativeBivector
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    rw [coordinatePropagation]
    ring

private def gravityTailProfileLorentzJetDriftOneForm
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    ∑ spacetimePair : Fin 6,
      fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
          contact internalPair spacetimePair *
        orientedLorentzBivectorBasisCoefficient spacetimePair
          derivativeDirection formDirection

private def gravityTailProfileLorentzJetDriftCLM
    (contact : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∑ derivativeDirection : LorentzianIndex,
    (baseCoordinate derivativeDirection).smulRight
      (gravityTailProfileLorentzJetDriftOneForm
        contact derivativeDirection)

private theorem gravityTailProfileNormalizedDerivative_eq_origin_add_drift
    (contact : BasePoint) :
    normalizedDerivativeBivector
        (cartanECSynchronizedGravityTailProfileOrigin Source Current contact)
        (cartanECSynchronizedGravityTailProfileTarget Source Current contact) =
      normalizedDerivativeBivector
          (Current.gravityConnection 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget
            Source Current 0) +
        fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
          contact := by
  unfold
    fixedP506L0CartanECConstraintCauchyGravityTailProfileNormalizedDerivativeDrift
  abel

private theorem gravityTailProfileLorentzJetOneForm_eq_origin_add_drift
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    cartanECSynchronizedGravityTailJetOneForm
        Source Current contact derivativeDirection =
      gravityTailOriginLorentzJetOneForm derivativeDirection +
        gravityTailProfileLorentzJetDriftOneForm
          contact derivativeDirection := by
  funext formDirection internalPair
  unfold cartanECSynchronizedGravityTailJetOneForm
    gravityTailOriginLorentzJetOneForm
    gravityTailProfileLorentzJetDriftOneForm
  rw [cartanECSynchronizedGravityTailLoweredConnectionFirstJet_normalForm,
    gravityTailProfileNormalizedDerivative_eq_origin_add_drift]
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  ring

private theorem gravityTailProfileLorentzJetCLM_eq_origin_add_drift
    (contact : BasePoint) :
    cartanECSynchronizedGravityTailJetCLM Source Current contact =
      gravityTailOriginLorentzJetCLM +
        gravityTailProfileLorentzJetDriftCLM contact := by
  unfold cartanECSynchronizedGravityTailJetCLM
    gravityTailOriginLorentzJetCLM
    gravityTailProfileLorentzJetDriftCLM
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [gravityTailProfileLorentzJetOneForm_eq_origin_add_drift]
  apply ContinuousLinearMap.ext
  intro point
  simp

private theorem gravityTailLorentzJet_curveIntegrable_segment
    (point : BasePoint) :
    CurveIntegrable
      (cartanECSynchronizedGravityTailJetCLM Source Current)
      (Path.segment (0 : BasePoint) point) := by
  rw [curveIntegrable_segment]
  have pathContinuous : Continuous fun parameter : ℝ =>
      AffineMap.lineMap (0 : BasePoint) point parameter := by
    fun_prop
  have coefficientContinuous : Continuous fun parameter : ℝ =>
      cartanECSynchronizedGravityTailJetCLM Source Current
        (AffineMap.lineMap (0 : BasePoint) point parameter) :=
    fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiff.continuous.comp
      pathContinuous
  exact
    (coefficientContinuous.clm_apply continuous_const).intervalIntegrable 0 1

private theorem gravityTailOriginLorentzJet_curveIntegrable_segment
    (point : BasePoint) :
    CurveIntegrable (fun _ : BasePoint => gravityTailOriginLorentzJetCLM)
      (Path.segment (0 : BasePoint) point) := by
  rw [curveIntegrable_segment]
  exact continuous_const.intervalIntegrable 0 1

/-- The only non-affine part of the fixed connection writer: the curve
integral generated from the typed normalized-derivative drift above.  No
equation, target field, or settlement receipt is accepted here. -/
def
    fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
    (point : BasePoint) : LorentzBivectorOneForm :=
  ∫ᶜ contact in Path.segment (0 : BasePoint) point,
    gravityTailProfileLorentzJetDriftCLM contact

private theorem gravityTailProfileLorentzJetDriftCLM_eq_sub
    (contact : BasePoint) :
    gravityTailProfileLorentzJetDriftCLM contact =
      cartanECSynchronizedGravityTailJetCLM Source Current contact -
        gravityTailOriginLorentzJetCLM := by
  rw [gravityTailProfileLorentzJetCLM_eq_origin_add_drift]
  abel

private theorem gravityTailProfileLorentzJetDrift_curveIntegrable_segment
    (point : BasePoint) :
    CurveIntegrable
      gravityTailProfileLorentzJetDriftCLM
      (Path.segment (0 : BasePoint) point) := by
  rw [show gravityTailProfileLorentzJetDriftCLM =
      (cartanECSynchronizedGravityTailJetCLM Source Current) -
        fun _ : BasePoint => gravityTailOriginLorentzJetCLM by
    funext contact
    exact gravityTailProfileLorentzJetDriftCLM_eq_sub contact]
  exact (gravityTailLorentzJet_curveIntegrable_segment point).sub
    (gravityTailOriginLorentzJet_curveIntegrable_segment point)

private theorem gravityTailRadialIncrement_eq_affine_add_profileJetDrift
    (point : BasePoint) :
    cartanECSynchronizedGravityTailRadialIncrement Source Current point =
      normalizedAffineBivectorOneForm
          (Current.gravityConnection 0)
          (diracDualFormNativeCoframeECContactCurvatureTarget
            Source Current 0)
          point +
        fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
          point := by
  unfold cartanECSynchronizedGravityTailRadialIncrement
    fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
  rw [show
      (cartanECSynchronizedGravityTailJetCLM Source Current) =
        (fun _ : BasePoint => gravityTailOriginLorentzJetCLM) +
          gravityTailProfileLorentzJetDriftCLM by
    funext contact
    exact gravityTailProfileLorentzJetCLM_eq_origin_add_drift contact]
  rw [curveIntegral_add
    (gravityTailOriginLorentzJet_curveIntegrable_segment point)
    (gravityTailProfileLorentzJetDrift_curveIntegrable_segment point)]
  rw [curveIntegral_segment_const, gravityTailOriginLorentzJetCLM_apply]
  simp

/-- Exact source-native normal form for the fixed connection writer.  Its
normalized-affine geometry closes unconditionally; the remaining physical
connection displacement is precisely the skew image of the same-path profile
jet drift generated above. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailRadialConnectionDisplacementDefect_eq_profileLorentzJetDrift
    (point : BasePoint) :
    lorentzSkewConnectionOfBivectorOneForm
        (cartanECSynchronizedGravityTailRadialIncrement
          Source Current point) -
        (GravityBase.gravityConnection point -
          GravityBase.gravityConnection 0) =
      lorentzSkewConnectionOfBivectorOneForm
        (fixedP506L0CartanECConstraintCauchyGravityTailProfileLorentzJetDriftRadialIncrement
          point) := by
  rw [gravityTailRadialIncrement_eq_affine_add_profileJetDrift]
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailBase_gravityConnection_eq_normalizedAffine]
  funext formDirection internalOut internalIn
  simp [normalizedAffineLorentzConnectionField,
    lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

/-- The exact next occurrence, indexed by the fixed source and the complete
constraint+Cauchy current before any field is emitted. -/
def fixedP506L0CartanECConstraintCauchyGravityTailJointPathOccurrence :
    CartanECSynchronizedGravityTailJointOccurrence Source Current :=
  sourceActionGeneratedCartanECSynchronizedGravityTailJointOccurrence
    Source Current

/-- The single common actual emitted by that occurrence. -/
def fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGravityTailJointPathOccurrence.finalActual

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite :
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual =
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator
        Source Current :=
  rfl

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt
        fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.coframe
        0 =
      cartanECSynchronizedGravityTailProfileCoframeFirstJet
        Source Current 0 := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe,
    holonomicCoframeFirstJetAt_cartanECSynchronizedGravityTailCoframePathField_zero_of_contDiffAt
      Source Current
      fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiffAt_origin]
  exact cartanECSynchronizedGravityTailCoframeRadialFirstJet_zero_eq_profile
    Source Current

/-- The emitted common successor preserves the closed current's complete
identity coframe first jet at the canonical occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_origin_eq_identity :
    holonomicCoframeFirstJetAt
        fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.coframe
        0 =
      identityCoframeMatterGeometry := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_origin,
    cartanECSynchronizedGravityTailProfileCoframeFirstJet_zero_eq_baseFirstJet]
  change
    holonomicCoframeFirstJetAt
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
          Source Current 0).coframe 0 = _
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframeFirstJet_contact]
  exact
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeFirstJet_origin

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_loweredConnectionFirstJet_origin
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual
          0 derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cartanECSynchronizedGravityTailJetOneForm
        Source Current 0 derivativeDirection formDirection internalPair := by
  unfold gravityConnectionDerivative
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection]
  rw [
    cartanECSynchronizedGravityTailPathConnectionField_loweredFirstJet_zero_of_contDiffAt
      Source Current
      fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiffAt_origin]
  exact congrArg (fun oneForm => oneForm formDirection internalPair)
    (cartanECSynchronizedGravityTailJetCLM_coordinate
      Source Current 0 derivativeDirection)

@[simp] theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframe_zero :
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.coframe
        0 =
      (1 : LorentzianCoframe) := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_coframe,
    cartanECSynchronizedGravityTailCoframePathField_zero]
  change GravityBase.coframe 0 = 1
  exact fixedP506L0CartanECConstraintCauchyGravityTailBase_coframe_zero

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_simplicity
      Source Current

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual := by
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_auxiliaryEquation
      Source Current

/-! ## All-point radial first-jet readback -/

/-- The complete coframe exactification defect vanishes at the radial source.
This is the full continuous-linear map, not only its radial evaluation. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetDefect_origin_zero
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
        Source Current 0 internal coordinate = 0 := by
  unfold cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
  exact radialCurveIntegralFirstJetDefect_zero_of_contDiff
    (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current contact internal coordinate)
    (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
      internal coordinate)

/-- The exactification defect is generated by the same occurrence-native
Lorentz path.  It records only the difference between the emitted radial
first jet and the sampled endpoint profile. -/
def fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect
    (point : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  radialCurveIntegralFirstJetDefect
    (cartanECSynchronizedGravityTailJetCLM Source Current) point

/-- The emitted Lorentz first jet splits into its endpoint profile and the
source-generated exactification defect. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailRadialFirstJet_eq_profile_add_defect
    (point : BasePoint) :
    cartanECSynchronizedGravityTailRadialFirstJet Source Current point =
      cartanECSynchronizedGravityTailJetCLM Source Current point +
        fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect
          point := by
  unfold cartanECSynchronizedGravityTailRadialFirstJet
    fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect
  exact radialCurveIntegralFirstJet_eq_endpoint_add_defect
    (cartanECSynchronizedGravityTailJetCLM Source Current) point

/-- Radial direction is already exact at every spacetime point. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect_apply_point
    (point : BasePoint) :
    fixedP506L0CartanECConstraintCauchyGravityTailRadialExactificationDefect
        point point = 0 := by
  exact radialCurveIntegralFirstJetDefect_apply_radial
    (cartanECSynchronizedGravityTailJetCLM Source Current)
    fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiff point

/-- Endpoint profile readout in the radial direction, with no closedness
premise. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailRadialFirstJet_apply_point
    (point : BasePoint) :
    cartanECSynchronizedGravityTailRadialFirstJet
        Source Current point point =
      cartanECSynchronizedGravityTailJetCLM Source Current point point := by
  unfold cartanECSynchronizedGravityTailRadialFirstJet
  exact radialCurveIntegralFirstJetCLM_apply_radial
    (cartanECSynchronizedGravityTailJetCLM Source Current)
    fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiff point

/-- Every coframe coordinate of the emitted common actual has the same
radial endpoint readout. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailCoframeRadialFirstJetCoordinate_apply_point
    (point : BasePoint)
    (internal coordinate : LorentzianIndex) :
    cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
        Source Current point internal coordinate point =
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current point internal coordinate point := by
  unfold cartanECSynchronizedGravityTailCoframeRadialFirstJetCoordinate
  exact radialCurveIntegralFirstJetCLM_apply_radial
    (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Current contact internal coordinate)
    (fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
      internal coordinate)
    point

/-- Complete all-point coframe first jet of the same emitted common actual. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_coframeFirstJet_eq_radialFirstJet
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.coframe
        point =
      cartanECSynchronizedGravityTailCoframeRadialFirstJet
        Source Current point := by
  exact
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathOccurrence.coframeFirstJet_eq_radialFirstJet
      (fun internal coordinate =>
        fixedP506L0CartanECConstraintCauchyGravityTailCoframeJetCoordinateCLM_contDiff
          internal coordinate)
      point

/-- Complete all-point lowered connection first jet of the same emitted
common actual. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_loweredConnectionFirstJet_eq_radialFirstJet
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cartanECSynchronizedGravityTailRadialFirstJet
        Source Current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  unfold gravityConnectionDerivative
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailJointPathOperator_gravityConnection]
  exact
    cartanECSynchronizedGravityTailPathConnectionField_loweredFirstJet_eq_radialFirstJet
      Source Current
      fixedP506L0CartanECConstraintCauchyGravityTailLorentzJetCLM_contDiff
      point derivativeDirection formDirection internalPair

/-- Ordinary derivative form recovered from the exact lowered radial jet. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_gravityConnectionDerivative_eq_radialFirstJet
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    gravityConnectionDerivative
        fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual
        point derivativeDirection formDirection
        (pairFirst internalPair) (pairSecond internalPair) =
      minkowskiInternalSign (pairFirst internalPair) *
        cartanECSynchronizedGravityTailRadialFirstJet
          Source Current point (coordinateDirection derivativeDirection)
          formDirection internalPair := by
  have lowered :=
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_loweredConnectionFirstJet_eq_radialFirstJet
      point derivativeDirection formDirection internalPair
  fin_cases internalPair <;>
    simp [minkowskiInternalSign, pairFirst, pairSecond] at lowered ⊢ <;>
    linarith

/-- Curvature of the emitted common actual, expressed only through its
source-generated radial connection jet and its own point value. -/
def fixedP506L0CartanECConstraintCauchyGravityTailRadialGravityCurvatureNormalForm
    (point : BasePoint) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let internalOut := pairFirst internalPair
    let internalIn := pairSecond internalPair
    let first := pairFirst spacetimePair
    let second := pairSecond spacetimePair
    let sign := minkowskiInternalSign internalOut
    sign *
      (sign *
          cartanECSynchronizedGravityTailRadialFirstJet
            Source Current point (coordinateDirection first) second internalPair -
        sign *
          cartanECSynchronizedGravityTailRadialFirstJet
            Source Current point (coordinateDirection second) first internalPair +
        ∑ middle : LorentzianIndex,
          (fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.gravityConnection
                point first internalOut middle *
              fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.gravityConnection
                point second middle internalIn -
            fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.gravityConnection
                point second internalOut middle *
              fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual.gravityConnection
                point first middle internalIn))

theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_gravityCurvature_normalForm
    (point : BasePoint) :
    holonomicGravityCurvature
        fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual
        point =
      fixedP506L0CartanECConstraintCauchyGravityTailRadialGravityCurvatureNormalForm
        point := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
    fixedP506L0CartanECConstraintCauchyGravityTailRadialGravityCurvatureNormalForm
  dsimp only
  rw [
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_gravityConnectionDerivative_eq_radialFirstJet,
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_gravityConnectionDerivative_eq_radialFirstJet]

/-- Exhaustive field custody of the one emitted actual. -/
theorem
    fixedP506L0CartanECConstraintCauchyGravityTailJointPath_fieldInventory :
    let output :=
      fixedP506L0CartanECConstraintCauchyGravityTailJointPathGlobalActual
    output.coframe =
        cartanECSynchronizedGravityTailCoframePathField Source Current ∧
      output.gravityConnection =
        cartanECSynchronizedGravityTailPathConnectionField Source Current ∧
      output.gravityAuxiliary = (fun point =>
        physicalIIPlusBivector
          (cartanECSynchronizedGravityTailCoframePathField
            Source Current point)) ∧
      output.gravitySimplicityMultiplier =
        formNativeGravityReactionField
          (cartanECSynchronizedGravityTailJointConnectedActual Source Current) ∧
      output.gaugeConnection = Current.gaugeConnection ∧
      output.gaugeAuxiliary = Current.gaugeAuxiliary ∧
      output.scalar = Current.scalar ∧
      output.matter = Current.matter ∧
      output.conjugateMatter = Current.conjugateMatter := by
  repeat' apply And.intro
  all_goals rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
