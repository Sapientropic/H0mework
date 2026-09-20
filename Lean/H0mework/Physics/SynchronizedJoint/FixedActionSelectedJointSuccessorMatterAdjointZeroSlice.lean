import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorStructuralReduction
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.JointVariation.AdjointTemporalLocalRegularity
import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity
import H0mework.Physics.Geometry.CanonicalTimePrimitiveSegmentRegularity
import H0mework.Physics.DualVariation.RepairedMatterEquationReadout
import H0mework.Physics.CoframeResponse.MatterActionAcceptance

/-!
# Matter/adjoint zero-slice readback of the action-selected successor

The coupled temporal leg integrates the action-generated primal and adjoint
velocities of the exact Cartan-restarted occurrence.  This module proves that
the one global action-selected successor realizes those two velocities on the
whole canonical zero slice, then reads the corresponding Euler channels on
that same actual.

No residual, support coordinate, target derivative, or zero-fiber receipt is
an input to a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalTimePrimitiveMeasurableGermCalculus
open StageNineCanonicalTimePrimitiveSegmentRegularity
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicRegularity
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointAdjointTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorStructuralReduction
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance (priority := high) actionSelectedMatterBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance (priority := high) actionSelectedMatterBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

local instance actionSelectedMatterP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance actionSelectedMatterP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance actionSelectedMatterP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Raw : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathActionSelectedJointSuccessor

private abbrev Point (space : StageNineSpatialPoint) : BasePoint :=
  canonicalCauchySlicePoint 0 space

private theorem carry_nondegenerate (point : BasePoint) :
    Matrix.det (Carry.coframe point) ≠ 0 := by
  rw [actionSelectedCarry_coframe_eq_one]
  norm_num

private theorem carry_noncharacteristic (point : BasePoint) :
    coframeTemporalPrincipalScalar (Carry.coframe point) ≠ 0 := by
  rw [actionSelectedCarry_coframe_eq_one,
    coframeTemporalPrincipalScalar_one]
  norm_num

private theorem carry_matterCorrection_contDiffAt (point : BasePoint) :
    ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection Source Carry) point := by
  apply completeJointMatterTemporalCoordinateCorrection_contDiffAt_of_local
      Source Carry point (carry_nondegenerate point)
        (carry_noncharacteristic point)
  · rw [actionSelectedCarry_coframe_eq_one]
    fun_prop
  · exact actionSelectedCarry_scalar_contDiff.contDiffAt.of_le (by norm_num)
  · exact
      actionSelectedCarry_matterCoordinates_contDiff.contDiffAt.of_le
        (by norm_num)
  · exact
      actionSelectedCarry_conjugateMatterCoordinates_contDiff.contDiffAt.of_le
        (by norm_num)
  · intro direction
    exact
      (actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction
        ).contDiffAt.of_le (by norm_num)

/- The matter response does not read the four gravity/gauge-auxiliary fields
replaced below.  The proxy supplies their already smooth fixed P506 values so
the full regularity theorem can expose the stronger regularity of the exact
Carry response without strengthening the Lorentz-path current globally. -/
private def SmoothCarryMatterProxy : StageNineHolonomicConfiguration :=
  { Raw with
    coframe := Carry.coframe
    gaugeConnection := Carry.gaugeConnection
    scalar := Carry.scalar }

private theorem smoothCarryMatterProxy_smooth : SmoothCarryMatterProxy.Smooth := by
  rcases fixedP506L0CompleteJointActionSpacetimeSection_smooth with
    ⟨_coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, _gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      _scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine ⟨?_, gravityConnectionSmooth, gravityAuxiliarySmooth,
    multiplierSmooth, ?_, gaugeAuxiliarySmooth,
    actionSelectedCarry_scalar_contDiff,
    matterSmooth, conjugateMatterSmooth⟩
  · intro row column
    rw [show SmoothCarryMatterProxy.coframe = fun _ => (1 : LorentzianCoframe) by
      exact actionSelectedCarry_coframe_eq_one]
    fun_prop
  · intro direction
    exact actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction

private theorem carryProxy_coframe_eq :
    Carry.coframe = SmoothCarryMatterProxy.coframe := rfl

private theorem carryProxy_gaugeConnection_eq :
    Carry.gaugeConnection = SmoothCarryMatterProxy.gaugeConnection := rfl

private theorem carryProxy_scalar_eq :
    Carry.scalar = SmoothCarryMatterProxy.scalar := rfl

private theorem carryProxy_matter_eq :
    Carry.matter = SmoothCarryMatterProxy.matter := by
  rfl

private theorem carryProxy_conjugateMatter_eq :
    Carry.conjugateMatter = SmoothCarryMatterProxy.conjugateMatter := by
  rfl

private theorem carryProxy_cartanGravityConnection_eq :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Carry).gravityConnection =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source SmoothCarryMatterProxy).gravityConnection := by
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  funext point
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      Source Carry SmoothCarryMatterProxy point
      (congrFun carryProxy_coframe_eq point)
      (congrFun carryProxy_matter_eq point)
      (congrFun carryProxy_conjugateMatter_eq point)
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [carryProxy_coframe_eq, spinEq]

private theorem
    actionGeneratedRawTimeVelocity_eq_of_coreFields
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe = second.coframe)
    (gravityConnectionEq :
      first.gravityConnection = second.gravityConnection)
    (gaugeConnectionEq : first.gaugeConnection = second.gaugeConnection)
    (scalarEq : first.scalar = second.scalar)
    (matterEq : first.matter = second.matter)
    (point : BasePoint) :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        first point =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        second point := by
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterCovariantDerivative holonomicMatterConnectionAction
  rw [coframeEq, gravityConnectionEq, gaugeConnectionEq, scalarEq, matterEq]

private theorem carryProxy_matterCorrection_eq :
    completeJointMatterTemporalCoordinateCorrection Source Carry =
      completeJointMatterTemporalCoordinateCorrection
        Source SmoothCarryMatterProxy := by
  funext point
  rw [completeJointMatterTemporalCoordinateCorrection_normalForm,
    completeJointMatterTemporalCoordinateCorrection_normalForm]
  have restartCoframeEq :
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Carry).coframe =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source SmoothCarryMatterProxy).coframe := by
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
      carryProxy_coframe_eq]
  have restartGaugeConnectionEq :
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Carry).gaugeConnection =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source SmoothCarryMatterProxy).gaugeConnection := by
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
      carryProxy_gaugeConnection_eq]
  have restartScalarEq :
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Carry).scalar =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source SmoothCarryMatterProxy).scalar := by
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
      carryProxy_scalar_eq]
  have restartMatterEq :
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Carry).matter =
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source SmoothCarryMatterProxy).matter := by
    rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
      carryProxy_matter_eq]
  rw [actionGeneratedRawTimeVelocity_eq_of_coreFields
      _ _ restartCoframeEq carryProxy_cartanGravityConnection_eq
      restartGaugeConnectionEq restartScalarEq restartMatterEq point,
    carryProxy_matter_eq]

private theorem carry_matterCorrection_contDiffAt_one
    (point : BasePoint) :
    ContDiffAt ℝ 1
      (completeJointMatterTemporalCoordinateCorrection Source Carry) point := by
  have proxyRegular :=
    completeJointMatterTemporalCoordinateCorrection_contDiffAt
      Source SmoothCarryMatterProxy smoothCarryMatterProxy_smooth point
      (by
        change Matrix.det (Carry.coframe point) ≠ 0
        exact carry_nondegenerate point)
      (by
        change coframeTemporalPrincipalScalar (Carry.coframe point) ≠ 0
        exact carry_noncharacteristic point)
  rw [carryProxy_matterCorrection_eq]
  exact proxyRegular.of_le (by norm_num)

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

theorem carry_matterCorrection_contDiff :
    ContDiff ℝ ∞
      (completeJointMatterTemporalCoordinateCorrection Source Carry) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  rw [carryProxy_matterCorrection_eq]
  exact
    completeJointMatterTemporalCoordinateCorrection_contDiffAt
      Source SmoothCarryMatterProxy smoothCarryMatterProxy_smooth point
      (by
        change Matrix.det (Carry.coframe point) ≠ 0
        exact carry_nondegenerate point)
      (by
        change coframeTemporalPrincipalScalar (Carry.coframe point) ≠ 0
        exact carry_noncharacteristic point)

private theorem carry_matterPrimitive_contDiff :
    ContDiff ℝ ∞
      (canonicalTimePrimitive
        (completeJointMatterTemporalCoordinateCorrection Source Carry)) :=
  canonicalTimePrimitive_contDiff_of_contDiff _
    carry_matterCorrection_contDiff

/-- The fixed coupled primal matter field is globally smooth.  The result is
read directly from the smooth Carry field and the canonical primitive of its
source/action-generated correction. -/
theorem actionSelectedCoupled_matterCoordinates_contDiff :
    ContDiff ℝ ∞
      (fun point => matterCoordinateEquiv
        ((completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual).matter
            point)) := by
  change ContDiff ℝ ∞
    (fun point => matterCoordinateEquiv
      (Carry.matter point + matterCoordinateEquiv.symm
        (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry)
          point)))
  rw [show
    (fun point => matterCoordinateEquiv
      (Carry.matter point + matterCoordinateEquiv.symm
        (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry)
          point))) =
      (fun point => matterCoordinateEquiv (Carry.matter point)) +
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry) by
    funext point
    rw [Pi.add_apply, map_add, matterCoordinateEquiv.apply_symm_apply]]
  exact actionSelectedCarry_matterCoordinates_contDiff.add
    carry_matterPrimitive_contDiff

private theorem carry_adjointCorrection_contDiffAt (point : BasePoint) :
    ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection Source Carry) point := by
  apply completeJointAdjointTemporalCoordinateCorrection_contDiffAt_of_local
      Source Carry point (carry_nondegenerate point)
        (carry_noncharacteristic point)
  · rw [actionSelectedCarry_coframe_eq_one]
    fun_prop
  · exact actionSelectedCarry_scalar_contDiff.contDiffAt.of_le (by norm_num)
  · exact
      actionSelectedCarry_matterCoordinates_contDiff.contDiffAt.of_le
        (by norm_num)
  · exact
      actionSelectedCarry_conjugateMatterCoordinates_contDiff.contDiffAt.of_le
        (by norm_num)
  · intro direction
    exact
      (actionSelectedCarry_gaugeConnectionCoordinate_contDiff direction
        ).contDiffAt.of_le (by norm_num)

private theorem carryProxy_cartanCoframe_eq :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Carry).coframe =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source SmoothCarryMatterProxy).coframe := by
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    carryProxy_coframe_eq]

private theorem carryProxy_cartanGaugeConnection_eq :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Carry).gaugeConnection =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source SmoothCarryMatterProxy).gaugeConnection := by
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    carryProxy_gaugeConnection_eq]

private theorem carryProxy_cartanScalar_eq :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Carry).scalar =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source SmoothCarryMatterProxy).scalar := by
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    carryProxy_scalar_eq]

private theorem carryProxy_cartanConjugateMatter_eq :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      Source Carry).conjugateMatter =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source SmoothCarryMatterProxy).conjugateMatter := by
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    carryProxy_conjugateMatter_eq]

private theorem carryProxy_cartanAdjointActionVelocity_eq
    (point : BasePoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source Carry) point =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          Source SmoothCarryMatterProxy) point := by
  apply
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · unfold holonomicCoframeFirstJetAt
    rw [carryProxy_cartanCoframe_eq]
  · exact congrFun carryProxy_cartanGravityConnection_eq point
  · exact congrFun carryProxy_cartanGaugeConnection_eq point
  · exact congrFun carryProxy_cartanScalar_eq point
  · exact congrFun carryProxy_cartanConjugateMatter_eq point
  · intro direction
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [carryProxy_cartanConjugateMatter_eq]

private theorem carryProxy_adjointCorrection_eq :
    completeJointAdjointTemporalCoordinateCorrection Source Carry =
      completeJointAdjointTemporalCoordinateCorrection
        Source SmoothCarryMatterProxy := by
  funext point
  rw [completeJointAdjointTemporalCoordinateCorrection_normalForm,
    completeJointAdjointTemporalCoordinateCorrection_normalForm,
    carryProxy_cartanAdjointActionVelocity_eq]
  unfold holonomicConjugateMatterCoordinates
  rw [carryProxy_conjugateMatter_eq]

theorem carry_adjointCorrection_contDiff :
    ContDiff ℝ ∞
      (completeJointAdjointTemporalCoordinateCorrection Source Carry) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  rw [carryProxy_adjointCorrection_eq]
  exact
    completeJointAdjointTemporalCoordinateCorrection_contDiffAt_infty
      Source SmoothCarryMatterProxy smoothCarryMatterProxy_smooth point
      (by
        change Matrix.det (Carry.coframe point) ≠ 0
        exact carry_nondegenerate point)
      (by
        change coframeTemporalPrincipalScalar (Carry.coframe point) ≠ 0
        exact carry_noncharacteristic point)

private theorem carry_adjointPrimitive_contDiff :
    ContDiff ℝ ∞
      (canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Carry)) :=
  canonicalTimePrimitive_contDiff_of_contDiff _
    carry_adjointCorrection_contDiff

/-- The fixed coupled adjoint coordinates are globally smooth, generated by
the same Carry occurrence and its canonical action primitive. -/
theorem actionSelectedCoupled_conjugateMatterCoordinates_contDiff :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)) := by
  change ContDiff ℝ ∞
    (fun point => matterDualCoordinates
      (Carry.conjugateMatter point + matterDualOfCoordinates
        (canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Carry)
          point)))
  rw [show
    (fun point => matterDualCoordinates
      (Carry.conjugateMatter point + matterDualOfCoordinates
        (canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Carry)
          point))) =
      holonomicConjugateMatterCoordinates Carry +
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Carry) by
    funext point
    rw [Pi.add_apply, matterDualCoordinates_add,
      matterDualCoordinates_matterDualOfCoordinates]
    rfl]
  exact actionSelectedCarry_conjugateMatterCoordinates_contDiff.add
    carry_adjointPrimitive_contDiff

private theorem contactTranslation_contDiff (point : BasePoint) :
    ContDiff ℝ ∞ (canonicalSpacetimeContactTranslation point) := by
  unfold canonicalSpacetimeContactTranslation
  fun_prop

private theorem coupledRecentered_matterCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    let point := Point space
    let translation := canonicalSpacetimeContactTranslation point
    let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
      fun localPoint => matterCoordinateEquiv (Carry.matter (translation localPoint))
    HasFDerivAt
      (fun localPoint =>
        matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Coupled point).matter
            localPoint))
      (fderiv ℝ inputCoordinates 0 +
        ContinuousLinearMap.smulRight canonicalTimeProjection
          (completeJointMatterTemporalCoordinateCorrection Source Carry point))
      0 := by
  dsimp only
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv (Carry.matter (translation localPoint))
  have inputSmooth : ContDiff ℝ ∞ inputCoordinates := by
    dsimp [inputCoordinates, translation]
    exact actionSelectedCarry_matterCoordinates_contDiff.comp
      (contactTranslation_contDiff point)
  have inputDerivative :
      HasFDerivAt inputCoordinates (fderiv ℝ inputCoordinates 0) 0 :=
    inputSmooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt
  have correctionAtPoint := carry_matterCorrection_contDiffAt point
  have correctionRecentered : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection Source Carry ∘
        translation) 0 := by
    have atTranslated : ContDiffAt ℝ 0
        (completeJointMatterTemporalCoordinateCorrection Source Carry)
        (translation 0) := by
      simpa [translation, canonicalSpacetimeContactTranslation] using
        correctionAtPoint
    exact atTranslated.comp 0
      ((contactTranslation_contDiff point).contDiffAt.of_le (by norm_num))
  have primitiveDerivative : HasFDerivAt
      (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
        translation)
      (ContinuousLinearMap.smulRight canonicalTimeProjection
        (completeJointMatterTemporalCoordinateCorrection Source Carry point))
      0 := by
    rw [show
      canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
          translation =
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry ∘
            translation) by
      simpa [translation, point, Point] using
        canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
          (completeJointMatterTemporalCoordinateCorrection Source Carry) space]
    have generated :=
      canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
        (completeJointMatterTemporalCoordinateCorrection Source Carry ∘
          translation) correctionRecentered
    simpa [translation, point, Point, canonicalSpacetimeContactTranslation]
      using generated
  have totalDerivative := inputDerivative.add primitiveDerivative
  have fieldEquality :
      (fun localPoint =>
        matterCoordinateEquiv
          ((fullyRecenterHolonomicConfiguration Coupled point).matter
            localPoint)) =
        inputCoordinates +
          (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
              translation) := by
    funext localPoint
    change
      matterCoordinateEquiv
          (Carry.matter (translation localPoint) +
            matterCoordinateEquiv.symm
              (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection Source Carry)
                (translation localPoint))) = _
    rw [map_add, matterCoordinateEquiv.apply_symm_apply]
    rfl
  rw [fieldEquality]
  exact totalDerivative

/-- The same explicit coupled matter field is locally `C¹` after recentering
at every canonical zero-slice occurrence.  This is the regularity needed to
read the next occurrence-native temporal action leg; it is derived from the
already generated Carry response and accepts no target jet. -/
theorem
    actionSelectedCoupled_recenteredMatterCoordinates_contDiffAt_one_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 1
      (fun localPoint => matterCoordinateEquiv
        ((fullyRecenterHolonomicConfiguration
          (completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
          (canonicalCauchySlicePoint 0 space)).matter localPoint)) 0 := by
  change ContDiffAt ℝ 1
    (fun localPoint => matterCoordinateEquiv
      ((fullyRecenterHolonomicConfiguration Coupled (Point space)).matter
        localPoint)) 0
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv
      (Carry.matter (translation localPoint))
  have inputRegular : ContDiffAt ℝ 1 inputCoordinates 0 := by
    exact
      (actionSelectedCarry_matterCoordinates_contDiff.comp
        (contactTranslation_contDiff point)).contDiffAt.of_le (by norm_num)
  have correctionRecentered : ContDiffAt ℝ 1
      (completeJointMatterTemporalCoordinateCorrection Source Carry ∘
        translation) 0 := by
    have atTranslated : ContDiffAt ℝ 1
        (completeJointMatterTemporalCoordinateCorrection Source Carry)
        (translation 0) := by
      simpa [translation, canonicalSpacetimeContactTranslation] using
        carry_matterCorrection_contDiffAt_one point
    exact atTranslated.comp 0
      ((contactTranslation_contDiff point).contDiffAt.of_le (by norm_num))
  have primitiveRegular : ContDiffAt ℝ 1
      (canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
        translation) 0 := by
    rw [show
      canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
          translation =
        canonicalTimePrimitive
          (completeJointMatterTemporalCoordinateCorrection Source Carry ∘
            translation) by
      simpa [translation, point, Point] using
        canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
          (completeJointMatterTemporalCoordinateCorrection Source Carry) space]
    exact canonicalTimePrimitive_contDiffAt_of_contDiffAt
      (completeJointMatterTemporalCoordinateCorrection Source Carry ∘
        translation) correctionRecentered
  have fieldEquality :
      (fun localPoint => matterCoordinateEquiv
        ((fullyRecenterHolonomicConfiguration Coupled point).matter
          localPoint)) =
        inputCoordinates +
          (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection Source Carry) ∘
              translation) := by
    funext localPoint
    change
      matterCoordinateEquiv
          (Carry.matter (translation localPoint) +
            matterCoordinateEquiv.symm
              (canonicalTimePrimitive
                (completeJointMatterTemporalCoordinateCorrection Source Carry)
                (translation localPoint))) = _
    rw [map_add, matterCoordinateEquiv.apply_symm_apply]
    rfl
  rw [fieldEquality]
  exact inputRegular.add primitiveRegular

/-- The coupled whole field realizes its occurrence-native primal velocity at
every point of the canonical zero slice. -/
private theorem actionSelectedCoupled_matterTemporalDerivative_zeroSlice_internal
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point))
        (Point space) canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source Carry (Point space)).matterVelocity := by
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv (Carry.matter (translation localPoint))
  have generated := coupledRecentered_matterCoordinates_hasFDerivAt space
  have localDerivative :
      fieldDirectionalDerivative
          (fun localPoint =>
            matterCoordinateEquiv
              ((fullyRecenterHolonomicConfiguration Coupled point).matter
                localPoint))
          0 canonicalLorentzianTimeDirection =
        matterCoordinateEquiv
          (sourceActionGeneratedDiracDualCompleteJointProfiles
            Source Carry point).matterVelocity := by
    unfold fieldDirectionalDerivative
    rw [show
      fderiv ℝ
          (fun localPoint =>
            matterCoordinateEquiv
              ((fullyRecenterHolonomicConfiguration Coupled point).matter
                localPoint)) 0 =
        fderiv ℝ inputCoordinates 0 +
          ContinuousLinearMap.smulRight canonicalTimeProjection
            (completeJointMatterTemporalCoordinateCorrection Source Carry point) by
      simpa [point, translation, inputCoordinates] using generated.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply]
    have timeProjection :
        canonicalTimeProjection
            (coordinateDirection canonicalLorentzianTimeDirection) = 1 := by
      simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
        coordinateDirection]
    rw [timeProjection, one_smul]
    change
      fieldDirectionalDerivative inputCoordinates 0
          canonicalLorentzianTimeDirection +
        completeJointMatterTemporalCoordinateCorrection Source Carry point =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source Carry point).matterVelocity
    rw [show
      fieldDirectionalDerivative inputCoordinates 0
          canonicalLorentzianTimeDirection =
        fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (Carry.matter target)) point
          canonicalLorentzianTimeDirection by
      change
        fieldDirectionalDerivative
            ((fun target => matterCoordinateEquiv (Carry.matter target)) ∘
              canonicalSpacetimeContactTranslation point)
            0 canonicalLorentzianTimeDirection = _
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (fun target => matterCoordinateEquiv (Carry.matter target))
          point 0 canonicalLorentzianTimeDirection]
    unfold completeJointMatterTemporalCoordinateCorrection
      fieldDirectionalDerivative
    module
  calc
    fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (Coupled.matter target))
          point canonicalLorentzianTimeDirection =
        fieldDirectionalDerivative
          ((fun target => matterCoordinateEquiv (Coupled.matter target)) ∘
            translation) 0 canonicalLorentzianTimeDirection := by
      symm
      simpa [translation, canonicalSpacetimeContactTranslation] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (fun target => matterCoordinateEquiv (Coupled.matter target))
          point 0 canonicalLorentzianTimeDirection
    _ = _ := by
      change
        fieldDirectionalDerivative
            (fun localPoint =>
              matterCoordinateEquiv (Coupled.matter (translation localPoint)))
            0 canonicalLorentzianTimeDirection = _
      simpa [translation, fullyRecenterHolonomicConfiguration] using
        localDerivative

/-- The same action-selected temporal primitive leaves the three spatial
matter derivatives equal to the supplied carry current on the zero slice. -/
private theorem actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry_internal
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Coupled.matter point))
        (Point space) direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point))
        (Point space) direction.succ := by
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  let inputCoordinates : BasePoint → MatterCoordinateCarrier :=
    fun localPoint => matterCoordinateEquiv (Carry.matter (translation localPoint))
  have generated := coupledRecentered_matterCoordinates_hasFDerivAt space
  have localSpatial :
      fieldDirectionalDerivative
          (fun localPoint =>
            matterCoordinateEquiv
              ((fullyRecenterHolonomicConfiguration Coupled point).matter
                localPoint))
          0 direction.succ =
        fieldDirectionalDerivative inputCoordinates 0 direction.succ := by
    unfold fieldDirectionalDerivative
    rw [show
      fderiv ℝ
          (fun localPoint =>
            matterCoordinateEquiv
              ((fullyRecenterHolonomicConfiguration Coupled point).matter
                localPoint)) 0 =
        fderiv ℝ inputCoordinates 0 +
          ContinuousLinearMap.smulRight canonicalTimeProjection
            (completeJointMatterTemporalCoordinateCorrection Source Carry point) by
      simpa [point, translation, inputCoordinates] using generated.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply]
    fin_cases direction <;>
      simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
        coordinateDirection]
  calc
    fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (Coupled.matter target))
          point direction.succ =
        fieldDirectionalDerivative
          ((fun target => matterCoordinateEquiv (Coupled.matter target)) ∘
            translation) 0 direction.succ := by
      symm
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (fun target => matterCoordinateEquiv (Coupled.matter target))
          point 0 direction.succ
    _ = fieldDirectionalDerivative inputCoordinates 0 direction.succ := by
      change
        fieldDirectionalDerivative
            (fun localPoint =>
              matterCoordinateEquiv
                ((fullyRecenterHolonomicConfiguration Coupled point).matter
                  localPoint))
            0 direction.succ = _
      simpa [translation, fullyRecenterHolonomicConfiguration] using
        localSpatial
    _ = fieldDirectionalDerivative
          (fun target => matterCoordinateEquiv (Carry.matter target))
          point direction.succ := by
      change
        fieldDirectionalDerivative
            ((fun target => matterCoordinateEquiv (Carry.matter target)) ∘
              canonicalSpacetimeContactTranslation point)
            0 direction.succ = _
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (fun target => matterCoordinateEquiv (Carry.matter target))
          point 0 direction.succ

private def coupledRecenteredAdjointCoordinates
    (space : StageNineSpatialPoint) : BasePoint → MatterCoordinateCarrier :=
  holonomicConjugateMatterCoordinates
    (fullyRecenterHolonomicConfiguration Coupled (Point space))

private def carryRecenteredAdjointCoordinates
    (space : StageNineSpatialPoint) : BasePoint → MatterCoordinateCarrier :=
  holonomicConjugateMatterCoordinates Carry ∘
    canonicalSpacetimeContactTranslation (Point space)

private def coupledRecenteredAdjointPrimitive
    (space : StageNineSpatialPoint) : BasePoint → MatterCoordinateCarrier :=
  canonicalTimePrimitive
      (completeJointAdjointTemporalCoordinateCorrection Source Carry) ∘
    canonicalSpacetimeContactTranslation (Point space)

private theorem coupledRecenteredAdjointPrimitive_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (coupledRecenteredAdjointPrimitive space)
      (ContinuousLinearMap.smulRight canonicalTimeProjection
        (completeJointAdjointTemporalCoordinateCorrection
          Source Carry (Point space))) 0 := by
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  have correctionRecentered : ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection Source Carry ∘
        translation) 0 := by
    have atTranslated : ContDiffAt ℝ 0
        (completeJointAdjointTemporalCoordinateCorrection Source Carry)
        (translation 0) := by
      simpa [translation, canonicalSpacetimeContactTranslation] using
        carry_adjointCorrection_contDiffAt point
    exact atTranslated.comp 0
      ((contactTranslation_contDiff point).contDiffAt.of_le (by norm_num))
  unfold coupledRecenteredAdjointPrimitive
  rw [show
    canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Carry) ∘
        translation =
      canonicalTimePrimitive
        (completeJointAdjointTemporalCoordinateCorrection Source Carry ∘
          translation) by
    simpa [translation, point, Point] using
      canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
        (completeJointAdjointTemporalCoordinateCorrection Source Carry) space]
  have generated :=
    canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
      (completeJointAdjointTemporalCoordinateCorrection Source Carry ∘
        translation) correctionRecentered
  simpa [translation, point, Point, canonicalSpacetimeContactTranslation]
    using generated

private theorem carryRecenteredAdjointCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (carryRecenteredAdjointCoordinates space)
      (fderiv ℝ (carryRecenteredAdjointCoordinates space) 0) 0 := by
  have smooth : ContDiff ℝ ∞ (carryRecenteredAdjointCoordinates space) := by
    unfold carryRecenteredAdjointCoordinates
    exact actionSelectedCarry_conjugateMatterCoordinates_contDiff.comp
      (contactTranslation_contDiff (Point space))
  exact smooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt

private theorem coupledRecenteredAdjointCoordinates_normalForm
    (space : StageNineSpatialPoint) :
    coupledRecenteredAdjointCoordinates space =
      carryRecenteredAdjointCoordinates space +
        coupledRecenteredAdjointPrimitive space := by
  funext localPoint
  unfold coupledRecenteredAdjointCoordinates
    carryRecenteredAdjointCoordinates coupledRecenteredAdjointPrimitive
    holonomicConjugateMatterCoordinates
  change
    matterDualCoordinates
        (Carry.conjugateMatter
            (canonicalSpacetimeContactTranslation (Point space) localPoint) +
          matterDualOfCoordinates
            (canonicalTimePrimitive
              (completeJointAdjointTemporalCoordinateCorrection Source Carry)
              (canonicalSpacetimeContactTranslation
                (Point space) localPoint))) = _
  rw [matterDualCoordinates_add,
    matterDualCoordinates_matterDualOfCoordinates]
  rfl

/-- Local continuity of the recentered coupled adjoint field.  It is the sum
of the smooth Carry adjoint and the canonical primitive of the locally
continuous occurrence-native correction. -/
theorem
    actionSelectedCoupled_recenteredConjugateMatterCoordinates_contDiffAt_zero
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ 0
      (holonomicConjugateMatterCoordinates
        (fullyRecenterHolonomicConfiguration
          (completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
          (canonicalCauchySlicePoint 0 space))) 0 := by
  change ContDiffAt ℝ 0 (coupledRecenteredAdjointCoordinates space) 0
  rw [coupledRecenteredAdjointCoordinates_normalForm]
  have carryRegular : ContDiffAt ℝ 0
      (carryRecenteredAdjointCoordinates space) 0 := by
    unfold carryRecenteredAdjointCoordinates
    exact
      (actionSelectedCarry_conjugateMatterCoordinates_contDiff.comp
        (contactTranslation_contDiff (Point space))).contDiffAt.of_le
          (by norm_num)
  let point := Point space
  let translation := canonicalSpacetimeContactTranslation point
  have correctionRecentered : ContDiffAt ℝ 0
      (completeJointAdjointTemporalCoordinateCorrection Source Carry ∘
        translation) 0 := by
    have atTranslated : ContDiffAt ℝ 0
        (completeJointAdjointTemporalCoordinateCorrection Source Carry)
        (translation 0) := by
      simpa [translation, canonicalSpacetimeContactTranslation] using
        carry_adjointCorrection_contDiffAt point
    exact atTranslated.comp 0
      ((contactTranslation_contDiff point).contDiffAt.of_le (by norm_num))
  have primitiveRegular : ContDiffAt ℝ 0
      (coupledRecenteredAdjointPrimitive space) 0 := by
    unfold coupledRecenteredAdjointPrimitive
    rw [show
      canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection Source Carry) ∘
          translation =
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection Source Carry ∘
            translation) by
      simpa [translation, point, Point] using
        canonicalTimePrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
          (completeJointAdjointTemporalCoordinateCorrection Source Carry) space]
    exact canonicalTimePrimitive_contDiffAt_zero_of_contDiffAt_zero
      (completeJointAdjointTemporalCoordinateCorrection Source Carry ∘
        translation) correctionRecentered
  exact carryRegular.add primitiveRegular

private theorem coupledRecenteredAdjointCoordinates_hasFDerivAt
    (space : StageNineSpatialPoint) :
    HasFDerivAt
      (coupledRecenteredAdjointCoordinates space)
      (fderiv ℝ (carryRecenteredAdjointCoordinates space) 0 +
        ContinuousLinearMap.smulRight canonicalTimeProjection
          (completeJointAdjointTemporalCoordinateCorrection
            Source Carry (Point space))) 0 := by
  rw [coupledRecenteredAdjointCoordinates_normalForm]
  exact
    (carryRecenteredAdjointCoordinates_hasFDerivAt space).add
      (coupledRecenteredAdjointPrimitive_hasFDerivAt space)

private theorem coupledRecenteredAdjointTimeDerivative
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (coupledRecenteredAdjointCoordinates space)
        0 canonicalLorentzianTimeDirection =
      matterDualCoordinates
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source Carry (Point space)).adjointVelocity := by
  unfold fieldDirectionalDerivative
  rw [(coupledRecenteredAdjointCoordinates_hasFDerivAt space).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  have timeProjection :
      canonicalTimeProjection
          (coordinateDirection canonicalLorentzianTimeDirection) = 1 := by
    simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection]
  rw [timeProjection, one_smul]
  change
    fieldDirectionalDerivative (carryRecenteredAdjointCoordinates space) 0
        canonicalLorentzianTimeDirection +
      completeJointAdjointTemporalCoordinateCorrection
        Source Carry (Point space) =
    matterDualCoordinates
      (sourceActionGeneratedDiracDualCompleteJointProfiles
        Source Carry (Point space)).adjointVelocity
  rw [show
    fieldDirectionalDerivative (carryRecenteredAdjointCoordinates space) 0
        canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative (holonomicConjugateMatterCoordinates Carry)
        (Point space) canonicalLorentzianTimeDirection by
    unfold carryRecenteredAdjointCoordinates
    simpa only [canonicalSpacetimeContactTranslation_zero] using
      fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
        (holonomicConjugateMatterCoordinates Carry) (Point space) 0
        canonicalLorentzianTimeDirection]
  unfold completeJointAdjointTemporalCoordinateCorrection
  module

/-- The independently generated adjoint primitive likewise preserves all
three spatial derivatives of the carry current on the zero slice. -/
private theorem
    actionSelectedCoupled_conjugateMatterSpatialDerivative_zeroSlice_eq_carry_internal
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Coupled)
        (Point space) direction.succ =
      fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry)
        (Point space) direction.succ := by
  have localSpatial :
      fieldDirectionalDerivative
          (coupledRecenteredAdjointCoordinates space) 0 direction.succ =
        fieldDirectionalDerivative
          (carryRecenteredAdjointCoordinates space) 0 direction.succ := by
    unfold fieldDirectionalDerivative
    rw [(coupledRecenteredAdjointCoordinates_hasFDerivAt space).fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply]
    fin_cases direction <;>
      simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
        coordinateDirection]
  calc
    fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates Coupled)
          (Point space) direction.succ =
        fieldDirectionalDerivative
          (coupledRecenteredAdjointCoordinates space) 0 direction.succ := by
      unfold coupledRecenteredAdjointCoordinates
      symm
      change
        fieldDirectionalDerivative
            (holonomicConjugateMatterCoordinates Coupled ∘
              canonicalSpacetimeContactTranslation (Point space))
            0 direction.succ = _
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (holonomicConjugateMatterCoordinates Coupled)
          (Point space) 0 direction.succ
    _ = fieldDirectionalDerivative
          (carryRecenteredAdjointCoordinates space) 0 direction.succ :=
      localSpatial
    _ = fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates Carry)
          (Point space) direction.succ := by
      unfold carryRecenteredAdjointCoordinates
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (holonomicConjugateMatterCoordinates Carry)
          (Point space) 0 direction.succ

/-- The same coupled whole field realizes the independently generated
adjoint velocity on every point of the canonical zero slice. -/
private theorem actionSelectedCoupled_conjugateMatterTemporalDerivative_zeroSlice_internal
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Coupled)
        (Point space) canonicalLorentzianTimeDirection =
      matterDualCoordinates
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source Carry (Point space)).adjointVelocity := by
  calc
    fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates Coupled)
          (Point space) canonicalLorentzianTimeDirection =
        fieldDirectionalDerivative
          (holonomicConjugateMatterCoordinates Coupled ∘
            canonicalSpacetimeContactTranslation (Point space))
          0 canonicalLorentzianTimeDirection := by
      symm
      simpa only [canonicalSpacetimeContactTranslation_zero] using
        fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
          (holonomicConjugateMatterCoordinates Coupled)
          (Point space) 0 canonicalLorentzianTimeDirection
    _ = fieldDirectionalDerivative
          (coupledRecenteredAdjointCoordinates space)
          0 canonicalLorentzianTimeDirection := by
      rfl
    _ = _ := coupledRecenteredAdjointTimeDerivative space

/-! ## Public explicit mouths -/

/-- Public primal temporal first-jet realization on the whole zero slice. -/
theorem actionSelectedCoupled_matterTemporalDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
          ).matter point))
        (canonicalCauchySlicePoint 0 space) canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          positiveSmoothUnifiedSource
          (completeJointActionSelectedScalarMomentumCarryActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
          (canonicalCauchySlicePoint 0 space)).matterVelocity := by
  simpa [Source, Current, Carry, Coupled, Point] using
    actionSelectedCoupled_matterTemporalDerivative_zeroSlice_internal space

/-- Public spatial primal first-jet retention on the same zero slice. -/
theorem actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
          ).matter point))
        (canonicalCauchySlicePoint 0 space) direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((completeJointActionSelectedScalarMomentumCarryActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
          ).matter point))
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  simpa [Source, Current, Carry, Coupled, Point] using
    actionSelectedCoupled_matterSpatialDerivative_zeroSlice_eq_carry_internal
      space direction

/-- Public adjoint temporal first-jet realization on the whole zero slice. -/
theorem actionSelectedCoupled_conjugateMatterTemporalDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
        (canonicalCauchySlicePoint 0 space) canonicalLorentzianTimeDirection =
      matterDualCoordinates
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          positiveSmoothUnifiedSource
          (completeJointActionSelectedScalarMomentumCarryActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual)
          (canonicalCauchySlicePoint 0 space)).adjointVelocity := by
  simpa [Source, Current, Carry, Coupled, Point] using
    actionSelectedCoupled_conjugateMatterTemporalDerivative_zeroSlice_internal
      space

/-- Public spatial adjoint first-jet retention on the same zero slice. -/
theorem
    actionSelectedCoupled_conjugateMatterSpatialDerivative_zeroSlice_eq_carry
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (completeJointActionSelectedCoupledTemporalActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
        (canonicalCauchySlicePoint 0 space) direction.succ =
      fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          (completeJointActionSelectedScalarMomentumCarryActual
            positiveSmoothUnifiedSource
            fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
        (canonicalCauchySlicePoint 0 space) direction.succ := by
  simpa [Source, Current, Carry, Coupled, Point] using
    actionSelectedCoupled_conjugateMatterSpatialDerivative_zeroSlice_eq_carry_internal
      space direction

/-- The same explicit action-selected adjoint whole field is differentiable
at every zero-slice occurrence.  This is obtained by transporting the already
generated recentered first derivative back through the inverse translation;
no target derivative or residual enters the statement. -/
theorem actionSelectedCoupled_conjugateMatterCoordinates_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates
        (completeJointActionSelectedCoupledTemporalActual
          positiveSmoothUnifiedSource
          fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual))
      (canonicalCauchySlicePoint 0 space) := by
  change DifferentiableAt ℝ (holonomicConjugateMatterCoordinates Coupled)
    (Point space)
  let point := Point space
  let recentered := coupledRecenteredAdjointCoordinates space
  let inverseTranslation := canonicalSpacetimeContactTranslation (-point)
  have recenteredDifferentiable : DifferentiableAt ℝ recentered 0 := by
    exact (coupledRecenteredAdjointCoordinates_hasFDerivAt space).differentiableAt
  have inverseTranslationDifferentiable : DifferentiableAt ℝ
      inverseTranslation point := by
    unfold inverseTranslation canonicalSpacetimeContactTranslation
    fun_prop
  have inverseTranslationPoint : inverseTranslation point = 0 := by
    unfold inverseTranslation canonicalSpacetimeContactTranslation
    simp
  have recenteredAtInverse : DifferentiableAt ℝ recentered
      (inverseTranslation point) := by
    rw [inverseTranslationPoint]
    exact recenteredDifferentiable
  have ambientEquality :
      holonomicConjugateMatterCoordinates Coupled =
        recentered ∘ inverseTranslation := by
    unfold recentered coupledRecenteredAdjointCoordinates
    funext candidate
    unfold inverseTranslation canonicalSpacetimeContactTranslation point Point
    unfold holonomicConjugateMatterCoordinates
    apply congrArg matterDualCoordinates
    apply congrArg Coupled.conjugateMatter
    unfold canonicalSpacetimeContactTranslation
    module
  rw [ambientEquality]
  exact recenteredAtInverse.comp point inverseTranslationDifferentiable

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorMatterAdjointZeroSlice
