import H0mework.Physics.ConstrainedCauchy.FixedGlobalOperator
import H0mework.Physics.DualVariation.JointResidualCarrier
import H0mework.Physics.Jets.IIPlusJetKinematics
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Fixed P506/L0 whole-spacetime common-actual assembly

This module diagonalizes the existing source/current-only constraint
Hessian, Cartan reread, and Cauchy writer over canonical recentered contacts.
It introduces no residual, target field, zero-fibre premise, repair branch,
or point-indexed family of world actuals.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyWholeSpacetimeAssembly

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicRegularity
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailInputRegularity
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionAcceptance
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineMatterPointwiseEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariation
open StageNineScalarMomentumCoframeReadout
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option pp.universes false
set_option pp.all false

/-- One local common write generated at the canonical recentering of an
exact physical occurrence. -/
def sourceActionGeneratedCartanECConstraintCauchyContact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  let recentered := fullyRecenterHolonomicConfiguration current contact
  let cartan := cartanECCauchyTemporalBase source recentered
  let prepared :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      source cartan
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    source prepared

/-- Diagonal assembly of the local contact writes into one whole-spacetime
actual.  The point index selects a restriction of this one configuration;
it does not select a separate world actual. -/
def sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).coframe 0
  gravityConnection := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gravityConnection 0
  gravityAuxiliary := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gravitySimplicityMultiplier 0
  gaugeConnection := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gaugeConnection 0
  gaugeAuxiliary := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gaugeAuxiliary 0
  scalar := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).scalar 0
  matter := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).matter 0
  conjugateMatter := fun point =>
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).conjugateMatter 0

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalInput

abbrev Candidate : StageNineHolonomicConfiguration :=
  sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
    Source Current

@[simp] private theorem cauchyTemporalGlobalOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
      source current).gaugeAuxiliary = current.gaugeAuxiliary := by
  rfl

private theorem globalOperator_gravityConnection_at_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).gravityConnection point =
      (sourceActionGeneratedCartanECConstraintCauchyContact
        source current point).gravityConnection 0 :=
  rfl

private theorem globalOperator_gaugeConnection_at_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).gaugeConnection point =
      (sourceActionGeneratedCartanECConstraintCauchyContact
        source current point).gaugeConnection 0 :=
  rfl

private theorem globalOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).coframe = current.coframe := by
  funext point
  simp [sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator,
    sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase,
    fullyRecenterHolonomicConfiguration]

private theorem globalOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).gaugeConnection = current.gaugeConnection := by
  funext point
  simp [sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator,
    sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase,
    fullyRecenterHolonomicConfiguration]

private theorem globalOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).scalar = current.scalar := by
  funext point
  simp [sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator,
    sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase,
    fullyRecenterHolonomicConfiguration]

private theorem globalOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).matter = current.matter := by
  funext point
  simp [sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator,
    sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase,
    fullyRecenterHolonomicConfiguration]

private theorem globalOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).conjugateMatter = current.conjugateMatter := by
  funext point
  simp [sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator,
    sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase,
    fullyRecenterHolonomicConfiguration]

private theorem globalOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current).gaugeAuxiliary = current.gaugeAuxiliary := by
  funext point
  simp [sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator,
    sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase,
    fullyRecenterHolonomicConfiguration]

private theorem contact_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gaugeConnection =
      (fullyRecenterHolonomicConfiguration current point).gaugeConnection := by
  simp [sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase]

private theorem contact_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).scalar =
      (fullyRecenterHolonomicConfiguration current point).scalar := by
  simp [sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase]

private theorem contact_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).matter =
      (fullyRecenterHolonomicConfiguration current point).matter := by
  simp [sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase]

private theorem contact_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).conjugateMatter =
      (fullyRecenterHolonomicConfiguration current point).conjugateMatter := by
  simp [sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase]

private theorem contact_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point).gaugeAuxiliary =
      (fullyRecenterHolonomicConfiguration current point).gaugeAuxiliary := by
  simp [sourceActionGeneratedCartanECConstraintCauchyContact,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift,
    cartanECCauchyTemporalBase]

theorem contact_coframe_hasFDerivAt_origin_of
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivative : BasePoint →L[ℝ] LorentzianCoframe)
    (currentDerivative :
      HasFDerivAt
        (fullyRecenterHolonomicConfiguration current point).coframe
        derivative 0) :
    HasFDerivAt
      (sourceActionGeneratedCartanECConstraintCauchyContact
        source current point).coframe derivative 0 := by
  unfold sourceActionGeneratedCartanECConstraintCauchyContact
  rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe]
  apply
    identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_hasFDerivAt_origin_of
  rw [show
      (cartanECCauchyTemporalBase source
        (fullyRecenterHolonomicConfiguration current point)).coframe =
        (fullyRecenterHolonomicConfiguration current point).coframe by
    unfold cartanECCauchyTemporalBase
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        source (fullyRecenterHolonomicConfiguration current point)]
  exact currentDerivative

private theorem coframe_differentiableAt_of_components
    (coframe : BasePoint → LorentzianCoframe)
    (point : BasePoint)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) point) :
    DifferentiableAt ℝ coframe point := by
  apply differentiableAt_pi.mpr
  intro internal
  apply differentiableAt_pi.mpr
  intro coordinate
  exact componentDifferentiable internal coordinate

private theorem component_fderiv_apply
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → I → V)
    (point : BasePoint)
    (fieldDifferentiableAt : DifferentiableAt ℝ field point)
    (direction : BasePoint) (index : I) :
    fderiv ℝ (fun candidate => field candidate index) point direction =
      (fderiv ℝ field point direction) index := by
  have derivativeEquality := fderiv_apply fieldDifferentiableAt index
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] V => derivative direction)
    derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied

private theorem contact_coframe_differentiableAt_of_components
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (currentComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point) :
    DifferentiableAt ℝ
      (sourceActionGeneratedCartanECConstraintCauchyContact
        source current point).coframe 0 := by
  have currentDifferentiable : DifferentiableAt ℝ current.coframe point :=
    coframe_differentiableAt_of_components current.coframe point
      currentComponents
  have currentAtTranslated : DifferentiableAt ℝ current.coframe
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using currentDifferentiable
  have recenteredDifferentiable : DifferentiableAt ℝ
      (fullyRecenterHolonomicConfiguration current point).coframe 0 := by
    change DifferentiableAt ℝ
      (current.coframe ∘ canonicalSpacetimeContactTranslation point) 0
    exact currentAtTranslated.comp 0 (by
      unfold canonicalSpacetimeContactTranslation
      fun_prop)
  exact
    (contact_coframe_hasFDerivAt_origin_of source current point
      (fderiv ℝ
        (fullyRecenterHolonomicConfiguration current point).coframe 0)
      recenteredDifferentiable.hasFDerivAt).differentiableAt

private theorem contact_coframeFirstJet_origin_of_components
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (currentComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point) :
    holonomicCoframeFirstJetAt
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point).coframe 0 =
      holonomicCoframeFirstJetAt current.coframe point := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact source current point
  let Recentered := fullyRecenterHolonomicConfiguration current point
  have currentDifferentiable : DifferentiableAt ℝ current.coframe point :=
    coframe_differentiableAt_of_components current.coframe point
      currentComponents
  have currentAtTranslated : DifferentiableAt ℝ current.coframe
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using currentDifferentiable
  have recenteredDifferentiable : DifferentiableAt ℝ Recentered.coframe 0 := by
    change DifferentiableAt ℝ
      (current.coframe ∘ canonicalSpacetimeContactTranslation point) 0
    exact currentAtTranslated.comp 0 (by
      unfold canonicalSpacetimeContactTranslation
      fun_prop)
  have contactHasFDeriv : HasFDerivAt Contact.coframe
      (fderiv ℝ Recentered.coframe 0) 0 :=
    contact_coframe_hasFDerivAt_origin_of source current point
      (fderiv ℝ Recentered.coframe 0)
      recenteredDifferentiable.hasFDerivAt
  have contactDifferentiable : DifferentiableAt ℝ Contact.coframe 0 :=
    contactHasFDeriv.differentiableAt
  have fderivEq :
      fderiv ℝ Contact.coframe 0 = fderiv ℝ Recentered.coframe 0 :=
    contactHasFDeriv.fderiv
  have recenteredJet :=
    fullyRecenterHolonomicConfiguration_coframeFirstJet_origin current point
  apply coframeJet_eq_of_fields_eq
  · change Contact.coframe 0 = current.coframe point
    calc
      Contact.coframe 0 = Recentered.coframe 0 := by
        unfold Contact sourceActionGeneratedCartanECConstraintCauchyContact
        rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe]
        exact
          identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin
            _ _
      _ = current.coframe point :=
        fullyRecenterHolonomicConfiguration_coframe_origin _ _
  · funext derivativeDirection internal coordinate
    change
      fderiv ℝ
          (fun candidate => Contact.coframe candidate internal coordinate)
          0 (coordinateDirection derivativeDirection) =
        fderiv ℝ
          (fun candidate => current.coframe candidate internal coordinate)
          point (coordinateDirection derivativeDirection)
    calc
      _ = ((fderiv ℝ Contact.coframe 0)
            (coordinateDirection derivativeDirection)) internal coordinate := by
        rw [component_fderiv_apply
          (fun candidate => Contact.coframe candidate internal) 0
          (differentiableAt_pi.mp contactDifferentiable internal)
          (coordinateDirection derivativeDirection) coordinate]
        rw [component_fderiv_apply Contact.coframe 0 contactDifferentiable
          (coordinateDirection derivativeDirection) internal]
        rfl
      _ = ((fderiv ℝ Recentered.coframe 0)
            (coordinateDirection derivativeDirection)) internal coordinate := by
        rw [fderivEq]
      _ = fderiv ℝ
          (fun candidate => Recentered.coframe candidate internal coordinate)
          0 (coordinateDirection derivativeDirection) := by
        rw [component_fderiv_apply
          (fun candidate => Recentered.coframe candidate internal) 0
          (differentiableAt_pi.mp recenteredDifferentiable internal)
          (coordinateDirection derivativeDirection) coordinate]
        rw [component_fderiv_apply Recentered.coframe 0
          recenteredDifferentiable
          (coordinateDirection derivativeDirection) internal]
        rfl
      _ = _ := congrArg
        (fun jet => jet.derivative derivativeDirection internal coordinate)
        recenteredJet

private theorem candidate_coframeFirstJet_identity
    (point : BasePoint) :
    holonomicCoframeFirstJetAt Candidate.coframe point =
      identityCoframeMatterGeometry := by
  rw [show Candidate.coframe = Current.coframe by
    exact globalOperator_coframe Source Current]
  rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

private theorem contact_coframeFirstJet_identity
    (point : BasePoint) :
    holonomicCoframeFirstJetAt
        (sourceActionGeneratedCartanECConstraintCauchyContact
          Source Current point).coframe 0 =
      identityCoframeMatterGeometry := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact Source Current point
  have recenteredCoframe :
      (fullyRecenterHolonomicConfiguration Current point).coframe =
        fun _ => (1 : LorentzianCoframe) := by
    simp [fullyRecenterHolonomicConfiguration,
      fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  let Increment :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement Source
      (cartanECCauchyTemporalBase Source
        (fullyRecenterHolonomicConfiguration Current point))
  have contactCoframeEq : Contact.coframe =
      fun candidate =>
        (1 : LorentzianCoframe) +
          coframeHolonomicSecondJetQuadraticRealization Increment candidate := by
    funext candidate
    simp [Contact, Increment,
      sourceActionGeneratedCartanECConstraintCauchyContact,
      sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
      identityECHolonomicCoframeHessianIncrementLocalActualLift,
      cartanECCauchyTemporalBase,
      fullyRecenterHolonomicConfiguration,
      fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  have incrementSmooth : ContDiff ℝ ∞
      (coframeHolonomicSecondJetQuadraticRealization Increment) :=
    coframeHolonomicSecondJetQuadraticRealization_contDiff Increment
  apply coframeJet_eq_of_fields_eq
  · change Contact.coframe 0 = 1
    simp [Contact, sourceActionGeneratedCartanECConstraintCauchyContact,
      sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
      identityECHolonomicCoframeHessianIncrementLocalActualLift,
      cartanECCauchyTemporalBase,
      fullyRecenterHolonomicConfiguration,
      fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  · funext derivativeDirection internal coordinate
    have incrementComponentDerivative :
        fieldDirectionalDerivative
            (fun candidate =>
              coframeHolonomicSecondJetQuadraticRealization Increment
                candidate internal coordinate)
            0 derivativeDirection = 0 := by
      rw [← fieldDirectionalDerivative_pi_apply
        (fun candidate =>
          coframeHolonomicSecondJetQuadraticRealization Increment candidate
            internal)
        (contDiff_pi.mp incrementSmooth internal) 0 derivativeDirection
        coordinate]
      rw [← fieldDirectionalDerivative_pi_apply
        (coframeHolonomicSecondJetQuadraticRealization Increment)
        incrementSmooth 0 derivativeDirection internal]
      exact congrFun
        (congrFun
          (coframeHolonomicSecondJetQuadraticRealization_firstJet_origin
            Increment derivativeDirection)
          internal) coordinate
    change
      fieldDirectionalDerivative
          (fun candidate => Contact.coframe candidate internal coordinate)
          0 derivativeDirection = 0
    rw [contactCoframeEq]
    rw [show
      (fun candidate =>
        (fun localPoint =>
          (1 : LorentzianCoframe) +
            coframeHolonomicSecondJetQuadraticRealization Increment localPoint)
          candidate internal coordinate) =
        (fun candidate =>
          (1 : LorentzianCoframe) internal coordinate +
            coframeHolonomicSecondJetQuadraticRealization Increment
              candidate internal coordinate) by
      rfl]
    unfold fieldDirectionalDerivative at incrementComponentDerivative ⊢
    rw [fderiv_const_add]
    exact incrementComponentDerivative

private theorem actionCartanConnectionAt_eq_of_jet_and_fields_at_two_points
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (jetEqual :
      holonomicCoframeFirstJetAt first.coframe firstPoint =
        holonomicCoframeFirstJetAt second.coframe secondPoint)
    (coframeEqual : first.coframe firstPoint = second.coframe secondPoint)
    (matterEqual : first.matter firstPoint = second.matter secondPoint)
    (conjugateEqual :
      first.conjugateMatter firstPoint =
        second.conjugateMatter secondPoint) :
    diracDualFormNativeActionCartanConnectionAt source first firstPoint =
      diracDualFormNativeActionCartanConnectionAt source second secondPoint := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at_two_points
      source first second firstPoint secondPoint coframeEqual matterEqual
        conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [jetEqual, coframeEqual, spinEqual]

private theorem
    contact_gravityConnection_origin_eq_actionCartanCurrent_of_currentCoframeDifferentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (currentComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point) :
    (sourceActionGeneratedCartanECConstraintCauchyContact
        source current point).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt source current point := by
  let Recentered := fullyRecenterHolonomicConfiguration current point
  let Cartan := cartanECCauchyTemporalBase source Recentered
  let Prepared :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      source Cartan
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact source current point
  have zeroPoint :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext coordinate
    fin_cases coordinate <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have preparedJet :
      holonomicCoframeFirstJetAt Prepared.coframe 0 =
        holonomicCoframeFirstJetAt current.coframe point := by
    have contactJet :=
      contact_coframeFirstJet_origin_of_components source current point
        currentComponents
    change holonomicCoframeFirstJetAt Contact.coframe 0 =
      holonomicCoframeFirstJetAt current.coframe point at contactJet
    have contactCoframe : Contact.coframe = Prepared.coframe := by
      change
        (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
          source Prepared).coframe = Prepared.coframe
      exact
        sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe
          source Prepared
    rw [contactCoframe] at contactJet
    exact contactJet
  have coreConnection :
      diracDualFormNativeActionCartanConnectionAt source Prepared 0 =
        diracDualFormNativeActionCartanConnectionAt source current point := by
    apply actionCartanConnectionAt_eq_of_jet_and_fields_at_two_points
    · exact preparedJet
    · calc
        Prepared.coframe 0 = Cartan.coframe 0 := by
          change
            (identityECHolonomicCoframeHessianIncrementLocalActualLift Cartan
              (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
                source Cartan)).coframe 0 = Cartan.coframe 0
          exact
            identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin
              Cartan _
        _ = Recentered.coframe 0 := by
          exact congrFun
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
              source Recentered) 0
        _ = current.coframe point :=
          fullyRecenterHolonomicConfiguration_coframe_origin current point
    · calc
        Prepared.matter 0 = Cartan.matter 0 := by rfl
        _ = Recentered.matter 0 := by rfl
        _ = current.matter point :=
          fullyRecenterHolonomicConfiguration_matter_origin current point
    · calc
        Prepared.conjugateMatter 0 = Cartan.conjugateMatter 0 := by rfl
        _ = Recentered.conjugateMatter 0 := by rfl
        _ = current.conjugateMatter point :=
          fullyRecenterHolonomicConfiguration_conjugateMatter_origin current point
  change
    (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
        source Prepared).gravityConnection 0 = _
  rw [← zeroPoint,
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice,
    zeroPoint]
  unfold cartanECCauchyTemporalBase
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact coreConnection

/-- The whole-spacetime assembly installs exactly the source-action Cartan
connection of its own current whenever that current's coframe is differentiable.
Thus the remaining gravity-curvature seam is a first-jet compatibility law of
one physical connection, not a mismatch between independently chosen fields. -/
theorem
    sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator_gravityConnection_eq_actionCartanCurrent_of_currentCoframeDifferentiable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentComponents : ∀ point internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point) :
    (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
        source current).gravityConnection =
      fun point =>
        diracDualFormNativeActionCartanConnectionAt source current point := by
  funext point
  rw [globalOperator_gravityConnection_at_contact]
  exact
    contact_gravityConnection_origin_eq_actionCartanCurrent_of_currentCoframeDifferentiableAt
      source current point (currentComponents point)

private theorem candidate_coframe_contDiff : ContDiff ℝ ∞ Candidate.coframe := by
  rw [show Candidate.coframe = Current.coframe by
    exact globalOperator_coframe Source Current]
  rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  exact contDiff_const

private theorem contact_coframe_contDiff (point : BasePoint) :
    ContDiff ℝ ∞
      (sourceActionGeneratedCartanECConstraintCauchyContact
        Source Current point).coframe := by
  let Increment :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement Source
      (cartanECCauchyTemporalBase Source
        (fullyRecenterHolonomicConfiguration Current point))
  rw [show
    (sourceActionGeneratedCartanECConstraintCauchyContact
      Source Current point).coframe =
        fun candidate =>
          (1 : LorentzianCoframe) +
            coframeHolonomicSecondJetQuadraticRealization Increment candidate by
    funext candidate
    simp [Increment, sourceActionGeneratedCartanECConstraintCauchyContact,
      sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
      identityECHolonomicCoframeHessianIncrementLocalActualLift,
      cartanECCauchyTemporalBase,
      fullyRecenterHolonomicConfiguration,
      fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]]
  exact contDiff_const.add
    (coframeHolonomicSecondJetQuadraticRealization_contDiff Increment)

private theorem current_smooth : Current.Smooth :=
  fixedP506L0ActionSelectedCartanECSynchronizedGravityTailBase_smooth

private theorem globalOperator_matterDifferentialMomentum
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) direction derivativeDirection =
      matterDifferentialMomentum source current direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [globalOperator_coframe source current,
    globalOperator_conjugateMatter source current]

private theorem globalOperator_matterDifferentialMomentumDivergence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) :
    matterDifferentialMomentumDivergence source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) direction point =
      matterDifferentialMomentumDivergence source current direction point := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [globalOperator_matterDifferentialMomentum source current direction
    derivativeDirection]

private theorem globalOperator_gaugeCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      holonomicGaugeCurvature current point := by
  exact holonomicGaugeCurvature_eq_of_connection_eq _ _
    (globalOperator_gaugeConnection source current) point

private theorem contact_gaugeCurvature_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point) 0 =
      holonomicGaugeCurvature current point := by
  rw [holonomicGaugeCurvature_eq_of_connection_eq _ _
    (contact_gaugeConnection source current point) 0]
  exact
    fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
      current point

private theorem globalOperator_scalarCovariantDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      holonomicScalarCovariantDerivative current point := by
  unfold holonomicScalarCovariantDerivative
  rw [globalOperator_scalar source current,
    globalOperator_gaugeConnection source current]

private theorem globalOperator_scalarDifferentialMomentum
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) direction derivativeDirection =
      scalarDifferentialMomentum source current direction
        derivativeDirection := by
  rw [scalarDifferentialMomentum_eq_readout,
    scalarDifferentialMomentum_eq_readout]
  funext point
  simp only [Function.comp_apply]
  rw [globalOperator_coframe source current,
    globalOperator_scalarCovariantDerivative source current point]

private theorem globalOperator_scalarDifferentialMomentumDivergence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) :
    scalarDifferentialMomentumDivergence source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) direction point =
      scalarDifferentialMomentumDivergence source current direction point := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [globalOperator_scalarDifferentialMomentum source current direction
    derivativeDirection]

private theorem recentered_coframe_eq_one (point : BasePoint) :
    (fullyRecenterHolonomicConfiguration Current point).coframe =
      fun _ => (1 : LorentzianCoframe) := by
  simp [fullyRecenterHolonomicConfiguration,
    fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]

private theorem contact_conjugateMatterCoordinates_contDiff (point : BasePoint) :
    ContDiff ℝ ∞
      (holonomicConjugateMatterCoordinates
        (sourceActionGeneratedCartanECConstraintCauchyContact
          Source Current point)) := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact Source Current point
  let Recentered := fullyRecenterHolonomicConfiguration Current point
  have recenteredSmooth : Recentered.Smooth :=
    fullyRecenterHolonomicConfiguration_smooth Current current_smooth point
  have coordinatesSmooth :=
    holonomicConjugateMatterCoordinates_contDiff Recentered recenteredSmooth
  rw [show holonomicConjugateMatterCoordinates Contact =
      holonomicConjugateMatterCoordinates Recentered by
    funext candidate
    unfold holonomicConjugateMatterCoordinates
    rw [contact_conjugateMatter Source Current point]]
  exact coordinatesSmooth

private theorem identityComparison_contact_matterDifferentialMomentum_eq_recentered
    (point : BasePoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum Source
        (identityCoframeComparison
          (sourceActionGeneratedCartanECConstraintCauchyContact
            Source Current point)) direction derivativeDirection =
      matterDifferentialMomentum Source
        (fullyRecenterHolonomicConfiguration Current point) direction
        derivativeDirection := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact Source Current point
  let Recentered := fullyRecenterHolonomicConfiguration Current point
  funext candidate
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField, identityCoframeComparison_coframe,
    identityCoframeComparison_conjugateMatter]
  rw [contact_conjugateMatter Source Current point]
  simp [recentered_coframe_eq_one point]

private theorem contact_matterDifferentialMomentumDivergence_eq_current
    (point : BasePoint)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence Source
        (sourceActionGeneratedCartanECConstraintCauchyContact
          Source Current point) direction 0 =
      matterDifferentialMomentumDivergence Source Current direction point := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact Source Current point
  let Recentered := fullyRecenterHolonomicConfiguration Current point
  have contactToIdentity :
      matterDifferentialMomentumDivergence Source Contact direction 0 =
        matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Contact) direction 0 :=
    matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
      Source Contact 0
      ((contact_coframe_contDiff point).differentiable (by simp)
        |>.differentiableAt)
      ((contact_conjugateMatterCoordinates_contDiff point).differentiable
        (by simp) |>.differentiableAt)
      (contact_coframeFirstJet_identity point) direction
  have identityToRecentered :
      matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Contact) direction 0 =
        matterDifferentialMomentumDivergence Source Recentered direction 0 := by
    unfold matterDifferentialMomentumDivergence
    apply Finset.sum_congr rfl
    intro derivativeDirection _
    rw [identityComparison_contact_matterDifferentialMomentum_eq_recentered
      point direction derivativeDirection]
  calc
    _ = matterDifferentialMomentumDivergence Source
          (identityCoframeComparison Contact) direction 0 := contactToIdentity
    _ = matterDifferentialMomentumDivergence Source Recentered direction 0 :=
      identityToRecentered
    _ = matterDifferentialMomentumDivergence Source Current direction point :=
      congrFun
        (matterDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
          Source Current point) direction

private theorem contact_scalarCovariantDerivative_eq_recentered
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point) =
      holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration current point) := by
  funext candidate
  unfold holonomicScalarCovariantDerivative
  rw [contact_scalar source current point,
    contact_gaugeConnection source current point]

private theorem recentered_scalarCovariantDerivative_eq_comp
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative
        (fullyRecenterHolonomicConfiguration current point) =
      holonomicScalarCovariantDerivative current ∘
        canonicalSpacetimeContactTranslation point := by
  funext candidate direction
  have derivativeEq :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      current.scalar point candidate direction
  unfold holonomicScalarCovariantDerivative
  change
    fieldDirectionalDerivative
          (current.scalar ∘ canonicalSpacetimeContactTranslation point)
          candidate direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection
              (canonicalSpacetimeContactTranslation point candidate) direction))
          (current.scalar
            (canonicalSpacetimeContactTranslation point candidate)) =
      fieldDirectionalDerivative current.scalar
          (canonicalSpacetimeContactTranslation point candidate) direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (current.gaugeConnection
              (canonicalSpacetimeContactTranslation point candidate) direction))
          (current.scalar
            (canonicalSpacetimeContactTranslation point candidate))
  rw [derivativeEq]

private def scalarMomentumInner
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint →
      LorentzianCoframe ×
        (LorentzianIndex → ScalarCoordinateCarrier) :=
  fun point =>
    (configuration.coframe point,
      holonomicScalarCovariantDerivative configuration point)

private theorem contact_scalarCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicScalarCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point) 0 =
      holonomicScalarCovariantDerivative current point := by
  unfold holonomicScalarCovariantDerivative
  rw [contact_scalar source current point,
    contact_gaugeConnection source current point]
  exact
    fullyRecenterHolonomicConfiguration_scalarCovariantDerivative_origin_unconditional
      current point

private theorem globalOperator_matterCovariantDerivative_eq_contact_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      holonomicMatterCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point) 0 := by
  funext direction
  let coordinateField : BasePoint → MatterCoordinateCarrier :=
    fun candidate => matterCoordinateEquiv (current.matter candidate)
  have derivativeEq :=
    fieldDirectionalDerivative_comp_canonicalSpacetimeContactTranslation
      coordinateField point 0 direction
  unfold holonomicMatterCovariantDerivative
  rw [globalOperator_matter source current,
    contact_matter source current point,
    globalOperator_gravityConnection_at_contact source current point,
    globalOperator_gaugeConnection_at_contact source current point]
  simp only [fullyRecenterHolonomicConfiguration]
  simp only [canonicalSpacetimeContactTranslation_zero]
  have fieldEq :
      coordinateField ∘ canonicalSpacetimeContactTranslation point =
        fun candidate =>
          matterCoordinateEquiv
            (current.matter
              (canonicalSpacetimeContactTranslation point candidate)) := by
    rfl
  rw [fieldEq] at derivativeEq
  have derivativeEq' :
      fieldDirectionalDerivative
          (fun candidate =>
            matterCoordinateEquiv
              (current.matter
                (canonicalSpacetimeContactTranslation point candidate)))
          0 direction =
        fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv (current.matter candidate))
          point direction := by
    simpa only [coordinateField,
      canonicalSpacetimeContactTranslation_zero] using derivativeEq
  rw [derivativeEq']

private theorem globalOperator_p286GaugeAuxiliaryExteriorCovariantDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative current point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [globalOperator_gaugeConnection source current,
    globalOperator_gaugeAuxiliary source current]

private theorem contact_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point) 0 =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative current point := by
  rw [show
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyContact
            source current point) 0 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (fullyRecenterHolonomicConfiguration current point) 0 by
    unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
      p286GaugeAuxiliaryDirectionalDerivative
      holonomicP286GaugeConnectionCoordinate
      holonomicP286GaugeAuxiliaryCoordinate
    rw [contact_gaugeConnection source current point,
      contact_gaugeAuxiliary source current point]]
  exact
    fullyRecenterHolonomicConfiguration_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
      current point

/-- Matching local-origin action jet of the same recentered contact write. -/
def contactActionJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    DiracDualFormNativePointwiseActionJetCarrier :=
  generatedDiracDualFormNativePointwiseActionJet source
    (sourceActionGeneratedCartanECConstraintCauchyContact
      source current point) 0

/-- Exhaustive derived-jet difference between the one global actual and its
matching local contact.  This is a downstream readout of two generated jets. -/
def candidateAssemblySeam
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    CompleteJointActionJetAssemblySeam :=
  completeJointActionJetAssemblySeam
    (generatedDiracDualFormNativePointwiseActionJet source
      (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
        source current) point)
    (contactActionJet source current point)

/-- The gravity-curvature assembly seam contains no independent quadratic
Cartan-bracket defect: both reads carry the same connection value at the
registered occurrence.  Its exact remaining content is the antisymmetrized
first derivative mismatch between the global diagonal and the matching
contact germ. -/
theorem
    candidateAssemblySeam_gravityCurvature_coordinate_eq_connectionDerivativeAntisymmetry
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    (candidateAssemblySeam source current point).gravityCurvature
        internalPair spacetimePair =
      minkowskiInternalSign (pairFirst internalPair) *
        ((gravityConnectionDerivative
              (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
                source current)
              point (pairFirst spacetimePair) (pairSecond spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair) -
            gravityConnectionDerivative
              (sourceActionGeneratedCartanECConstraintCauchyContact
                source current point)
              0 (pairFirst spacetimePair) (pairSecond spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair)) -
          (gravityConnectionDerivative
              (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
                source current)
              point (pairSecond spacetimePair) (pairFirst spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair) -
            gravityConnectionDerivative
              (sourceActionGeneratedCartanECConstraintCauchyContact
                source current point)
              0 (pairSecond spacetimePair) (pairFirst spacetimePair)
              (pairFirst internalPair) (pairSecond internalPair))) := by
  unfold candidateAssemblySeam contactActionJet
    completeJointActionJetAssemblySeam
    generatedDiracDualFormNativePointwiseActionJet toContinuumPointField
    holonomicGravityCurvature
  simp only [Pi.sub_apply]
  rw [globalOperator_gravityConnection_at_contact source current point]
  ring

/-- Point-local first-jet custody closes the gravity-auxiliary coordinate of
the source/current-only assembly seam.  The regularity hypothesis belongs to
the actual current coframe; the candidate and contact jets are generated by
the existing whole-spacetime writer. -/
theorem
    candidateAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero_of_currentCoframeDifferentiableAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (currentComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point) :
    (candidateAssemblySeam source current point
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 := by
  let Candidate :=
    sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      source current
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact source current point
  have candidateCoframe : Candidate.coframe = current.coframe := by
    exact globalOperator_coframe source current
  have candidateAuxiliary :
      Candidate.gravityAuxiliary =
        fun candidate => physicalIIPlusBivector (Candidate.coframe candidate) := by
    funext candidatePoint
    change
      (sourceActionGeneratedCartanECConstraintCauchyContact
        source current candidatePoint).gravityAuxiliary 0 = _
    exact
      sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
        source
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          source
          (cartanECCauchyTemporalBase source
            (fullyRecenterHolonomicConfiguration current candidatePoint)))
        0
  have contactAuxiliary :
      Contact.gravityAuxiliary =
        fun candidate => physicalIIPlusBivector (Contact.coframe candidate) := by
    funext localPoint
    unfold Contact sourceActionGeneratedCartanECConstraintCauchyContact
    exact
      sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
        source
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          source
          (cartanECCauchyTemporalBase source
            (fullyRecenterHolonomicConfiguration current point)))
        localPoint
  have candidateComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => Candidate.coframe candidate internal coordinate)
        point := by
    rw [candidateCoframe]
    exact currentComponents
  have contactDifferentiable : DifferentiableAt ℝ Contact.coframe 0 := by
    exact contact_coframe_differentiableAt_of_components
      source current point currentComponents
  have contactComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => Contact.coframe candidate internal coordinate) 0 := by
    intro internal coordinate
    exact differentiableAt_pi.mp
      (differentiableAt_pi.mp contactDifferentiable internal) coordinate
  have coframeJetEq :
      holonomicCoframeFirstJetAt Candidate.coframe point =
        holonomicCoframeFirstJetAt Contact.coframe 0 := by
    rw [candidateCoframe]
    exact (contact_coframeFirstJet_origin_of_components
      source current point currentComponents).symm
  have auxiliaryJetEq :
      holonomicGravityAuxiliaryJet Candidate point =
        holonomicGravityAuxiliaryJet Contact 0 := by
    exact holonomicGravityAuxiliaryJet_eq_of_iiPlus_of_coframeFirstJet_eq
      Candidate Contact point 0 candidateAuxiliary contactAuxiliary
      candidateComponents contactComponents coframeJetEq
  change
    holonomicGravityAuxiliaryExteriorCovariantDerivative Candidate point -
        holonomicGravityAuxiliaryExteriorCovariantDerivative Contact 0 = 0
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
  rw [auxiliaryJetEq]
  have connectionEq :
      Candidate.gravityConnection point = Contact.gravityConnection 0 := rfl
  rw [connectionEq]
  exact sub_self _

/-- The scalar-divergence coordinate of the assembly closes wherever the
actual current supplies its point-local coframe and scalar-covariant first
jets and the coframe is nondegenerate at that exact occurrence.  This is a
local source regularity theorem: it neither assumes a target field nor turns
nondegeneracy at one occurrence into a global premise. -/
theorem
    candidateAssemblySeam_scalarDifferentialMomentumDivergence_zero_of_currentLocalRegularity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (currentCoframeComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point)
    (currentScalarCovariantDerivativeDifferentiable :
      DifferentiableAt ℝ
        (holonomicScalarCovariantDerivative current) point)
    (currentCoframeNondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    (candidateAssemblySeam source current point
      ).scalarDifferentialMomentumDivergence = 0 := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact source current point
  let Recentered := fullyRecenterHolonomicConfiguration current point
  have currentCoframeDifferentiable :
      DifferentiableAt ℝ current.coframe point :=
    coframe_differentiableAt_of_components current.coframe point
      currentCoframeComponents
  have currentCoframeAtTranslated : DifferentiableAt ℝ current.coframe
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using currentCoframeDifferentiable
  have recenteredCoframeDifferentiable :
      DifferentiableAt ℝ Recentered.coframe 0 := by
    change DifferentiableAt ℝ
      (current.coframe ∘ canonicalSpacetimeContactTranslation point) 0
    exact currentCoframeAtTranslated.comp 0 (by
      unfold canonicalSpacetimeContactTranslation
      fun_prop)
  have contactCoframeHasFDeriv : HasFDerivAt Contact.coframe
      (fderiv ℝ Recentered.coframe 0) 0 :=
    contact_coframe_hasFDerivAt_origin_of source current point
      (fderiv ℝ Recentered.coframe 0)
      recenteredCoframeDifferentiable.hasFDerivAt
  have contactCoframeDifferentiable :
      DifferentiableAt ℝ Contact.coframe 0 :=
    contactCoframeHasFDeriv.differentiableAt
  have contactCoframeFderivEq :
      fderiv ℝ Contact.coframe 0 = fderiv ℝ Recentered.coframe 0 :=
    contactCoframeHasFDeriv.fderiv
  have currentScalarAtTranslated : DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative current)
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using currentScalarCovariantDerivativeDifferentiable
  have recenteredScalarDifferentiable : DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative Recentered) 0 := by
    rw [recentered_scalarCovariantDerivative_eq_comp current point]
    exact currentScalarAtTranslated.comp 0 (by
      unfold canonicalSpacetimeContactTranslation
      fun_prop)
  have contactScalarDifferentiable : DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative Contact) 0 := by
    rw [contact_scalarCovariantDerivative_eq_recentered source current point]
    exact recenteredScalarDifferentiable
  have innerOriginEq :
      scalarMomentumInner Contact 0 = scalarMomentumInner Recentered 0 := by
    apply Prod.ext
    · change Contact.coframe 0 = Recentered.coframe 0
      unfold Contact sourceActionGeneratedCartanECConstraintCauchyContact
      rw [sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe]
      exact
        identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin
          _ _
    · change holonomicScalarCovariantDerivative Contact 0 =
        holonomicScalarCovariantDerivative Recentered 0
      exact congrFun
        (contact_scalarCovariantDerivative_eq_recentered source current point) 0
  have contactInnerDifferentiable :
      DifferentiableAt ℝ (scalarMomentumInner Contact) 0 := by
    unfold scalarMomentumInner
    exact contactCoframeDifferentiable.prodMk contactScalarDifferentiable
  have recenteredInnerDifferentiable :
      DifferentiableAt ℝ (scalarMomentumInner Recentered) 0 := by
    unfold scalarMomentumInner
    exact recenteredCoframeDifferentiable.prodMk
      recenteredScalarDifferentiable
  have innerFderivEq :
      fderiv ℝ (scalarMomentumInner Contact) 0 =
        fderiv ℝ (scalarMomentumInner Recentered) 0 := by
    unfold scalarMomentumInner
    let commonDerivative :=
      (fderiv ℝ Recentered.coframe 0).prod
        (fderiv ℝ
          (holonomicScalarCovariantDerivative Recentered) 0)
    have contactDerivative : HasFDerivAt
        (fun candidate : BasePoint =>
          (Contact.coframe candidate,
            holonomicScalarCovariantDerivative Contact candidate))
        commonDerivative 0 := by
      apply HasFDerivAt.prodMk
      · rw [← contactCoframeFderivEq]
        exact contactCoframeDifferentiable.hasFDerivAt
      · rw [← contact_scalarCovariantDerivative_eq_recentered
          source current point]
        exact contactScalarDifferentiable.hasFDerivAt
    have recenteredDerivative : HasFDerivAt
        (fun candidate : BasePoint =>
          (Recentered.coframe candidate,
            holonomicScalarCovariantDerivative Recentered candidate))
        commonDerivative 0 :=
      HasFDerivAt.prodMk recenteredCoframeDifferentiable.hasFDerivAt
        recenteredScalarDifferentiable.hasFDerivAt
    exact contactDerivative.fderiv.trans recenteredDerivative.fderiv.symm
  have recenteredCoframeOrigin :
      Recentered.coframe 0 = current.coframe point :=
    fullyRecenterHolonomicConfiguration_coframe_origin current point
  have compositionFderivEq
      (direction : ScalarCoordinateCarrier)
      (derivativeDirection : LorentzianIndex) :
      fderiv ℝ
          (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
            scalarMomentumInner Contact) 0 =
        fderiv ℝ
          (scalarMomentumCoframeCovariantReadout direction derivativeDirection ∘
            scalarMomentumInner Recentered) 0 := by
    let outer :=
      scalarMomentumCoframeCovariantReadout direction derivativeDirection
    have outerAtRecentered : DifferentiableAt ℝ outer
        (scalarMomentumInner Recentered 0) := by
      change DifferentiableAt ℝ outer
        (Recentered.coframe 0,
          holonomicScalarCovariantDerivative Recentered 0)
      rw [recenteredCoframeOrigin]
      exact
        (scalarMomentumCoframeCovariantReadout_contDiffAt direction
          derivativeDirection (current.coframe point)
          currentCoframeNondegenerate
          (holonomicScalarCovariantDerivative Recentered 0)).differentiableAt
          (by simp)
    have outerAtContact : DifferentiableAt ℝ outer
        (scalarMomentumInner Contact 0) := by
      rw [innerOriginEq]
      exact outerAtRecentered
    change
      fderiv ℝ (outer ∘ scalarMomentumInner Contact) 0 =
        fderiv ℝ (outer ∘ scalarMomentumInner Recentered) 0
    rw [fderiv_comp 0 outerAtContact contactInnerDifferentiable,
      fderiv_comp 0 outerAtRecentered recenteredInnerDifferentiable,
      innerOriginEq]
    exact congrArg
      (fun innerDerivative :
          BasePoint →L[ℝ]
            (LorentzianCoframe ×
              (LorentzianIndex → ScalarCoordinateCarrier)) =>
        (fderiv ℝ outer (scalarMomentumInner Recentered 0)).comp
          innerDerivative)
      innerFderivEq
  change
    (fun direction =>
      scalarDifferentialMomentumDivergence source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) direction point) -
        (fun direction =>
          scalarDifferentialMomentumDivergence source Contact direction 0) = 0
  funext direction
  rw [Pi.sub_apply, Pi.zero_apply,
    globalOperator_scalarDifferentialMomentumDivergence
      source current direction point]
  have contactDivergence :
      scalarDifferentialMomentumDivergence source Contact direction 0 =
        scalarDifferentialMomentumDivergence source current direction point := by
    calc
      _ = scalarDifferentialMomentumDivergence source Recentered direction 0 := by
        unfold scalarDifferentialMomentumDivergence
        apply Finset.sum_congr rfl
        intro derivativeDirection _
        unfold fieldDirectionalDerivative
        rw [scalarDifferentialMomentum_eq_readout,
          scalarDifferentialMomentum_eq_readout]
        change
          (fderiv ℝ
            (scalarMomentumCoframeCovariantReadout direction
                derivativeDirection ∘ scalarMomentumInner Contact) 0)
              (coordinateDirection derivativeDirection) =
            (fderiv ℝ
              (scalarMomentumCoframeCovariantReadout direction
                  derivativeDirection ∘ scalarMomentumInner Recentered) 0)
                (coordinateDirection derivativeDirection)
        rw [compositionFderivEq direction derivativeDirection]
      _ = scalarDifferentialMomentumDivergence source current direction point :=
        congrFun
          (scalarDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
            source current point) direction
  rw [contactDivergence]
  exact sub_self _

/-- The matter-divergence coordinate of the assembly closes at an exact
occurrence whose actual current has the identity coframe first jet and whose
coframe/conjugate-matter fields are differentiable there.  Both the generated
contact and the canonical recentering are compared through the same frozen
identity-coframe readout, so no target divergence or zero fibre is assumed. -/
theorem
    candidateAssemblySeam_matterDifferentialMomentumDivergence_zero_of_identityFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (currentCoframeComponents : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => current.coframe candidate internal coordinate)
        point)
    (currentConjugateMatterCoordinatesDifferentiable :
      DifferentiableAt ℝ
        (holonomicConjugateMatterCoordinates current) point)
    (currentFirstJet :
      holonomicCoframeFirstJetAt current.coframe point =
        identityCoframeMatterGeometry) :
    (candidateAssemblySeam source current point
      ).matterDifferentialMomentumDivergence = 0 := by
  let Contact :=
    sourceActionGeneratedCartanECConstraintCauchyContact source current point
  let Recentered := fullyRecenterHolonomicConfiguration current point
  have currentCoframeDifferentiable :
      DifferentiableAt ℝ current.coframe point :=
    coframe_differentiableAt_of_components current.coframe point
      currentCoframeComponents
  have currentCoframeAtTranslated : DifferentiableAt ℝ current.coframe
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using currentCoframeDifferentiable
  have recenteredCoframeDifferentiable :
      DifferentiableAt ℝ Recentered.coframe 0 := by
    change DifferentiableAt ℝ
      (current.coframe ∘ canonicalSpacetimeContactTranslation point) 0
    exact currentCoframeAtTranslated.comp 0 (by
      unfold canonicalSpacetimeContactTranslation
      fun_prop)
  have contactCoframeDifferentiable :
      DifferentiableAt ℝ Contact.coframe 0 :=
    contact_coframe_differentiableAt_of_components source current point
      currentCoframeComponents
  have contactFirstJet :
      holonomicCoframeFirstJetAt Contact.coframe 0 =
        identityCoframeMatterGeometry :=
    (contact_coframeFirstJet_origin_of_components source current point
      currentCoframeComponents).trans currentFirstJet
  have recenteredFirstJet :
      holonomicCoframeFirstJetAt Recentered.coframe 0 =
        identityCoframeMatterGeometry :=
    (fullyRecenterHolonomicConfiguration_coframeFirstJet_origin current point
      ).trans currentFirstJet
  have currentCoordinatesAtTranslated : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current)
      (canonicalSpacetimeContactTranslation point 0) := by
    simpa using currentConjugateMatterCoordinatesDifferentiable
  have recenteredCoordinatesDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates Recentered) 0 := by
    change DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates current ∘
        canonicalSpacetimeContactTranslation point) 0
    exact currentCoordinatesAtTranslated.comp 0 (by
      unfold canonicalSpacetimeContactTranslation
      fun_prop)
  have contactCoordinatesDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates Contact) 0 := by
    rw [show holonomicConjugateMatterCoordinates Contact =
        holonomicConjugateMatterCoordinates Recentered by
      funext candidate
      unfold holonomicConjugateMatterCoordinates
      rw [contact_conjugateMatter source current point]]
    exact recenteredCoordinatesDifferentiable
  have identityComparisonDivergenceEq
      (direction : MatterCoordinateCarrier) :
      matterDifferentialMomentumDivergence source
          (identityCoframeComparison Contact) direction 0 =
        matterDifferentialMomentumDivergence source
          (identityCoframeComparison Recentered) direction 0 := by
    unfold matterDifferentialMomentumDivergence
    apply Finset.sum_congr rfl
    intro derivativeDirection _
    unfold fieldDirectionalDerivative matterDifferentialMomentum
      matterDifferentialVariationVector generatedVolumeDensity
    simp only [toContinuumPointField, identityCoframeComparison_coframe,
      identityCoframeComparison_conjugateMatter]
    rw [contact_conjugateMatter source current point]
  have contactDivergence
      (direction : MatterCoordinateCarrier) :
      matterDifferentialMomentumDivergence source Contact direction 0 =
        matterDifferentialMomentumDivergence source current direction point := by
    calc
      _ = matterDifferentialMomentumDivergence source
            (identityCoframeComparison Contact) direction 0 :=
        matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
          source Contact 0 contactCoframeDifferentiable
          contactCoordinatesDifferentiable contactFirstJet direction
      _ = matterDifferentialMomentumDivergence source
            (identityCoframeComparison Recentered) direction 0 :=
        identityComparisonDivergenceEq direction
      _ = matterDifferentialMomentumDivergence source Recentered direction 0 :=
        (matterDifferentialMomentumDivergence_eq_identityCoframeComparison_of_identity_firstJet
          source Recentered 0 recenteredCoframeDifferentiable
          recenteredCoordinatesDifferentiable recenteredFirstJet direction).symm
      _ = matterDifferentialMomentumDivergence source current direction point :=
        congrFun
          (matterDifferentialMomentumDivergence_fullyRecenter_origin_unconditional
            source current point) direction
  change
    (fun direction =>
      matterDifferentialMomentumDivergence source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) direction point) -
        (fun direction =>
          matterDifferentialMomentumDivergence source Contact direction 0) = 0
  funext direction
  rw [Pi.sub_apply, Pi.zero_apply,
    globalOperator_matterDifferentialMomentumDivergence
      source current direction point,
    contactDivergence direction]
  exact sub_self _

private theorem candidateAssemblySeam_gaugeCurvature_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (candidateAssemblySeam source current point).gaugeCurvature = 0 := by
  change
    holonomicGaugeCurvature
          (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
            source current) point -
        holonomicGaugeCurvature
          (sourceActionGeneratedCartanECConstraintCauchyContact
            source current point) 0 =
      0
  rw [globalOperator_gaugeCurvature source current point,
    contact_gaugeCurvature_origin source current point]
  exact sub_self _

private theorem candidateAssemblySeam_scalarCovariantDerivative_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (candidateAssemblySeam source current point
      ).scalarCovariantDerivative = 0 := by
  change
    holonomicScalarCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
            source current) point -
        holonomicScalarCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyContact
            source current point) 0 =
      0
  rw [globalOperator_scalarCovariantDerivative source current point,
    contact_scalarCovariantDerivative_origin source current point]
  exact sub_self _

private theorem candidateAssemblySeam_matterCovariantDerivative_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (candidateAssemblySeam source current point
      ).matterCovariantDerivative = 0 := by
  change
    holonomicMatterCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
            source current) point -
        holonomicMatterCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyContact
            source current point) 0 =
      0
  rw [globalOperator_matterCovariantDerivative_eq_contact_origin
    source current point]
  exact sub_self _

private theorem candidateAssemblySeam_p286GaugeAuxiliaryExteriorCovariantDerivative_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (candidateAssemblySeam source current point
      ).p286GaugeAuxiliaryExteriorCovariantDerivative = 0 := by
  change
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
            source current) point -
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          (sourceActionGeneratedCartanECConstraintCauchyContact
            source current point) 0 =
      0
  rw [globalOperator_p286GaugeAuxiliaryExteriorCovariantDerivative
      source current point,
    contact_p286GaugeAuxiliaryExteriorCovariantDerivative_origin
      source current point]
  exact sub_self _

/-- Four derived coordinates of every source/current-only assembly seam close
for arbitrary input.  The remaining four coordinates are preserved verbatim;
no fixed-current regularity or target-zero premise is hidden in this readout. -/
theorem candidateAssemblySeam_eq_openCoordinatesOnly
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    candidateAssemblySeam source current point =
      { gravityCurvature :=
          (candidateAssemblySeam source current point).gravityCurvature
        gaugeCurvature := 0
        scalarCovariantDerivative := 0
        matterCovariantDerivative := 0
        gravityAuxiliaryExteriorCovariantDerivative :=
          (candidateAssemblySeam source current point
            ).gravityAuxiliaryExteriorCovariantDerivative
        p286GaugeAuxiliaryExteriorCovariantDerivative := 0
        scalarDifferentialMomentumDivergence :=
          (candidateAssemblySeam source current point
            ).scalarDifferentialMomentumDivergence
        matterDifferentialMomentumDivergence :=
          (candidateAssemblySeam source current point
            ).matterDifferentialMomentumDivergence } := by
  apply CompleteJointActionJetAssemblySeam.ext
  · rfl
  · exact candidateAssemblySeam_gaugeCurvature_zero source current point
  · exact
      candidateAssemblySeam_scalarCovariantDerivative_zero source current point
  · exact
      candidateAssemblySeam_matterCovariantDerivative_zero source current point
  · rfl
  · exact
      candidateAssemblySeam_p286GaugeAuxiliaryExteriorCovariantDerivative_zero
        source current point
  · rfl
  · rfl

/-- Exact generic closure boundary for the source/current-only assembly.
Four coordinates close unconditionally; the whole seam vanishes exactly when
the four genuinely open coordinates vanish. -/
theorem candidateAssemblySeam_eq_zero_iff_openCoordinates_eq_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    candidateAssemblySeam source current point = 0 ↔
      (candidateAssemblySeam source current point).gravityCurvature = 0 ∧
      (candidateAssemblySeam source current point
        ).gravityAuxiliaryExteriorCovariantDerivative = 0 ∧
      (candidateAssemblySeam source current point
        ).scalarDifferentialMomentumDivergence = 0 ∧
      (candidateAssemblySeam source current point
        ).matterDifferentialMomentumDivergence = 0 := by
  constructor
  · intro seamZero
    rw [seamZero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨gravityCurvatureZero, gravityAuxiliaryZero,
      scalarDivergenceZero, matterDivergenceZero⟩
    apply CompleteJointActionJetAssemblySeam.ext
    · exact gravityCurvatureZero
    · exact candidateAssemblySeam_gaugeCurvature_zero source current point
    · exact
        candidateAssemblySeam_scalarCovariantDerivative_zero source current point
    · exact
        candidateAssemblySeam_matterCovariantDerivative_zero source current point
    · exact gravityAuxiliaryZero
    · exact
        candidateAssemblySeam_p286GaugeAuxiliaryExteriorCovariantDerivative_zero
          source current point
    · exact scalarDivergenceZero
    · exact matterDivergenceZero

private theorem candidateAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
    (point : BasePoint) :
    (candidateAssemblySeam Source Current point
      ).gravityAuxiliaryExteriorCovariantDerivative = 0 := by
  apply
    candidateAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero_of_currentCoframeDifferentiableAt
  intro internal coordinate
  rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
  fun_prop

private theorem candidateAssemblySeam_scalarDifferentialMomentumDivergence_zero
    (point : BasePoint) :
    (candidateAssemblySeam Source Current point
      ).scalarDifferentialMomentumDivergence = 0 := by
  apply
    candidateAssemblySeam_scalarDifferentialMomentumDivergence_zero_of_currentLocalRegularity
  · intro internal coordinate
    rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
    fun_prop
  · have covariantSmooth : ContDiff ℝ ∞
        (holonomicScalarCovariantDerivative Current) := by
      apply contDiff_pi'
      intro direction
      exact holonomicScalarCovariantDerivative_contDiff
        Current current_smooth direction
    exact (covariantSmooth.differentiable (by simp)).differentiableAt
  · rw [fixedP506L0CartanECCauchyTemporalInput_coframe_eq_one]
    norm_num

private theorem candidateAssemblySeam_matterDifferentialMomentumDivergence_zero
    (point : BasePoint) :
    (candidateAssemblySeam Source Current point
      ).matterDifferentialMomentumDivergence = 0 := by
  change
    (fun direction =>
      matterDifferentialMomentumDivergence Source Candidate direction point) -
        (fun direction =>
          matterDifferentialMomentumDivergence Source
            (sourceActionGeneratedCartanECConstraintCauchyContact
              Source Current point) direction 0) =
      0
  funext direction
  rw [Pi.sub_apply, Pi.zero_apply,
    globalOperator_matterDifferentialMomentumDivergence
      Source Current direction point,
    contact_matterDifferentialMomentumDivergence_eq_current point direction]
  exact sub_self _

/-- The source/current-only whole-spacetime assembly has exactly one open
derived coordinate: gravity curvature.  Every first-jet and non-gravity
second-order seam is generated to zero by the same contact family. -/
theorem candidateAssemblySeam_eq_gravityCurvatureOnly
    (point : BasePoint) :
    candidateAssemblySeam Source Current point =
      { gravityCurvature :=
          (candidateAssemblySeam Source Current point).gravityCurvature
        gaugeCurvature := 0
        scalarCovariantDerivative := 0
        matterCovariantDerivative := 0
        gravityAuxiliaryExteriorCovariantDerivative := 0
        p286GaugeAuxiliaryExteriorCovariantDerivative := 0
        scalarDifferentialMomentumDivergence := 0
        matterDifferentialMomentumDivergence := 0 } := by
  apply CompleteJointActionJetAssemblySeam.ext
  · rfl
  · exact candidateAssemblySeam_gaugeCurvature_zero Source Current point
  · exact
      candidateAssemblySeam_scalarCovariantDerivative_zero Source Current point
  · exact
      candidateAssemblySeam_matterCovariantDerivative_zero Source Current point
  · exact
      candidateAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
        point
  · exact
      candidateAssemblySeam_p286GaugeAuxiliaryExteriorCovariantDerivative_zero
        Source Current point
  · exact
      candidateAssemblySeam_scalarDifferentialMomentumDivergence_zero point
  · exact
      candidateAssemblySeam_matterDifferentialMomentumDivergence_zero point

theorem candidateAssemblySeam_eq_zero_iff_gravityCurvature_eq_zero
    (point : BasePoint) :
    candidateAssemblySeam Source Current point = 0 ↔
      (candidateAssemblySeam Source Current point).gravityCurvature = 0 := by
  constructor
  · intro seamZero
    rw [seamZero]
    rfl
  · intro gravityCurvatureZero
    apply CompleteJointActionJetAssemblySeam.ext
    · exact gravityCurvatureZero
    · exact candidateAssemblySeam_gaugeCurvature_zero Source Current point
    · exact
        candidateAssemblySeam_scalarCovariantDerivative_zero Source Current point
    · exact
        candidateAssemblySeam_matterCovariantDerivative_zero Source Current point
    · exact
        candidateAssemblySeam_gravityAuxiliaryExteriorCovariantDerivative_zero
          point
    · exact
        candidateAssemblySeam_p286GaugeAuxiliaryExteriorCovariantDerivative_zero
          Source Current point
    · exact
        candidateAssemblySeam_scalarDifferentialMomentumDivergence_zero point
    · exact
        candidateAssemblySeam_matterDifferentialMomentumDivergence_zero point

/-- Whole-carrier naturality of the diagonal common write.  Primitive values
and both connection values agree definitionally; the one exhaustive seam
records every possible derived-jet mismatch. -/
theorem candidate_actionJet_naturality
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      pointwiseActionJetWithCompleteJointAssemblySeam
        (contactActionJet source current point)
        (candidateAssemblySeam source current point) := by
  apply DiracDualFormNativePointwiseActionJetCarrier.ext
  · apply StageNineContinuumPointField.ext
    · rfl
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        candidateAssemblySeam, completeJointActionJetAssemblySeam]
    · rfl
    · rfl
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        candidateAssemblySeam, completeJointActionJetAssemblySeam]
    · rfl
    · rfl
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        candidateAssemblySeam, completeJointActionJetAssemblySeam]
    · rfl
    · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
        candidateAssemblySeam, completeJointActionJetAssemblySeam]
    · rfl
  · rfl
  · rfl
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      candidateAssemblySeam, completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      candidateAssemblySeam, completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      candidateAssemblySeam, completeJointActionJetAssemblySeam]
  · simp [pointwiseActionJetWithCompleteJointAssemblySeam,
      candidateAssemblySeam, completeJointActionJetAssemblySeam]

theorem candidate_actionJet_eq_contact_of_assemblySeam_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (seamZero : candidateAssemblySeam source current point = 0) :
    generatedDiracDualFormNativePointwiseActionJet source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      contactActionJet source current point := by
  rw [candidate_actionJet_naturality, seamZero,
    pointwiseActionJetWithCompleteJointAssemblySeam_zero]

theorem candidate_residual_eq_contact_of_assemblySeam_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (seamZero : candidateAssemblySeam source current point = 0) :
    diracDualFormNativePointwiseJointResidual source
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          source current) point =
      diracDualFormNativePointwiseJointResidual source
        (sourceActionGeneratedCartanECConstraintCauchyContact
          source current point) 0 := by
  exact
    diracDualFormNativePointwiseJointResidual_eq_of_generatedActionJet_eq
      source
      (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
        source current)
      (sourceActionGeneratedCartanECConstraintCauchyContact
        source current point)
      point 0
      (candidate_actionJet_eq_contact_of_assemblySeam_zero
        source current point seamZero)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyWholeSpacetimeAssembly
