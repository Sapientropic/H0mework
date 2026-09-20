import H0mework.Physics.Matter.MatterActionTimeVelocity
import H0mework.Physics.Matter.MatterPointwiseEquation

/-!
# S9-C3h97: action-generated conjugate-matter time velocity

The adjoint Dirac equation is first order in the independent conjugate matter
field.  On the identity-coframe Cauchy domain, write

`Pμ ψ = i γμ ψ`.

The primitive Cauchy state supplies the conjugate-field value and its three
spatial derivatives.  The actual matter action supplies the algebraic
operator `A`.  The temporal adjoint action law is therefore

`λ̇ ∘ P₀ + ∑ᵢ (∂ᵢ λ) ∘ Pᵢ = λ ∘ A`.

Because `P₀² = 1`, this law uniquely generates

`λ̇ = (λ ∘ A - ∑ᵢ (∂ᵢ λ) ∘ Pᵢ) ∘ P₀`.

The generated dual first jet is installed in the C3h96 synchronized
gravity--P286--matter actual lift before any Euler--Lagrange residual is
read.  The pointwise residual is used only as a downstream acceptance law.
No endpoint, residual preimage, supplied velocity, equation witness, or
branch selector occurs in the producer mouth.

This is an identity-coframe local first-jet checkpoint.  It does not claim a
generic evolving-coframe adjoint equation or a finite-time solution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineConjugateMatterActionTimeVelocity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionVariationDensity
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## The adjoint temporal principal action -/

/-- Identity-coframe principal action `Pμ = i γμ` as an actual complex-linear
endomorphism of the matter carrier. -/
def identityCoframeMatterPrincipal
    (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracMatrixMatterAction (diracGamma direction)

@[simp] theorem identityCoframeMatterPrincipal_apply
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    identityCoframeMatterPrincipal direction matter =
      Complex.I • diracMatrixMatterAction (diracGamma direction) matter :=
  rfl

/-- The temporal principal endomorphism is involutive. -/
theorem identityCoframeMatterPrincipal_time_involutive
    (matter : DiracExteriorMatterCarrier) :
    identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
          matter) =
      matter := by
  simpa [identityCoframeMatterPrincipal,
    identityCoframeMatterTimePrincipal,
    canonicalLorentzianTimeDirection] using
    identityCoframeMatterTimePrincipal_involutive matter

/-! ## Primitive spatial dual jet and action operator -/

/-- Spatial derivative of the primitive conjugate-matter coordinates on the
selected Cauchy slice. -/
def cauchyConjugateMatterSpatialDerivativeCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) : MatterCoordinateCarrier :=
  fderiv ℝ
    (fun candidate => matterDualCoordinates (state.conjugateMatter candidate))
    space
    (canonicalSpatialCoordinateDirection direction)

/-- The spatial derivative reconstructed as the full complex-linear dual.
This is a derivative of primitive Cauchy data, not a residual readout. -/
def cauchyConjugateMatterSpatialDerivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  matterDualOfCoordinates
    (cauchyConjugateMatterSpatialDerivativeCoordinate state space direction)

/-- Lorentz plus P286 action on an arbitrary matter variation, evaluated
from primitive Cauchy connection data. -/
def cauchyMatterVariationConnectionOperator
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (state.gravityConnection space) direction) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (state.gaugeConnection space direction))

@[simp] theorem cauchyMatterVariationConnectionOperator_apply
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex)
    (matter : DiracExteriorMatterCarrier) :
    cauchyMatterVariationConnectionOperator state space direction matter =
      diracMatrixMatterAction
          (diracSpinConnectionLift
            (state.gravityConnection space) direction)
          matter +
        diracExteriorMotherLieAction
          (p286LieBlockEmbed (state.gaugeConnection space direction))
          matter :=
  rfl

/-- The full algebraic operator `A` in the adjoint matter equation at the
identity-coframe Cauchy point.  It is assembled directly from the actual
Lorentz/P286 action and the Yukawa action. -/
def actionGeneratedMatterAlgebraicOperator
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        (diracMatrixMatterAction (diracGamma direction)).comp
          (cauchyMatterVariationConnectionOperator state space direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (state.scalar space))

/-- Spatial part of the adjoint principal transport, generated from the
primitive Cauchy dual jet. -/
def actionGeneratedConjugateMatterSpatialTransport
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ direction : Fin 3,
    (cauchyConjugateMatterSpatialDerivative state space direction).comp
      (identityCoframeMatterPrincipal direction.succ)

/-- All action-known terms before the temporal dual derivative. -/
def actionGeneratedConjugateMatterKnownDual
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  (state.conjugateMatter space).comp
      (actionGeneratedMatterAlgebraicOperator state space) -
    actionGeneratedConjugateMatterSpatialTransport state space

/-! ## Unique action-generated temporal dual derivative -/

/-- The actual adjoint action law over a fixed primitive Cauchy state. -/
def IdentityCoframeConjugateMatterTimeActionLaw
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  timeDerivative.comp
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) +
      actionGeneratedConjugateMatterSpatialTransport state space =
    (state.conjugateMatter space).comp
      (actionGeneratedMatterAlgebraicOperator state space)

/-- Temporal dual derivative generated by the adjoint action and the
involutive temporal principal symbol. -/
def actionGeneratedConjugateMatterTimeDerivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  (actionGeneratedConjugateMatterKnownDual state space).comp
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

theorem actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    IdentityCoframeConjugateMatterTimeActionLaw state space
      (actionGeneratedConjugateMatterTimeDerivative state space) := by
  apply LinearMap.ext
  intro matter
  simp only [actionGeneratedConjugateMatterTimeDerivative,
    actionGeneratedConjugateMatterKnownDual, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply]
  rw [identityCoframeMatterPrincipal_time_involutive]
  abel

/-- The adjoint action law has no hidden temporal branch. -/
theorem identityCoframeConjugateMatterTimeActionLaw_unique
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw :
      IdentityCoframeConjugateMatterTimeActionLaw state space first)
    (secondLaw :
      IdentityCoframeConjugateMatterTimeActionLaw state space second) :
    first = second := by
  have composedEqual :
      first.comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) =
        second.comp
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection) := by
    apply LinearMap.ext
    intro matter
    have firstAt := LinearMap.congr_fun firstLaw matter
    have secondAt := LinearMap.congr_fun secondLaw matter
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at firstAt secondAt
    exact add_right_cancel (firstAt.trans secondAt.symm)
  apply LinearMap.ext
  intro matter
  calc
    first matter =
        first
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      rw [identityCoframeMatterPrincipal_time_involutive]
    _ =
        second
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      exact LinearMap.congr_fun composedEqual
        (identityCoframeMatterPrincipal
          canonicalLorentzianTimeDirection matter)
    _ = second matter := by
      rw [identityCoframeMatterPrincipal_time_involutive]

/-- At identity coframe the adjoint Dirac law is a genuine evolution law:
the involutive temporal principal symbol selects exactly one time derivative
for every primitive Cauchy state.  Thus this equation contributes no separate
Cauchy compatibility constraint. -/
theorem identityCoframeConjugateMatterTimeActionLaw_iff
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier) :
    IdentityCoframeConjugateMatterTimeActionLaw state space candidate ↔
      candidate =
        actionGeneratedConjugateMatterTimeDerivative state space := by
  constructor
  · intro candidateLaw
    exact identityCoframeConjugateMatterTimeActionLaw_unique
      state space candidate
        (actionGeneratedConjugateMatterTimeDerivative state space)
      candidateLaw
      (actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
        state space)
  · rintro rfl
    exact actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
      state space

/-! ## Primitive affine conjugate-matter germ -/

/-- Complete generated dual first jet: temporal action output followed by
the three actual spatial Cauchy derivatives. -/
def actionGeneratedConjugateMatterLocalJet
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  ![
    actionGeneratedConjugateMatterTimeDerivative state space,
    cauchyConjugateMatterSpatialDerivative state space 0,
    cauchyConjugateMatterSpatialDerivative state space 1,
    cauchyConjugateMatterSpatialDerivative state space 2
  ] direction

/-- Affine primitive dual field carrying the generated first jet. -/
def actionGeneratedConjugateMatterLocalField
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  state.conjugateMatter space +
    ∑ direction : LorentzianIndex,
      (localBaseCoordinate direction point) •
        actionGeneratedConjugateMatterLocalJet state space direction

/-- Evaluation of the affine increment as a real continuous linear map. -/
def actionGeneratedConjugateMatterLocalEvaluationIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    BasePoint →L[ℝ] ℂ :=
  ∑ direction : LorentzianIndex,
    (localBaseCoordinate direction).smulRight
      (actionGeneratedConjugateMatterLocalJet state space direction matter)

theorem actionGeneratedConjugateMatterLocalField_apply
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (matter : DiracExteriorMatterCarrier) :
    actionGeneratedConjugateMatterLocalField state space point matter =
      state.conjugateMatter space matter +
        actionGeneratedConjugateMatterLocalEvaluationIncrement
          state space matter point := by
  simp [actionGeneratedConjugateMatterLocalField,
    actionGeneratedConjugateMatterLocalEvaluationIncrement]

theorem actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    actionGeneratedConjugateMatterLocalEvaluationIncrement state space matter
        (coordinateDirection direction) =
      actionGeneratedConjugateMatterLocalJet state space direction matter := by
  fin_cases direction <;>
    simp [actionGeneratedConjugateMatterLocalEvaluationIncrement,
      actionGeneratedConjugateMatterLocalJet, localBaseCoordinate,
      coordinateDirection, Fin.sum_univ_four]

@[simp] theorem actionGeneratedConjugateMatterLocalField_origin
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterLocalField state space 0 =
      state.conjugateMatter space := by
  apply LinearMap.ext
  intro matter
  simp [actionGeneratedConjugateMatterLocalField_apply,
    actionGeneratedConjugateMatterLocalEvaluationIncrement]

theorem actionGeneratedConjugateMatterLocalField_derivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          actionGeneratedConjugateMatterLocalField state space point matter)
        0 direction =
      actionGeneratedConjugateMatterLocalJet state space direction matter := by
  rw [show
    (fun point =>
      actionGeneratedConjugateMatterLocalField state space point matter) =
      fun point =>
        state.conjugateMatter space matter +
          actionGeneratedConjugateMatterLocalEvaluationIncrement
            state space matter point by
    funext point
    exact actionGeneratedConjugateMatterLocalField_apply
      state space point matter]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_add]
  rw [(actionGeneratedConjugateMatterLocalEvaluationIncrement
    state space matter).hasFDerivAt.fderiv]
  exact
    actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection
      state space matter direction

theorem actionGeneratedConjugateMatterLocalField_real_derivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (actionGeneratedConjugateMatterLocalField state space point
            matter).re)
        0 direction =
      (actionGeneratedConjugateMatterLocalJet state space direction
        matter).re := by
  rw [show
    (fun point =>
      (actionGeneratedConjugateMatterLocalField state space point matter).re) =
      fun point =>
        (state.conjugateMatter space matter).re +
          (Complex.reCLM.comp
            (actionGeneratedConjugateMatterLocalEvaluationIncrement
              state space matter)) point by
    funext point
    rw [actionGeneratedConjugateMatterLocalField_apply]
    rfl]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_add]
  rw [((Complex.reCLM.comp
    (actionGeneratedConjugateMatterLocalEvaluationIncrement
      state space matter))).hasFDerivAt.fderiv]
  change
    (actionGeneratedConjugateMatterLocalEvaluationIncrement
      state space matter (coordinateDirection direction)).re =
      _
  rw [
    actionGeneratedConjugateMatterLocalEvaluationIncrement_coordinateDirection]

theorem actionGeneratedConjugateMatterLocalField_smooth
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ fun point =>
      actionGeneratedConjugateMatterLocalField state space point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ))) := by
  rw [show
    (fun point =>
      actionGeneratedConjugateMatterLocalField state space point
        (matterCoordinateEquiv.symm
          (EuclideanSpace.single index (1 : ℂ)))) =
      fun point =>
        state.conjugateMatter space
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) +
          actionGeneratedConjugateMatterLocalEvaluationIncrement
            state space
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) point by
    funext point
    exact actionGeneratedConjugateMatterLocalField_apply
      state space point _]
  exact contDiff_const.add
    (actionGeneratedConjugateMatterLocalEvaluationIncrement state space
      (matterCoordinateEquiv.symm
        (EuclideanSpace.single index (1 : ℂ)))).contDiff

/-! ## Synchronized primitive actual output -/

/-- C3h96 actual output with the independently generated adjoint dual germ
installed before equation acceptance. -/
def sourceActionGeneratedMatterDualLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  { sourceActionGeneratedMatterLocalActualLift source state space with
    conjugateMatter :=
      actionGeneratedConjugateMatterLocalField state space }

theorem sourceActionGeneratedMatterDualLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedMatterDualLocalActualLift source state space).Smooth := by
  have baseSmooth :=
    sourceActionGeneratedMatterLocalActualLift_smooth source state space
  rcases baseSmooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, _conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth,
      actionGeneratedConjugateMatterLocalField_smooth state space⟩

theorem sourceActionGeneratedMatterDualLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedMatterDualLocalActualLift source state
      space).Nondegenerate := by
  exact sourceActionGeneratedMatterLocalActualLift_nondegenerate
    source state space nondegenerate

@[simp] theorem sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedMatterDualLocalActualLift source state
      space).conjugateMatter 0 =
      state.conjugateMatter space := by
  exact actionGeneratedConjugateMatterLocalField_origin state space

theorem sourceActionGeneratedMatterDualLocalActualLift_conjugateDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          (sourceActionGeneratedMatterDualLocalActualLift source state
            space).conjugateMatter point matter)
        0 direction =
      actionGeneratedConjugateMatterLocalJet state space direction matter := by
  exact actionGeneratedConjugateMatterLocalField_derivative
    state space matter direction

/-! ## Action decomposition at the common origin -/

theorem sourceActionGeneratedMatterDualLocalActualLift_variationConnection_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    holonomicMatterVariationAlgebraicDirection
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        direction 0 formDirection =
      cauchyMatterVariationConnectionOperator state space formDirection
        (matterCoordinateEquiv.symm direction) := by
  unfold holonomicMatterVariationAlgebraicDirection
    cauchyMatterVariationConnectionOperator
    sourceActionGeneratedMatterDualLocalActualLift
    sourceActionGeneratedMatterLocalActualLift
  rw [
    sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin]
  rw [show
    (sourceActionGeneratedGravityGaugeLocalActualLift source state
      space).gaugeConnection 0 =
        state.gaugeConnection space by
    funext candidate
    exact sourceGeneratedP286ActionLocalConnection_origin
      source state space candidate]
  rfl

theorem sourceActionGeneratedMatterDualLocalActualLift_differentialVector_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialVariationVector source 0
        (toContinuumPointField
          (sourceActionGeneratedMatterDualLocalActualLift source state
            space) 0)
        direction derivativeDirection =
      identityCoframeMatterPrincipal derivativeDirection
        (matterCoordinateEquiv.symm direction) := by
  unfold matterDifferentialVariationVector
  simp only [toContinuumPointField]
  rw [show
    (sourceActionGeneratedMatterDualLocalActualLift source state
      space).coframe 0 =
        (1 : LorentzianCoframe) by exact identityCoframe]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  rw [inverseCoframeDiracGamma_identity]
  rfl

theorem sourceActionGeneratedMatterDualLocalActualLift_algebraicVector_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicVariationVector source
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        direction 0 =
      actionGeneratedMatterAlgebraicOperator state space
        (matterCoordinateEquiv.symm direction) := by
  unfold matterAlgebraicVariationVector matterFieldVariationVector
    actionGeneratedMatterAlgebraicOperator
  rw [matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  rw [show
    (sourceActionGeneratedMatterDualLocalActualLift source state
      space).coframe 0 =
        (1 : LorentzianCoframe) by exact identityCoframe]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp_rw [
    sourceActionGeneratedMatterDualLocalActualLift_variationConnection_origin]
  rw [show
    (sourceActionGeneratedMatterDualLocalActualLift source state
      space).scalar 0 =
        state.scalar space by
    exact sourceGeneratedP286ActionLocalActualLift_scalar_origin
      source state space]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]

theorem sourceActionGeneratedMatterDualLocalActualLift_volume_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    generatedVolumeDensity
        (toContinuumPointField
          (sourceActionGeneratedMatterDualLocalActualLift source state
            space) 0) =
      1 := by
  simp [generatedVolumeDensity, toContinuumPointField,
    sourceActionGeneratedMatterDualLocalActualLift,
    sourceActionGeneratedMatterLocalActualLift,
    sourceActionGeneratedGravityGaugeLocalActualLift_coframe,
    identityCoframe]

theorem sourceActionGeneratedMatterDualLocalActualLift_differentialMomentum
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        direction derivativeDirection =
      fun point =>
        ((sourceActionGeneratedMatterDualLocalActualLift source state
            space).conjugateMatter point
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
  simp only [toContinuumPointField]
  rw [show
    (sourceActionGeneratedMatterDualLocalActualLift source state
      space).coframe point =
        (1 : LorentzianCoframe) by exact identityCoframe]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  rw [inverseCoframeDiracGamma_identity]
  simp [generatedVolumeDensity, identityCoframeMatterPrincipal]

theorem sourceActionGeneratedMatterDualLocalActualLift_momentumDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum source
          (sourceActionGeneratedMatterDualLocalActualLift source state space)
          direction derivativeDirection)
        0 derivativeDirection =
      (actionGeneratedConjugateMatterLocalJet state space derivativeDirection
        (identityCoframeMatterPrincipal derivativeDirection
          (matterCoordinateEquiv.symm direction))).re := by
  rw [
    sourceActionGeneratedMatterDualLocalActualLift_differentialMomentum
      source state space identityCoframe direction derivativeDirection]
  exact actionGeneratedConjugateMatterLocalField_real_derivative
    state space
    (identityCoframeMatterPrincipal derivativeDirection
      (matterCoordinateEquiv.symm direction))
    derivativeDirection

theorem sourceActionGeneratedMatterDualLocalActualLift_momentumDivergence_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence source
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        direction 0 =
      ∑ derivativeDirection : LorentzianIndex,
        (actionGeneratedConjugateMatterLocalJet state space
          derivativeDirection
          (identityCoframeMatterPrincipal derivativeDirection
            (matterCoordinateEquiv.symm direction))).re := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    sourceActionGeneratedMatterDualLocalActualLift_momentumDerivative_origin
      source state space identityCoframe direction derivativeDirection

theorem sourceActionGeneratedMatterDualLocalActualLift_algebraicCoefficient_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        direction 0 =
      (state.conjugateMatter space
        (actionGeneratedMatterAlgebraicOperator state space
          (matterCoordinateEquiv.symm direction))).re := by
  unfold matterAlgebraicDirectionalCoefficient
  rw [
    sourceActionGeneratedMatterDualLocalActualLift_volume_origin
      source state space identityCoframe,
    sourceActionGeneratedMatterDualLocalActualLift_algebraicVector_origin
      source state space identityCoframe direction,
    sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin]
  simp

/-- The complete generated dual first jet satisfies the complex adjoint
action balance before real-valued Euler--Lagrange acceptance is read. -/
theorem actionGeneratedConjugateMatterLocalJet_actionBalance
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matter : DiracExteriorMatterCarrier) :
    (∑ direction : LorentzianIndex,
      actionGeneratedConjugateMatterLocalJet state space direction
        (identityCoframeMatterPrincipal direction matter)) =
      state.conjugateMatter space
        (actionGeneratedMatterAlgebraicOperator state space matter) := by
  have law :=
    actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
      state space
  have atMatter := LinearMap.congr_fun law matter
  simpa [IdentityCoframeConjugateMatterTimeActionLaw,
    actionGeneratedConjugateMatterSpatialTransport,
    actionGeneratedConjugateMatterLocalJet,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_four, Fin.sum_univ_three,
    canonicalLorentzianTimeDirection, add_assoc] using atMatter

/-! ## Downstream adjoint Euler--Lagrange acceptance -/

/-- The action-generated conjugate germ satisfies the actual adjoint matter
pointwise equation at the common origin.  The residual appears only here, as
an acceptance readout of the already constructed actual output. -/
theorem sourceActionGeneratedMatterDualLocalActualLift_matterEulerLagrange_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1)
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient source
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        direction 0 =
      0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [
    sourceActionGeneratedMatterDualLocalActualLift_algebraicCoefficient_origin
      source state space identityCoframe direction,
    sourceActionGeneratedMatterDualLocalActualLift_momentumDivergence_origin
      source state space identityCoframe direction]
  have balance :=
    actionGeneratedConjugateMatterLocalJet_actionBalance state space
      (matterCoordinateEquiv.symm direction)
  have realBalance := congrArg Complex.re balance
  simp only [Complex.re_sum] at realBalance
  exact sub_eq_zero.mpr realBalance.symm

/-- Updating only the independent conjugate field preserves the C3h96
Dirac--Yukawa equation on the same generated actual output. -/
theorem sourceActionGeneratedMatterDualLocalActualLift_diracYukawa_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    generatedContinuumMatterVector source 0 0
      (toContinuumPointField
        (sourceActionGeneratedMatterDualLocalActualLift source state space)
        0) =
      0 := by
  change
    generatedContinuumMatterVector source 0 0
      (toContinuumPointField
        (sourceActionGeneratedMatterLocalActualLift source state space) 0) =
      0
  exact sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin
    source state space identityCoframe

/-- Frontier theorem: one source/Cauchy/action-generated primitive local
actual output satisfies gravity simplicity, the gravity auxiliary equation,
all six P286 auxiliary components, the Dirac--Yukawa equation, and the full
all-direction adjoint matter equation at the common origin. -/
theorem
    sourceActionGeneratedGravityGaugeMatterDualLocalActualLift_origin_system
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    let actual :=
      sourceActionGeneratedMatterDualLocalActualLift source state space
    actual.gravityAuxiliary 0 =
        physicalIIPlusBivector (actual.coframe 0) ∧
      holonomicGravityCurvature actual 0 =
        gravityInternalDualEquiv (actual.gravityAuxiliary 0) ∧
      holonomicGaugeCurvature actual 0 =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared :
              ℝ) •
            coframeGaugeSpacetimeHodgeLinear (actual.coframe 0))
          (actual.gaugeAuxiliary 0) ∧
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField actual 0) =
        0 ∧
      ∀ direction : MatterCoordinateCarrier,
        matterEulerLagrangeDirectionalCoefficient source actual direction 0 =
          0 := by
  have previous :=
    sourceActionGeneratedGravityGaugeMatterLocalActualLift_origin_system
      source state space identityCoframe
  rcases previous with
    ⟨simplicity, gravityAuxiliary, p286Auxiliary, diracYukawa⟩
  refine ⟨simplicity, gravityAuxiliary, p286Auxiliary, ?_, ?_⟩
  · exact diracYukawa
  · intro direction
    exact
      sourceActionGeneratedMatterDualLocalActualLift_matterEulerLagrange_origin
        source state space identityCoframe direction

/-! ## Positive and negative producer regressions -/

/-- The existing positive phase Cauchy state inhabits the identity-coframe
domain and the generated actual output closes the five displayed origin
equalities.  Its matter/dual sector is zero, so this is a domain/regression
checkpoint, not an interaction-sensitive producer. -/
theorem
    positiveProbe_sourceActionGeneratedGravityGaugeMatterDual_origin_system :
    let actual :=
      sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0
    actual.gravityAuxiliary 0 =
        physicalIIPlusBivector (actual.coframe 0) ∧
      holonomicGravityCurvature actual 0 =
        gravityInternalDualEquiv (actual.gravityAuxiliary 0) ∧
      holonomicGaugeCurvature actual 0 =
        liftGaugeTwoFormOperator
          (((sourceGeneratedUnifiedCouplings
              positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
            coframeGaugeSpacetimeHodgeLinear (actual.coframe 0))
          (actual.gaugeAuxiliary 0) ∧
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField actual 0) =
        0 ∧
      ∀ direction : MatterCoordinateCarrier,
        matterEulerLagrangeDirectionalCoefficient
          positiveSmoothUnifiedSource actual direction 0 =
          0 := by
  exact
    sourceActionGeneratedGravityGaugeMatterDualLocalActualLift_origin_system
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 rfl

/-- A distinct candidate temporal dual derivative cannot pass the action law.
This guards against reintroducing a supplied branch or endpoint witness. -/
theorem not_identityCoframeConjugateMatterTimeActionLaw_of_ne_generated
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateNe :
      candidate ≠
        actionGeneratedConjugateMatterTimeDerivative state space) :
    ¬ IdentityCoframeConjugateMatterTimeActionLaw state space candidate := by
  intro candidateLaw
  apply candidateNe
  exact identityCoframeConjugateMatterTimeActionLaw_unique
    state space candidate
    (actionGeneratedConjugateMatterTimeDerivative state space)
    candidateLaw
    (actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw
      state space)

end

end SaturationMonoid.PhysicsCore.StageNineConjugateMatterActionTimeVelocity
