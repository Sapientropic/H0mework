import H0mework.Physics.Gauge.GravityGaugeActionLocalActualLift
import H0mework.Physics.Matter.MatterVariation

/-!
# S9-C3h96: action-generated matter time velocity

The Dirac--Yukawa action is first order in matter.  On an identity-coframe
time slice its temporal principal operator is

`P₀ ψ = i γ⁰ ψ`.

The Clifford law makes `P₀` an involution, so the actual action uniquely
generates the temporal covariant derivative from the primitive spatial
Cauchy jet and the algebraic Yukawa term.  This module then subtracts the
already generated Lorentz/P286 connection actions to obtain the raw matter
time derivative, builds an affine primitive matter germ, and installs that
germ in the existing synchronized gravity--P286 actual lift.

The order is therefore

```text
source + primitive Cauchy state
→ actual spatial matter jet and connection actions
→ unique Dirac time velocity
→ primitive affine matter germ
→ Dirac--Yukawa equation acceptance at the origin.
```

No residual, endpoint, preimage, inverse certificate, supplied velocity, or
branch selector is consumed.  The identity-coframe hypothesis is a
structural noncharacteristic domain condition for this local checkpoint; it
is not a stored receipt or a new source slot.  The result is still a local
first-jet producer, not a finite-time matter flow or a dual-matter/coframe
development.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineMatterActionTimeVelocity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
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

/-! ## Primitive spatial jet and action-known vector -/

/-- Real Fréchet derivative of the primitive matter coordinates along one
canonical spatial direction. -/
def cauchyMatterSpatialDerivativeCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) : MatterCoordinateCarrier :=
  fderiv ℝ
    (fun candidate => matterCoordinateEquiv (state.matter candidate))
    space
    (canonicalSpatialCoordinateDirection direction)

/-- Connection action on the matter value in one spacetime direction,
computed entirely from primitive Cauchy data. -/
def cauchyMatterConnectionAction
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (state.gravityConnection space) direction)
      (state.matter space) +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (state.gaugeConnection space direction))
      (state.matter space)

/-- Full spatial covariant derivative derived from the primitive slice. -/
def cauchyMatterSpatialCovariantDerivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
      (cauchyMatterSpatialDerivativeCoordinate state space direction) +
    cauchyMatterConnectionAction state space direction.succ

/-- Identity-coframe temporal principal action `i γ⁰`. -/
def identityCoframeMatterTimePrincipal
    (matter : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 0) matter

/-- The identity-coframe temporal principal action is its own inverse. -/
theorem identityCoframeMatterTimePrincipal_involutive
    (matter : DiracExteriorMatterCarrier) :
    identityCoframeMatterTimePrincipal
        (identityCoframeMatterTimePrincipal matter) =
      matter := by
  unfold identityCoframeMatterTimePrincipal
  rw [map_smul, smul_smul, Complex.I_mul_I]
  rw [← LinearMap.comp_apply, ← diracMatrixMatterAction_mul]
  rw [show diracGamma (0 : LorentzianIndex) * diracGamma 0 =
      -(1 : DiracMatrix) by exact diracGammaZero_sq]
  funext row
  fin_cases row <;>
    simp [diracMatrixMatterAction, Matrix.neg_apply, Matrix.one_apply,
      Fin.sum_univ_four] <;>
    module

/-- All terms in the identity-coframe Dirac--Yukawa equation except the
temporal principal action. -/
def actionGeneratedMatterKnownVector
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : Fin 3,
        diracMatrixMatterAction (diracGamma direction.succ)
          (cauchyMatterSpatialCovariantDerivative state space direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (state.scalar space))
      (state.matter space)

/-- Downstream action-law predicate for a candidate temporal covariant
derivative. -/
def IdentityCoframeMatterTimeActionLaw
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (timeCovariantDerivative : DiracExteriorMatterCarrier) : Prop :=
  identityCoframeMatterTimePrincipal timeCovariantDerivative +
      actionGeneratedMatterKnownVector state space =
    0

/-! ## Action-generated time velocity -/

/-- Unique temporal covariant derivative generated by the identity-coframe
Dirac principal action. -/
def actionGeneratedMatterTimeCovariantDerivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    DiracExteriorMatterCarrier :=
  -identityCoframeMatterTimePrincipal
    (actionGeneratedMatterKnownVector state space)

theorem actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    IdentityCoframeMatterTimeActionLaw state space
      (actionGeneratedMatterTimeCovariantDerivative state space) := by
  unfold IdentityCoframeMatterTimeActionLaw
    actionGeneratedMatterTimeCovariantDerivative
  rw [show
    identityCoframeMatterTimePrincipal
        (-identityCoframeMatterTimePrincipal
          (actionGeneratedMatterKnownVector state space)) =
      -identityCoframeMatterTimePrincipal
        (identityCoframeMatterTimePrincipal
          (actionGeneratedMatterKnownVector state space)) by
    simp [identityCoframeMatterTimePrincipal]]
  rw [identityCoframeMatterTimePrincipal_involutive]
  simp

/-- The action law has exactly one temporal covariant derivative over fixed
source and Cauchy data. -/
theorem identityCoframeMatterTimeActionLaw_unique
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (first second : DiracExteriorMatterCarrier)
    (firstLaw :
      IdentityCoframeMatterTimeActionLaw state space first)
    (secondLaw :
      IdentityCoframeMatterTimeActionLaw state space second) :
    first = second := by
  have principalEqual :
      identityCoframeMatterTimePrincipal first =
        identityCoframeMatterTimePrincipal second := by
    unfold IdentityCoframeMatterTimeActionLaw at firstLaw secondLaw
    calc
      identityCoframeMatterTimePrincipal first =
          -actionGeneratedMatterKnownVector state space :=
        eq_neg_of_add_eq_zero_left firstLaw
      _ = identityCoframeMatterTimePrincipal second :=
        (eq_neg_of_add_eq_zero_left secondLaw).symm
  calc
    first =
        identityCoframeMatterTimePrincipal
          (identityCoframeMatterTimePrincipal first) :=
      (identityCoframeMatterTimePrincipal_involutive first).symm
    _ =
        identityCoframeMatterTimePrincipal
          (identityCoframeMatterTimePrincipal second) := by
      rw [principalEqual]
    _ = second :=
      identityCoframeMatterTimePrincipal_involutive second

/-- Raw primitive time derivative obtained by removing the temporal
Lorentz/P286 connection actions from the generated covariant derivative. -/
def actionGeneratedMatterRawTimeVelocity
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    DiracExteriorMatterCarrier :=
  actionGeneratedMatterTimeCovariantDerivative state space -
    cauchyMatterConnectionAction state space
      canonicalLorentzianTimeDirection

/-! ## Primitive affine matter germ -/

/-- Complete action/Cauchy-generated matter first jet in finite coordinates:
the generated time velocity followed by the three actual spatial
derivatives. -/
def actionGeneratedMatterLocalJetCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) : MatterCoordinateCarrier :=
  ![
    matterCoordinateEquiv
      (actionGeneratedMatterRawTimeVelocity state space),
    cauchyMatterSpatialDerivativeCoordinate state space 0,
    cauchyMatterSpatialDerivativeCoordinate state space 1,
    cauchyMatterSpatialDerivativeCoordinate state space 2
  ] direction

def actionGeneratedMatterLocalIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    BasePoint →L[ℝ] MatterCoordinateCarrier :=
  ∑ direction : LorentzianIndex,
    (localBaseCoordinate direction).smulRight
      (actionGeneratedMatterLocalJetCoordinate state space direction)

def actionGeneratedMatterLocalCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv (state.matter space) +
    actionGeneratedMatterLocalIncrement state space point

/-- Actual primitive matter germ generated before equation acceptance. -/
def actionGeneratedMatterLocalField
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (actionGeneratedMatterLocalCoordinate state space point)

@[simp] theorem actionGeneratedMatterLocalField_origin
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterLocalField state space 0 =
      state.matter space := by
  simp [actionGeneratedMatterLocalField,
    actionGeneratedMatterLocalCoordinate,
    actionGeneratedMatterLocalIncrement]

/-- The generated local matter germ depends on a Cauchy state only through
the matter slice and the gravity, gauge, and scalar values at the selected
contact.  This congruence is intentionally proved once at the owning module:
downstream provenance comparisons should not repeatedly unfold the complete
finite-coordinate action germ. -/
theorem actionGeneratedMatterLocalField_eq_of_contact_data
    (first second : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (matterEq : first.matter = second.matter)
    (gravityConnectionEq :
      first.gravityConnection space = second.gravityConnection space)
    (gaugeConnectionEq :
      first.gaugeConnection space = second.gaugeConnection space)
    (scalarEq : first.scalar space = second.scalar space) :
    actionGeneratedMatterLocalField first space =
      actionGeneratedMatterLocalField second space := by
  funext point
  apply matterCoordinateEquiv.injective
  unfold actionGeneratedMatterLocalField
    actionGeneratedMatterLocalCoordinate
    actionGeneratedMatterLocalIncrement
    actionGeneratedMatterLocalJetCoordinate
    actionGeneratedMatterRawTimeVelocity
    actionGeneratedMatterTimeCovariantDerivative
    actionGeneratedMatterKnownVector
    cauchyMatterSpatialCovariantDerivative
    cauchyMatterSpatialDerivativeCoordinate
    cauchyMatterConnectionAction
  rw [matterEq, gravityConnectionEq, gaugeConnectionEq, scalarEq]

theorem actionGeneratedMatterLocalField_smooth
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (actionGeneratedMatterLocalField state space point) := by
  simpa [actionGeneratedMatterLocalField,
    actionGeneratedMatterLocalCoordinate] using
    (contDiff_const.add
      (actionGeneratedMatterLocalIncrement state space).contDiff)

theorem actionGeneratedMatterLocalCoordinate_derivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (actionGeneratedMatterLocalCoordinate state space)
        0 direction =
      actionGeneratedMatterLocalJetCoordinate state space direction := by
  unfold fieldDirectionalDerivative
    actionGeneratedMatterLocalCoordinate
  rw [fderiv_const_add]
  rw [(actionGeneratedMatterLocalIncrement state space).hasFDerivAt.fderiv]
  fin_cases direction <;>
    simp [actionGeneratedMatterLocalIncrement,
      localBaseCoordinate, coordinateDirection, Fin.sum_univ_four]

/-- Synchronized gravity--P286--matter local actual output. -/
def sourceActionGeneratedMatterLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  { sourceActionGeneratedGravityGaugeLocalActualLift source state space with
    matter := actionGeneratedMatterLocalField state space }

theorem sourceActionGeneratedMatterLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedMatterLocalActualLift source state space).Smooth := by
  have baseSmooth :=
    sourceActionGeneratedGravityGaugeLocalActualLift_smooth source state space
  rcases baseSmooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth,
      actionGeneratedMatterLocalField_smooth state space,
      conjugateMatterSmooth⟩

theorem sourceActionGeneratedMatterLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedMatterLocalActualLift source state
      space).Nondegenerate := by
  exact sourceActionGeneratedGravityGaugeLocalActualLift_nondegenerate
    source state space nondegenerate

@[simp] theorem sourceActionGeneratedMatterLocalActualLift_matter_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedMatterLocalActualLift source state space).matter 0 =
      state.matter space := by
  exact actionGeneratedMatterLocalField_origin state space

theorem sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((sourceActionGeneratedMatterLocalActualLift source state
              space).matter point))
        0 direction =
      actionGeneratedMatterLocalJetCoordinate state space direction := by
  unfold sourceActionGeneratedMatterLocalActualLift
  simp only [actionGeneratedMatterLocalField,
    matterCoordinateEquiv.apply_symm_apply]
  change
    fieldDirectionalDerivative
        (actionGeneratedMatterLocalCoordinate state space)
        0 direction =
      _
  exact actionGeneratedMatterLocalCoordinate_derivative
    state space direction

theorem sourceActionGeneratedMatterLocalActualLift_timeCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedMatterLocalActualLift source state space)
        0 canonicalLorentzianTimeDirection =
      actionGeneratedMatterTimeCovariantDerivative state space := by
  unfold holonomicMatterCovariantDerivative
  rw [
    sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin]
  simp only [actionGeneratedMatterLocalJetCoordinate,
    canonicalLorentzianTimeDirection, Matrix.cons_val_zero,
    matterCoordinateEquiv.symm_apply_apply]
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  rw [show
    (sourceActionGeneratedMatterLocalActualLift source state
      space).gravityConnection 0 =
        state.gravityConnection space by
      exact
        sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
          source state space]
  rw [show
    (sourceActionGeneratedMatterLocalActualLift source state
      space).gaugeConnection 0 =
        state.gaugeConnection space by
      funext direction
      exact sourceGeneratedP286ActionLocalConnection_origin
        source state space direction]
  unfold actionGeneratedMatterRawTimeVelocity
    cauchyMatterConnectionAction
  simp [canonicalLorentzianTimeDirection]
  abel

theorem sourceActionGeneratedMatterLocalActualLift_spatialCovariantDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedMatterLocalActualLift source state space)
        0 direction.succ =
      cauchyMatterSpatialCovariantDerivative state space direction := by
  unfold holonomicMatterCovariantDerivative
  rw [
    sourceActionGeneratedMatterLocalActualLift_rawDerivative_origin]
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  fin_cases direction <;>
    simp [actionGeneratedMatterLocalJetCoordinate,
      cauchyMatterSpatialCovariantDerivative,
      cauchyMatterConnectionAction,
      sourceActionGeneratedMatterLocalActualLift,
      sourceActionGeneratedGravityGaugeLocalActualLift,
      sourceGeneratedP286ActionLocalActualLift,
      sourceGeneratedP286ActionLocalConnection_origin] <;>
    abel

/-! ## Actual Dirac--Yukawa acceptance -/

/-- The generated primitive matter germ satisfies the actual Dirac--Yukawa
equation at the common origin on the identity-coframe noncharacteristic
domain. -/
theorem sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    generatedContinuumMatterVector source 0 0
      (toContinuumPointField
        (sourceActionGeneratedMatterLocalActualLift source state space) 0) =
      0 := by
  unfold generatedContinuumMatterVector
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  rw [show
    (sourceActionGeneratedMatterLocalActualLift source state space).coframe 0 =
      (1 : LorentzianCoframe) by exact identityCoframe]
  rw [show ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp only [Fin.sum_univ_four, diracGamma]
  rw [show
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedMatterLocalActualLift source state space)
        0 (0 : LorentzianIndex) =
      actionGeneratedMatterTimeCovariantDerivative state space by
    simpa [canonicalLorentzianTimeDirection] using
      sourceActionGeneratedMatterLocalActualLift_timeCovariantDerivative_origin
        source state space]
  rw [sourceActionGeneratedMatterLocalActualLift_matter_origin]
  rw [show
    (sourceActionGeneratedMatterLocalActualLift source state space).scalar 0 =
      state.scalar space by
    exact sourceGeneratedP286ActionLocalActualLift_scalar_origin
      source state space]
  rw [
    show
      holonomicMatterCovariantDerivative
          (sourceActionGeneratedMatterLocalActualLift source state space)
          0 (1 : LorentzianIndex) =
        cauchyMatterSpatialCovariantDerivative state space 0 by
      simpa using
        sourceActionGeneratedMatterLocalActualLift_spatialCovariantDerivative_origin
          source state space 0,
    show
      holonomicMatterCovariantDerivative
          (sourceActionGeneratedMatterLocalActualLift source state space)
          0 (2 : LorentzianIndex) =
        cauchyMatterSpatialCovariantDerivative state space 1 by
      simpa using
        sourceActionGeneratedMatterLocalActualLift_spatialCovariantDerivative_origin
          source state space 1,
    show
      holonomicMatterCovariantDerivative
          (sourceActionGeneratedMatterLocalActualLift source state space)
          0 (3 : LorentzianIndex) =
        cauchyMatterSpatialCovariantDerivative state space 2 by
      simpa using
        sourceActionGeneratedMatterLocalActualLift_spatialCovariantDerivative_origin
          source state space 2]
  have actionLaw :=
    actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw
      state space
  simp [IdentityCoframeMatterTimeActionLaw,
    identityCoframeMatterTimePrincipal,
    actionGeneratedMatterKnownVector, Fin.sum_univ_three,
    diracGamma] at actionLaw
  change
    Complex.I •
          ((diracMatrixMatterAction diracGammaZero)
              (actionGeneratedMatterTimeCovariantDerivative state space) +
            (diracMatrixMatterAction diracGammaOne)
              (cauchyMatterSpatialCovariantDerivative state space 0) +
            (diracMatrixMatterAction diracGammaTwo)
              (cauchyMatterSpatialCovariantDerivative state space 1) +
            (diracMatrixMatterAction diracGammaThree)
              (cauchyMatterSpatialCovariantDerivative state space 2)) +
        chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (state.scalar space))
          (state.matter space) =
      0
  simpa only [smul_add, add_assoc] using actionLaw

/-- One frontier theorem exposes gravity simplicity, gravity auxiliary,
P286 auxiliary, and matter Dirac--Yukawa laws on the same generated actual
output. -/
theorem sourceActionGeneratedGravityGaugeMatterLocalActualLift_origin_system
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (identityCoframe : state.coframe space = 1) :
    let actual :=
      sourceActionGeneratedMatterLocalActualLift source state space
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
        0 := by
  refine
    ⟨?_, ?_, ?_,
      sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin
        source state space identityCoframe⟩
  · exact
      sourceActionGeneratedGravityGaugeLocalActualLift_simplicity_origin
        source state space
  · exact
      sourceActionGeneratedGravityGaugeLocalActualLift_gravityAuxiliaryEquation_origin
        source state space
  · exact
      sourceActionGeneratedGravityGaugeLocalActualLift_p286AuxiliaryEquation_origin
        source state space

/-! ## Positive and negative controls -/

/-- The identity-coframe action domain is inhabited by the existing positive
phase probe; its generated actual matter germ satisfies the Dirac--Yukawa
equation without a supplied velocity. -/
theorem positiveProbe_sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
      (toContinuumPointField
        (sourceActionGeneratedMatterLocalActualLift
          positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0) 0) =
      0 := by
  exact
    sourceActionGeneratedMatterLocalActualLift_diracYukawa_origin
      positiveSmoothUnifiedSource positivePhaseProbeCauchyState 0 rfl

theorem actionGeneratedMatterTimeCovariantDerivative_ne_zero_of_knownVector
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (knownNonzero :
      actionGeneratedMatterKnownVector state space ≠ 0) :
    actionGeneratedMatterTimeCovariantDerivative state space ≠
      0 := by
  intro velocityZero
  have principalKnownZero :
      identityCoframeMatterTimePrincipal
        (actionGeneratedMatterKnownVector state space) = 0 := by
    simpa [actionGeneratedMatterTimeCovariantDerivative] using
      velocityZero
  apply knownNonzero
  calc
    actionGeneratedMatterKnownVector state space =
        identityCoframeMatterTimePrincipal
          (identityCoframeMatterTimePrincipal
            (actionGeneratedMatterKnownVector state space)) :=
      (identityCoframeMatterTimePrincipal_involutive _).symm
    _ = identityCoframeMatterTimePrincipal 0 := by
      rw [principalKnownZero]
    _ = 0 := by simp [identityCoframeMatterTimePrincipal]

@[simp] theorem actionGeneratedMatterTimeCovariantDerivative_eq_zero_of_knownVector
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (knownZero :
      actionGeneratedMatterKnownVector state space = 0) :
    actionGeneratedMatterTimeCovariantDerivative state space =
      0 := by
  simp [actionGeneratedMatterTimeCovariantDerivative, knownZero,
    identityCoframeMatterTimePrincipal]

end

end SaturationMonoid.PhysicsCore.StageNineMatterActionTimeVelocity
