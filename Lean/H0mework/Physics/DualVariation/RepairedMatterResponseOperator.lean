import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponseActualLift
import H0mework.Physics.DualVariation.ConjugateMatterVariation
import H0mework.Physics.CoframeResponse.MatterActionResponse
import H0mework.Physics.Coframe.IdentityCoframeConjugateMatterTimeResponseActualLift

/-!
# Repaired-root primal/adjoint matter response operator

The authoritative form-native root uses the right-chiral Dirac-dual Yukawa
operator.  The historical current-state matter producers still solve the
earlier chiral Yukawa action.  This module upgrades the producer itself:

```text
current actual
  -> repaired Dirac-dual spatial/algebraic action terms
  -> existing canonical temporal-principal inverse
  -> unique primal time response
  -> unique adjoint time response
  -> one common holonomic actual.
```

The construction accepts no residual, residual coordinate, sign, support
branch, target derivative, candidate response, zero-fiber witness, or
stationarity receipt.  The repaired-versus-historical seam is consumed only
downstream as a regression; it is not an input to any definition here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedMatterResponseOperator

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineConjugateMatterActionTimeVelocity
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineP286ActionCauchySplit
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Repaired primal action law -/

/-- All non-temporal terms of the repaired Dirac-dual matter equation,
evaluated on the live coframe, connection, scalar, and matter jet. -/
def holonomicDiracDualCurrentCoframeMatterKnownVector
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : Fin 3,
        diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            direction.succ)
          (holonomicMatterCovariantDerivative configuration point
            direction.succ) +
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))
      (configuration.matter point)

/-- Repaired current-coframe temporal matter action law. -/
def HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeCovariantDerivative : DiracExteriorMatterCarrier) : Prop :=
  CurrentCoframeMatterTemporalActionLaw
    (configuration.coframe point)
    (holonomicDiracDualCurrentCoframeMatterKnownVector configuration point)
    timeCovariantDerivative

/-- Branch-free repaired temporal covariant response.  The inverse is the
existing action-owned temporal-principal equivalence. -/
def actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    DiracExteriorMatterCarrier :=
  actionGeneratedCurrentCoframeMatterTemporalDerivative
    (configuration.coframe point)
    (holonomicDiracDualCurrentCoframeMatterKnownVector configuration point)

/-- Primitive repaired matter velocity after removing the live temporal
connection action. -/
def actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    DiracExteriorMatterCarrier :=
  actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
      configuration point -
    holonomicMatterConnectionAction configuration point
      canonicalLorentzianTimeDirection

theorem
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe point) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw configuration point
      (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        configuration point) := by
  exact
    actionGeneratedCurrentCoframeMatterTemporalDerivative_satisfies_actionLaw
      (configuration.coframe point) noncharacteristic
      (holonomicDiracDualCurrentCoframeMatterKnownVector configuration point)

theorem holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe point) ≠ 0)
    (first second : DiracExteriorMatterCarrier)
    (firstLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        configuration point first)
    (secondLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        configuration point second) :
    first = second := by
  exact
    currentCoframeMatterTemporalActionLaw_unique
      (configuration.coframe point) noncharacteristic
      (holonomicDiracDualCurrentCoframeMatterKnownVector configuration point)
      first second firstLaw secondLaw

/-! ## Repaired primal actualization -/

/-- Raw first-jet change generated from the repaired action equation. -/
def diracDualCurrentCoframeMatterTimeResponseWrite
    (configuration : StageNineHolonomicConfiguration) :
    DiracExteriorMatterCarrier :=
  actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
      configuration 0 -
    holonomicMatterCovariantDerivative configuration 0
      canonicalLorentzianTimeDirection

/-- Install the repaired action-owned primal response on the same actual. -/
def actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installMatterLinearTimeResponse configuration
    (diracDualCurrentCoframeMatterTimeResponseWrite configuration)

@[simp] theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      configuration).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      configuration).matter 0 =
      configuration.matter 0 :=
  installMatterLinearTimeResponse_matter_origin _ _

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_spatialCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 direction.succ =
      holonomicMatterCovariantDerivative configuration 0 direction.succ := by
  unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin
      configuration smooth
      (diracDualCurrentCoframeMatterTimeResponseWrite configuration)]
  simp [canonicalLorentzianTimeDirection]

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_timeCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        configuration 0 := by
  unfold actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin
      configuration smooth
      (diracDualCurrentCoframeMatterTimeResponseWrite configuration)]
  simp only [if_pos]
  unfold diracDualCurrentCoframeMatterTimeResponseWrite
  abel

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_knownVector
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector configuration 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]
  simp_rw [
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_spatialCovariantDerivative
      configuration smooth]

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
        configuration)
      0
      (holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have generatedLaw :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      configuration 0 noncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generatedLaw ⊢
  rw [
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_knownVector
      configuration smooth,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_timeCovariantDerivative
      configuration smooth]
  exact generatedLaw

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      configuration).Smooth :=
  installMatterLinearTimeResponse_smooth _ smooth _

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      configuration).Nondegenerate :=
  installMatterLinearTimeResponse_nondegenerate _ nondegenerate _

/-- Faithful zero fiber of the repaired primal write. -/
theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_eq_iff
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration =
        configuration ↔
      holonomicMatterCovariantDerivative configuration 0
          canonicalLorentzianTimeDirection =
        actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          configuration 0 := by
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_eq_iff]
  unfold diracDualCurrentCoframeMatterTimeResponseWrite
  constructor
  · intro responseZero
    exact (sub_eq_zero.mp responseZero).symm
  · intro alreadyGenerated
    exact sub_eq_zero.mpr alreadyGenerated.symm

theorem
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_unique
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0)
    (candidate : DiracExteriorMatterCarrier)
    (candidateLaw :
      HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 candidate) :
    candidate =
      holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection := by
  exact
    holonomicDiracDualCurrentCoframeMatterTimeActionLaw_unique _ _
      (by simpa using noncharacteristic)
      _ _ candidateLaw
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw
        configuration smooth noncharacteristic)

/-! ## Repaired adjoint action law -/

/-- The identity-coframe algebraic Dirac operator of the authoritative
Dirac-dual root.  Only the Yukawa summand differs from the historical
operator; the connection action is unchanged. -/
def holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        (diracMatrixMatterAction (diracGamma direction)).comp
          (holonomicIdentityCoframeMatterConnectionOperator configuration
            point direction) +
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point))

/-- All already-present terms in the repaired adjoint equation. -/
def holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (configuration.conjugateMatter point).comp
      (holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        configuration point) -
    holonomicIdentityCoframeConjugateMatterSpatialTransport configuration point

/-- Branch-free repaired adjoint velocity selected by the involutive temporal
principal symbol. -/
def holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  (holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
      configuration point).comp
    (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)

def HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (timeDerivative : Module.Dual ℂ DiracExteriorMatterCarrier) : Prop :=
  timeDerivative.comp
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection) +
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
        point =
    (configuration.conjugateMatter point).comp
      (holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        configuration point)

theorem
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_satisfies
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      configuration point
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        configuration point) := by
  apply LinearMap.ext
  intro matter
  simp only [
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity,
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [identityCoframeMatterPrincipal_time_involutive]
  abel

theorem holonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw_unique
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (first second : Module.Dual ℂ DiracExteriorMatterCarrier)
    (firstLaw :
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        configuration point first)
    (secondLaw :
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        configuration point second) :
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
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      rw [identityCoframeMatterPrincipal_time_involutive]
    _ =
        second
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection matter)) := by
      exact LinearMap.congr_fun composedEqual
        (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection matter)
    _ = second matter := by
      rw [identityCoframeMatterPrincipal_time_involutive]

/-! ## Repaired adjoint actualization -/

def diracDualIdentityCoframeConjugateMatterTimeResponseWrite
    (configuration : StageNineHolonomicConfiguration) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
      configuration 0 -
    holonomicConjugateMatterDerivativeDual configuration 0
      canonicalLorentzianTimeDirection

def actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installConjugateMatterLinearTimeResponse configuration
    (diracDualIdentityCoframeConjugateMatterTimeResponseWrite configuration)

@[simp] theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_matter
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).matter =
      configuration.matter :=
  rfl

@[simp] theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).conjugateMatter 0 =
      configuration.conjugateMatter 0 :=
  installConjugateMatterLinearTimeResponse_conjugateMatter_origin _ _

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_spatialTransport
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicIdentityCoframeConjugateMatterSpatialTransport
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
        0 := by
  unfold
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
  apply Finset.sum_congr rfl
  intro direction _
  rw [
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
      configuration smooth
      (diracDualIdentityCoframeConjugateMatterTimeResponseWrite configuration)
      direction.succ]
  have spatialNe :
      direction.succ ≠ canonicalLorentzianTimeDirection := by
    fin_cases direction <;>
      decide
  simp [spatialNe]

theorem
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator_actionGeneratedAdjointActual_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualIdentityCoframeMatterAlgebraicOperator
        configuration 0 := by
  simp [holonomicDiracDualIdentityCoframeMatterAlgebraicOperator,
    holonomicIdentityCoframeMatterConnectionOperator]

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_knownDual
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
        configuration 0 := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
  rw [
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin,
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator_actionGeneratedAdjointActual_origin,
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_spatialTransport
      configuration smooth]

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_actionVelocity
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        configuration 0 := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
  rw [
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_knownDual
      configuration smooth]

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_timeDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection =
      holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
        configuration 0 := by
  unfold
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
  rw [
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
      configuration smooth
      (diracDualIdentityCoframeConjugateMatterTimeResponseWrite configuration)
      canonicalLorentzianTimeDirection]
  simp [diracDualIdentityCoframeConjugateMatterTimeResponseWrite]

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        configuration)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have generatedLaw :=
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_satisfies
      (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        configuration)
      0
  rw [
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_timeDerivative
      configuration smooth,
    ← actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_actionVelocity
      configuration smooth]
  exact generatedLaw

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).Smooth :=
  installConjugateMatterLinearTimeResponse_smooth _ smooth _

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
      configuration).Nondegenerate :=
  installConjugateMatterLinearTimeResponse_nondegenerate _ nondegenerate _

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_eq_iff
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration =
        configuration ↔
      holonomicConjugateMatterDerivativeDual configuration 0
          canonicalLorentzianTimeDirection =
        holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          configuration 0 := by
  rw [
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual,
    installConjugateMatterLinearTimeResponse_eq_iff]
  unfold diracDualIdentityCoframeConjugateMatterTimeResponseWrite
  constructor
  · intro responseZero
    exact (sub_eq_zero.mp responseZero).symm
  · intro alreadyGenerated
    exact sub_eq_zero.mpr alreadyGenerated.symm

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_unique
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateLaw :
      HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 candidate) :
    candidate =
      holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection := by
  exact
    holonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw_unique
      _ _ _ _ candidateLaw
      (actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
        configuration smooth)

/-! ## Identity-contact compatibility

The legacy identity-coframe API remains available as a compatibility
readout.  The active joint producer below uses the live-coframe writer; these
equalities show that no fixed identity first-jet regression changes merely
because the producer has been generalized. -/

theorem
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator_eq_rightChiralIdentity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator configuration
        point =
      holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator
        configuration point := by
  apply LinearMap.ext
  intro matter
  simp [holonomicDiracDualIdentityCoframeMatterAlgebraicOperator,
    holonomicDiracDualRightChiralIdentityCoframeMatterAlgebraicOperator,
    identityCoframeMatterPrincipal, LinearMap.sum_apply]
  rw [Finset.smul_sum]

theorem
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual_eq_rightChiralIdentity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual configuration
        point =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
        configuration point := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterKnownDual
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterKnownDual
  rw [
    holonomicDiracDualIdentityCoframeMatterAlgebraicOperator_eq_rightChiralIdentity]

theorem
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity configuration
        point =
      holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
        configuration point := by
  unfold holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
    holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
  rw [
    holonomicDiracDualIdentityCoframeConjugateMatterKnownDual_eq_rightChiralIdentity]

theorem
    diracDualIdentityCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity
    (configuration : StageNineHolonomicConfiguration) :
    diracDualIdentityCoframeConjugateMatterTimeResponseWrite configuration =
      diracDualRightChiralIdentityCoframeConjugateMatterTimeResponseWrite
        configuration := by
  unfold diracDualIdentityCoframeConjugateMatterTimeResponseWrite
    diracDualRightChiralIdentityCoframeConjugateMatterTimeResponseWrite
  rw [
    holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity]

theorem
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_eq_rightChiralIdentity
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        configuration =
      actionGeneratedDiracDualRightChiralIdentityCoframeConjugateMatterTimeResponseActual
        configuration := by
  unfold actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
    actionGeneratedDiracDualRightChiralIdentityCoframeConjugateMatterTimeResponseActual
  rw [
    diracDualIdentityCoframeConjugateMatterTimeResponseWrite_eq_rightChiralIdentity]

theorem
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_identity_of_firstJet
    (configuration : StageNineHolonomicConfiguration)
    (firstJet :
      holonomicCoframeFirstJetAt configuration.coframe 0 =
        identityCoframeMatterGeometry) :
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
        configuration =
      actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual
        configuration := by
  rw [
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_rightChiralIdentity_of_firstJet
      configuration firstJet,
    ← actionGeneratedDiracDualIdentityCoframeConjugateMatterTimeResponseActual_eq_rightChiralIdentity]

/-! ## One common repaired matter actual -/

/-- Apply both repaired-root action writes to one common actual.  This
constructor depends only on the current configuration and the authoritative
action operators. -/
def actionGeneratedDiracDualRepairedMatterJointResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
      configuration)

theorem actionGeneratedDiracDualRepairedMatterJointResponseActual_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedDiracDualRepairedMatterJointResponseActual
      configuration).Smooth :=
  actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_smooth
    _
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_smooth
      configuration smooth)

theorem actionGeneratedDiracDualRepairedMatterJointResponseActual_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedDiracDualRepairedMatterJointResponseActual
      configuration).Nondegenerate :=
  actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_nondegenerate
    _
    (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_nondegenerate
      configuration nondegenerate)

theorem
    actionGeneratedDiracDualRepairedMatterJointResponseActual_primalActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (actionGeneratedDiracDualRepairedMatterJointResponseActual
        configuration)
      0
      (holonomicMatterCovariantDerivative
        (actionGeneratedDiracDualRepairedMatterJointResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  have primalLaw :=
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw
      configuration smooth noncharacteristic
  simpa [
    actionGeneratedDiracDualRepairedMatterJointResponseActual,
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual,
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw,
    holonomicDiracDualCurrentCoframeMatterKnownVector,
    holonomicMatterCovariantDerivative] using primalLaw

theorem
    actionGeneratedDiracDualRepairedMatterJointResponseActual_liveAdjointActionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : Matrix.det (configuration.coframe 0) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw
      (actionGeneratedDiracDualRepairedMatterJointResponseActual
        configuration)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedDiracDualRepairedMatterJointResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  exact
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
      _
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_smooth
        configuration smooth)
      (by simpa using nondegenerate)
      (by simpa using noncharacteristic)

/-- Faithful zero fiber of the two-channel repaired matter operator.  Both
conditions are read on the supplied current; neither is accepted as a
constructor premise. -/
theorem actionGeneratedDiracDualRepairedMatterJointResponseActual_eq_iff
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedDiracDualRepairedMatterJointResponseActual configuration =
          configuration ↔
      (holonomicMatterCovariantDerivative configuration 0
            canonicalLorentzianTimeDirection =
          actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
            configuration 0) ∧
        (holonomicConjugateMatterDerivativeDual configuration 0
              canonicalLorentzianTimeDirection =
            holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
              configuration 0) := by
  constructor
  · intro jointFixed
    have matterFixed :
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          configuration).matter =
          configuration.matter := by
      have fieldsEqual :=
        congrArg StageNineHolonomicConfiguration.matter jointFixed
      simpa [actionGeneratedDiracDualRepairedMatterJointResponseActual] using
        fieldsEqual
    have primalFixed :
        actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration =
          configuration := by
      apply StageNineHolonomicConfiguration.ext
      all_goals try rfl
      exact matterFixed
    have adjointFixed :
        actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
            configuration =
          configuration := by
      simpa [
        actionGeneratedDiracDualRepairedMatterJointResponseActual,
        primalFixed] using jointFixed
    exact
      ⟨(actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_eq_iff
          configuration).1 primalFixed,
        (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_iff
          configuration).1 adjointFixed⟩
  · rintro ⟨primalZero, adjointZero⟩
    have primalFixed :
        actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            configuration =
          configuration :=
      (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_eq_iff
        configuration).2 primalZero
    have adjointFixed :
        actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
            configuration =
          configuration :=
      (actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_eq_iff
        configuration).2 adjointZero
    simp [
      actionGeneratedDiracDualRepairedMatterJointResponseActual,
      primalFixed, adjointFixed]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedMatterResponseOperator
