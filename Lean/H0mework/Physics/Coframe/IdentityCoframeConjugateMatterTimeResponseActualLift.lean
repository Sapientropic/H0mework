import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Holonomic.HolonomicIdentityCoframeConjugateMatterActionResponse

/-!
# Identity-coframe conjugate-matter time-response actual lift

The holonomic adjoint action selects a unique temporal dual response.  This
module installs that response faithfully in the current actual:

```text
actual U
→ action-generated temporal dual response T†(U)
→ generated difference T†(U) - D₀U†
→ canonical linear physical-time conjugate-matter write
→ actual U†.
```

The constructor consumes only `U` and action-owned operators.  It does not
consume an Euler--Lagrange residual, target jet, branch witness, response
certificate, or adjustable coefficient.  Re-substitution into the same
action law is producer soundness.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineIdentityCoframeConjugateMatterTimeResponseActualLift

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

@[simp] theorem matterDualCoordinates_zero :
    matterDualCoordinates
        (0 : Module.Dual ℂ DiracExteriorMatterCarrier) =
      0 := by
  apply PiLp.ext
  intro index
  rfl

/-! ## Canonical faithful linear-time installer -/

/-- Linear physical-time coordinate write for an already action-generated
dual response.  The coefficient is fixed by the canonical time coordinate. -/
def conjugateMatterLinearTimeCoordinateWrite
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  localBaseCoordinate canonicalLorentzianTimeDirection point •
    matterDualCoordinates response

@[simp] theorem conjugateMatterLinearTimeCoordinateWrite_origin
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    conjugateMatterLinearTimeCoordinateWrite response 0 = 0 := by
  simp [conjugateMatterLinearTimeCoordinateWrite, localBaseCoordinate]

theorem conjugateMatterLinearTimeCoordinateWrite_directionalDerivative
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (conjugateMatterLinearTimeCoordinateWrite response) point direction =
      if direction = canonicalLorentzianTimeDirection then
        matterDualCoordinates response
      else
        0 := by
  have derivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := point)
      |>.smul_const (matterDualCoordinates response)
  unfold fieldDirectionalDerivative conjugateMatterLinearTimeCoordinateWrite
  change
    fderiv ℝ
        (fun candidate =>
          localBaseCoordinate canonicalLorentzianTimeDirection candidate •
            matterDualCoordinates response)
        point (coordinateDirection direction) =
      _
  rw [derivative.fderiv]
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]

theorem conjugateMatterLinearTimeCoordinateWrite_contDiff
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (conjugateMatterLinearTimeCoordinateWrite response) := by
  exact
    (localBaseCoordinate canonicalLorentzianTimeDirection).contDiff.smul
      contDiff_const

/-- Install one already-generated temporal dual response.  This is a
transporter; the no-premise producer below supplies its response. -/
def installConjugateMatterLinearTimeResponse
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  varyConjugateMatterCoordinates configuration
    (conjugateMatterLinearTimeCoordinateWrite response) 1

@[simp] theorem installConjugateMatterLinearTimeResponse_coframe
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installConjugateMatterLinearTimeResponse_gravityConnection
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem installConjugateMatterLinearTimeResponse_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

@[simp] theorem
    installConjugateMatterLinearTimeResponse_gravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).gravitySimplicityMultiplier =
      configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem installConjugateMatterLinearTimeResponse_gaugeConnection
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem installConjugateMatterLinearTimeResponse_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem installConjugateMatterLinearTimeResponse_scalar
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem installConjugateMatterLinearTimeResponse_matter
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response).matter =
      configuration.matter :=
  rfl

theorem installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterDualCoordinates
        ((installConjugateMatterLinearTimeResponse configuration response
          ).conjugateMatter point) =
      matterDualCoordinates (configuration.conjugateMatter point) +
        conjugateMatterLinearTimeCoordinateWrite response point := by
  apply PiLp.ext
  intro index
  simp [installConjugateMatterLinearTimeResponse,
    varyConjugateMatterCoordinates, matterDualCoordinates,
    matterDualOfCoordinates_basis_apply]

@[simp] theorem installConjugateMatterLinearTimeResponse_conjugateMatter_origin
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).conjugateMatter 0 =
      configuration.conjugateMatter 0 := by
  apply LinearMap.ext
  intro matter
  simp [installConjugateMatterLinearTimeResponse,
    varyConjugateMatterCoordinates,
    conjugateMatterLinearTimeCoordinateWrite]

theorem
    holonomicConjugateMatterDerivativeCoordinates_installConjugateMatterLinearTimeResponse_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeCoordinates
        (installConjugateMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicConjugateMatterDerivativeCoordinates configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterDualCoordinates response
        else
          0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) 0 :=
    (holonomicConjugateMatterCoordinates_contDiff configuration smooth
      ).differentiable (by simp) |>.differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (conjugateMatterLinearTimeCoordinateWrite response) 0 :=
    (conjugateMatterLinearTimeCoordinateWrite_contDiff response
      ).differentiable (by simp) |>.differentiableAt
  unfold holonomicConjugateMatterDerivativeCoordinates
    fieldDirectionalDerivative
  rw [show
    holonomicConjugateMatterCoordinates
        (installConjugateMatterLinearTimeResponse configuration response) =
      holonomicConjugateMatterCoordinates configuration +
        conjugateMatterLinearTimeCoordinateWrite response by
    funext point
    exact
      installConjugateMatterLinearTimeResponse_conjugateMatterCoordinates
        configuration response point]
  rw [fderiv_add backgroundDifferentiable responseDifferentiable, add_apply]
  change
    _ +
        fieldDirectionalDerivative
          (conjugateMatterLinearTimeCoordinateWrite response) 0 direction =
      _
  rw [conjugateMatterLinearTimeCoordinateWrite_directionalDerivative]

theorem matterDualOfCoordinates_add
    (first second : MatterCoordinateCarrier) :
    matterDualOfCoordinates (first + second) =
      matterDualOfCoordinates first + matterDualOfCoordinates second := by
  apply LinearMap.ext
  intro matter
  simp [matterDualOfCoordinates_apply, mul_add,
    Finset.sum_add_distrib]

theorem
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (installConjugateMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicConjugateMatterDerivativeDual configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then response else 0 := by
  unfold holonomicConjugateMatterDerivativeDual
  rw [
    holonomicConjugateMatterDerivativeCoordinates_installConjugateMatterLinearTimeResponse_origin
      configuration smooth response direction]
  split_ifs <;>
    simp [matterDualOfCoordinates_add,
      matterDualOfCoordinates_surjective]

theorem installConjugateMatterLinearTimeResponse_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, ?_⟩
  intro index
  have responseCoordinateSmooth : ContDiff ℝ ∞ (fun point =>
      conjugateMatterLinearTimeCoordinateWrite response point index) := by
    simpa [conjugateMatterLinearTimeCoordinateWrite] using
      (Complex.ofRealCLM.contDiff.comp
        (localBaseCoordinate canonicalLorentzianTimeDirection).contDiff).mul
          (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
            matterDualCoordinates response index))
  simpa [installConjugateMatterLinearTimeResponse,
    varyConjugateMatterCoordinates, matterDualOfCoordinates_basis_apply] using
    (conjugateMatterSmooth index).add responseCoordinateSmooth

theorem installConjugateMatterLinearTimeResponse_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    (installConjugateMatterLinearTimeResponse configuration response
      ).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

@[simp] theorem installConjugateMatterLinearTimeResponse_zero
    (configuration : StageNineHolonomicConfiguration) :
    installConjugateMatterLinearTimeResponse configuration 0 =
      configuration := by
  cases configuration
  simp [installConjugateMatterLinearTimeResponse,
    varyConjugateMatterCoordinates,
    conjugateMatterLinearTimeCoordinateWrite]

/-- Faithful zero fiber: a nonzero generated dual first-jet response cannot
disappear into an unchanged third actual. -/
theorem installConjugateMatterLinearTimeResponse_eq_iff
    (configuration : StageNineHolonomicConfiguration)
    (response : Module.Dual ℂ DiracExteriorMatterCarrier) :
    installConjugateMatterLinearTimeResponse configuration response =
        configuration ↔
      response = 0 := by
  constructor
  · intro actualEq
    have conjugateEq := congrArg
      (fun candidate : StageNineHolonomicConfiguration =>
        candidate.conjugateMatter
          (coordinateDirection canonicalLorentzianTimeDirection))
      actualEq
    have responseZero :
        configuration.conjugateMatter
              (coordinateDirection canonicalLorentzianTimeDirection) +
            response =
          configuration.conjugateMatter
            (coordinateDirection canonicalLorentzianTimeDirection) := by
      simpa [installConjugateMatterLinearTimeResponse,
        varyConjugateMatterCoordinates,
        conjugateMatterLinearTimeCoordinateWrite, localBaseCoordinate,
        coordinateDirection, canonicalLorentzianTimeDirection,
        matterDualOfCoordinates_surjective] using conjugateEq
    exact (add_eq_left.mp responseZero)
  · rintro rfl
    exact installConjugateMatterLinearTimeResponse_zero configuration

/-! ## State-dependent action response -/

/-- Raw dual first-jet change determined by the action response and the
actual's current temporal dual derivative. -/
def identityCoframeConjugateMatterTimeResponseWrite
    (configuration : StageNineHolonomicConfiguration) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicIdentityCoframeConjugateMatterActionVelocity configuration 0 -
    holonomicConjugateMatterDerivativeDual configuration 0
      canonicalLorentzianTimeDirection

/-- Apply the unique current-state adjoint write to the same actual. -/
def actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installConjugateMatterLinearTimeResponse configuration
    (identityCoframeConjugateMatterTimeResponseWrite configuration)

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gravitySimplicityMultiplier =
      configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_matter
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).matter =
      configuration.matter :=
  rfl

@[simp] theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).conjugateMatter 0 =
      configuration.conjugateMatter 0 :=
  installConjugateMatterLinearTimeResponse_conjugateMatter_origin _ _

theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_toContinuumPointField_origin
    (configuration : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      toContinuumPointField configuration 0 := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  exact
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin
      configuration

/-- A temporal adjoint-response write changes the physical time jet but not
the complete canonical zero slice.  The response remains recoverable by
recomputing the action vector field from that slice. -/
theorem
    canonicalCauchyRestriction_zero_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    canonicalCauchyRestriction 0
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration) =
      canonicalCauchyRestriction 0 configuration := by
  apply StageNineCauchyState.ext
  all_goals try rfl
  funext space
  apply LinearMap.ext
  intro matter
  change
    (installConjugateMatterLinearTimeResponse configuration
        (identityCoframeConjugateMatterTimeResponseWrite configuration)
      |>.conjugateMatter) (canonicalCauchySlicePoint 0 space) matter =
      configuration.conjugateMatter
        (canonicalCauchySlicePoint 0 space) matter
  simp [installConjugateMatterLinearTimeResponse,
    varyConjugateMatterCoordinates,
    conjugateMatterLinearTimeCoordinateWrite,
    canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
    Fin.sum_univ_three]

theorem
    holonomicIdentityCoframeMatterConnectionOperator_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicIdentityCoframeMatterConnectionOperator
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicIdentityCoframeMatterConnectionOperator configuration 0 := by
  funext direction
  simp [holonomicIdentityCoframeMatterConnectionOperator]

theorem
    holonomicIdentityCoframeMatterAlgebraicOperator_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin
    (configuration : StageNineHolonomicConfiguration) :
    holonomicIdentityCoframeMatterAlgebraicOperator
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicIdentityCoframeMatterAlgebraicOperator configuration 0 := by
  simp [holonomicIdentityCoframeMatterAlgebraicOperator,
    holonomicIdentityCoframeMatterConnectionOperator]

theorem
    holonomicIdentityCoframeConjugateMatterSpatialTransport_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicIdentityCoframeConjugateMatterSpatialTransport
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicIdentityCoframeConjugateMatterSpatialTransport configuration
        0 := by
  unfold actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
  unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
  apply Finset.sum_congr rfl
  intro direction _
  rw [
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
      configuration smooth
      (identityCoframeConjugateMatterTimeResponseWrite configuration)
      direction.succ]
  have spatialNe :
      direction.succ ≠ canonicalLorentzianTimeDirection := by
    fin_cases direction <;>
      decide
  simp [spatialNe]

theorem
    holonomicIdentityCoframeConjugateMatterActionVelocity_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicIdentityCoframeConjugateMatterActionVelocity
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 =
      holonomicIdentityCoframeConjugateMatterActionVelocity configuration 0 := by
  unfold holonomicIdentityCoframeConjugateMatterActionVelocity
    holonomicIdentityCoframeConjugateMatterKnownDual
  rw [
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin,
    holonomicIdentityCoframeMatterAlgebraicOperator_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin,
    holonomicIdentityCoframeConjugateMatterSpatialTransport_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin
      configuration smooth]

theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_timeDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection =
      holonomicIdentityCoframeConjugateMatterActionVelocity configuration 0 := by
  unfold actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
  rw [
    holonomicConjugateMatterDerivativeDual_installConjugateMatterLinearTimeResponse_origin
      configuration smooth
      (identityCoframeConjugateMatterTimeResponseWrite configuration)
      canonicalLorentzianTimeDirection]
  simp [identityCoframeConjugateMatterTimeResponseWrite]

theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_recomputes_timeDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicConjugateMatterDerivativeDual
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection =
      holonomicIdentityCoframeConjugateMatterActionVelocity
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 := by
  rw [
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_timeDerivative
      configuration smooth,
    holonomicIdentityCoframeConjugateMatterActionVelocity_actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_origin
      configuration smooth]

theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
        configuration)
      0
      (holonomicConjugateMatterDerivativeDual
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection) := by
  rw [
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_recomputes_timeDerivative
      configuration smooth]
  exact holonomicIdentityCoframeConjugateMatterActionVelocity_satisfies _ _

theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).Smooth :=
  installConjugateMatterLinearTimeResponse_smooth _ smooth _

theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
      configuration).Nondegenerate :=
  installConjugateMatterLinearTimeResponse_nondegenerate _ nondegenerate _

/-- The no-premise action write is the identity exactly when the current
actual already realizes the action-generated temporal dual response. -/
theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_eq_iff
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration =
        configuration ↔
      holonomicConjugateMatterDerivativeDual configuration 0
          canonicalLorentzianTimeDirection =
        holonomicIdentityCoframeConjugateMatterActionVelocity configuration
          0 := by
  rw [actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual,
    installConjugateMatterLinearTimeResponse_eq_iff]
  change
    holonomicIdentityCoframeConjugateMatterActionVelocity configuration 0 -
          holonomicConjugateMatterDerivativeDual configuration 0
            canonicalLorentzianTimeDirection =
        0 ↔
      holonomicConjugateMatterDerivativeDual configuration 0
          canonicalLorentzianTimeDirection =
        holonomicIdentityCoframeConjugateMatterActionVelocity configuration 0
  constructor
  · intro responseZero
    exact (sub_eq_zero.mp responseZero).symm
  · intro alreadyGenerated
    exact sub_eq_zero.mpr alreadyGenerated.symm

/-- Any candidate temporal dual derivative satisfying the same action law
equals the response carried by the generated output actual. -/
theorem
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_unique
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (candidateLaw :
      HolonomicIdentityCoframeConjugateMatterTimeActionLaw
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 candidate) :
    candidate =
      holonomicConjugateMatterDerivativeDual
        (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
          configuration)
        0 canonicalLorentzianTimeDirection := by
  exact
    holonomicIdentityCoframeConjugateMatterTimeActionLaw_unique _ _ _ _
      candidateLaw
      (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_satisfies_actionLaw
        configuration smooth)

end
end SaturationMonoid.PhysicsCore.StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
