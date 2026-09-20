import H0mework.Physics.Exterior.GravityAuxiliaryVariation
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm
import H0mework.Physics.MatterCurrent.CoframeStress

/-!
# S9-C3h152: source/action-generated P506 linear-Plebanski local actual

C3h149 first generates the complete P506/L0 Einstein--Cartan primitive
response `U₁`.  C3h151 then reads the nonzero matter coframe stress of that
already generated actual from the actual matter action.  This module lets the
linear Plebanski action generate the next local actual:

```text
exact P506/L0 source
→ path-first Einstein--Cartan actual U₁
→ actual matter-action stress T
→ canonical four-dimensional trace reversal
→ linear-Plebanski response and multiplier
→ normalized affine Lorentz connection
→ complete local actual U₂.
```

The curvature target is not supplied by source data.  It is the unique
action-owned auxiliary balance

`F(U₂, 0) = ⋆ᵢ B(U₂, 0) - λ(U₂, 0)`.

The same generated multiplier cancels the complete matter coframe stress in
every coframe direction and cancels the BF auxiliary principal in every
auxiliary direction.  Thus the response is interaction-sensitive in both
the coframe and curvature channels.

This remains a local linear-Plebanski action checkpoint.  It does not claim
stationarity of the historical squared-multiplier action, global
integrability, finite action, or the final simultaneous Stage-9 producer.
No residual, stress, curvature, endpoint, inverse principal, range witness,
coefficient, or branch receipt is accepted by a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCoframeSectorStress
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNinePlebanskiMultiplierVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentCoframeStress
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanPrimitiveCauchyUpdate
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## Canonical response generated from `U₁` -/

/-- The complete coframe response generated from the actual C3h151 matter
stress.  This is a deterministic action readout, not source data. -/
def positiveP506MatterCurrentLinearPlebanskiCoframeResponse :
    LorentzianCoframe :=
  linearPlebanskiCoframeResponseOfStress
    positiveP506MatterCurrentEinsteinCartanMatterStress

/-- The linear-Plebanski multiplier generated from the canonical response. -/
def positiveP506MatterCurrentLinearPlebanskiMultiplier :
    PhysicalBivector :=
  linearPlebanskiMultiplierOfCoframeResponse
    positiveP506MatterCurrentLinearPlebanskiCoframeResponse

/-- The auxiliary Euler balance fixes the curvature target without a source
parameter or branch choice. -/
def positiveP506MatterCurrentLinearPlebanskiCurvatureTarget :
    PhysicalBivector :=
  gravityInternalDualEquiv
      (physicalIIPlusBivector (1 : LorentzianCoframe)) -
    positiveP506MatterCurrentLinearPlebanskiMultiplier

/-- The already generated C3h149 actual at its initial contact. -/
def positiveP506MatterCurrentLinearPlebanskiBaseActual :
    StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift
    0 0

/-- Complete `U₂`: retain every primitive field of `U₁`, replace the
connection by the normalized affine germ generated from the action-owned
curvature target, and install the action-generated multiplier. -/
def positiveP506MatterCurrentLinearPlebanskiLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentLinearPlebanskiBaseActual with
    gravityConnection :=
      normalizedAffineLorentzConnectionField
        (positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityConnection
          0)
        positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
    gravitySimplicityMultiplier :=
      fun _ => positiveP506MatterCurrentLinearPlebanskiMultiplier }

theorem positiveP506MatterCurrentLinearPlebanskiCoframeResponse_selected :
    positiveP506MatterCurrentLinearPlebanskiCoframeResponse 0 3 =
      -(1 / 16 : ℝ) := by
  simp [positiveP506MatterCurrentLinearPlebanskiCoframeResponse,
    linearPlebanskiCoframeResponseOfStress,
    linearPlebanskiTraceReverse, coframeCovectorCoordinates,
    Matrix.trace,
    positiveP506MatterCurrentEinsteinCartanMatterStress_selected]
  norm_num

theorem positiveP506MatterCurrentLinearPlebanskiCoframeResponse_nonzero :
    positiveP506MatterCurrentLinearPlebanskiCoframeResponse ≠ 0 := by
  intro responseZero
  have selectedZero := congrFun (congrFun responseZero 0) 3
  rw [positiveP506MatterCurrentLinearPlebanskiCoframeResponse_selected]
    at selectedZero
  norm_num at selectedZero

theorem positiveP506MatterCurrentLinearPlebanskiMultiplier_nonzero :
    positiveP506MatterCurrentLinearPlebanskiMultiplier ≠ 0 := by
  intro multiplierZero
  have principalAtSelected :=
    linearPlebanskiCoframePrincipalValue_eq_principal
      positiveP506MatterCurrentLinearPlebanskiCoframeResponse
      (coframeCoordinateDirection 3 0)
  rw [linearPlebanskiCoframePrincipalValue,
    show
      linearPlebanskiMultiplierOfCoframeResponse
          positiveP506MatterCurrentLinearPlebanskiCoframeResponse =
        positiveP506MatterCurrentLinearPlebanskiMultiplier by
      rfl,
    multiplierZero] at principalAtSelected
  simp only [map_zero, zero_apply, neg_zero,
    gravityCoordinatePairing] at principalAtSelected
  have normalized :=
    DFunLike.congr_fun
      (linearPlebanskiCoframePrincipal_response_eq_neg
        positiveP506MatterCurrentEinsteinCartanMatterStress)
      (coframeCoordinateDirection 3 0)
  change
    linearPlebanskiCoframePrincipal
        positiveP506MatterCurrentLinearPlebanskiCoframeResponse
        (coframeCoordinateDirection 3 0) =
      -positiveP506MatterCurrentEinsteinCartanMatterStress
        (coframeCoordinateDirection 3 0)
    at normalized
  rw [
    positiveP506MatterCurrentEinsteinCartanMatterStress_selected]
    at normalized
  rw [← principalAtSelected] at normalized
  norm_num at normalized

/-! ## Complete primitive lift and interaction-sensitive geometry -/

@[simp] theorem positiveP506MatterCurrentLinearPlebanskiLocalActualLift_coframe
    (point : BasePoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.coframe point =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.coframe point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_gravityAuxiliary
    (point : BasePoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityAuxiliary
        point =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityAuxiliary
        point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_multiplier
    (point : BasePoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravitySimplicityMultiplier
        point =
      positiveP506MatterCurrentLinearPlebanskiMultiplier :=
  rfl

theorem positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual :
    positiveP506MatterCurrentLinearPlebanskiBaseActual =
      positiveP506MatterCurrentEinsteinCartanLocalActualLift := by
  exact
    positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift_zero

theorem positiveP506MatterCurrentLinearPlebanskiLocalActualLift_gaugeConnection_zero :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gaugeConnection =
      0 := by
  change positiveP506MatterCurrentLinearPlebanskiBaseActual.gaugeConnection = 0
  rw [positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]
  exact
    positiveP506MatterCurrentEinsteinCartanLocalActualLift_gaugeConnection_zero

theorem positiveP506MatterCurrentLinearPlebanskiLocalActualLift_gaugeAuxiliary_zero :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gaugeAuxiliary =
      0 := by
  change positiveP506MatterCurrentLinearPlebanskiBaseActual.gaugeAuxiliary = 0
  rw [positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]
  exact
    positiveP506MatterCurrentEinsteinCartanLocalActualLift_gaugeAuxiliary_zero

theorem positiveP506MatterCurrentLinearPlebanskiLocalActualLift_scalar_vacuum :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  change
    positiveP506MatterCurrentLinearPlebanskiBaseActual.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource
  rw [positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]
  exact positiveP506MatterCurrentEinsteinCartanLocalActualLift_scalar_vacuum

theorem positiveP506MatterCurrentLinearPlebanskiLocalActualLift_matter_origin :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter 0 =
      positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter 0 := by
  change
    positiveP506MatterCurrentLinearPlebanskiBaseActual.matter 0 =
      positiveP506MatterCurrentEinsteinCartanLocalActualLift.matter 0
  rw [positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_conjugate_origin :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.conjugateMatter 0 =
      positiveP506MatterCurrentEinsteinCartanLocalActualLift.conjugateMatter
        0 := by
  change
    positiveP506MatterCurrentLinearPlebanskiBaseActual.conjugateMatter 0 =
      positiveP506MatterCurrentEinsteinCartanLocalActualLift.conjugateMatter 0
  rw [positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_coframe_one
    (point : BasePoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.coframe point =
      1 := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_coframe,
    positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]
  exact positiveP506MatterCurrentEinsteinCartanLocalActualLift_coframe point

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliary_eq
    (point : BasePoint) :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityAuxiliary
        point =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_gravityAuxiliary,
    positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]
  exact
    positiveP506MatterCurrentEinsteinCartanLocalActualLift_gravityAuxiliary_eq
      point

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_connection_origin :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityConnection
        0 := by
  exact
    normalizedAffineLorentzConnectionField_zero
      (positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityConnection 0)
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_origin :
    holonomicGravityCurvature
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 =
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          (positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityConnection
            0)
          positiveP506MatterCurrentLinearPlebanskiCurvatureTarget)
        0 =
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
  exact
    holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

theorem
    positiveP506MatterCurrentLinearPlebanskiCurvatureTarget_ne_uncoupled :
    positiveP506MatterCurrentLinearPlebanskiCurvatureTarget ≠
      gravityInternalDualEquiv
        (physicalIIPlusBivector (1 : LorentzianCoframe)) := by
  intro targetUncoupled
  have multiplierZero :
      positiveP506MatterCurrentLinearPlebanskiMultiplier = 0 := by
    exact sub_eq_self.mp targetUncoupled
  exact
    positiveP506MatterCurrentLinearPlebanskiMultiplier_nonzero multiplierZero

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_interactionSensitive :
    holonomicGravityCurvature
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 ≠
      gravityInternalDualEquiv
        (physicalIIPlusBivector (1 : LorentzianCoframe)) := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_origin]
  exact
    positiveP506MatterCurrentLinearPlebanskiCurvatureTarget_ne_uncoupled

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliaryBalance :
    holonomicGravityCurvature
          positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 -
        gravityInternalDualEquiv
          (positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityAuxiliary
            0) +
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravitySimplicityMultiplier
          0 =
      0 := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_origin,
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliary_eq,
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_multiplier]
  unfold positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
  abel

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_simplicity :
    GravitySimplicityEquation
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift := by
  intro point
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliary_eq,
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_coframe_one]

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_nondegenerate :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.Nondegenerate := by
  intro point
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_coframe_one]
  simp

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_smooth :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.Smooth := by
  have baseSmooth :
      positiveP506MatterCurrentLinearPlebanskiBaseActual.Smooth := by
    rw [
      positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual]
    exact positiveP506MatterCurrentEinsteinCartanLocalActualLift_smooth
  rcases baseSmooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      _gravityMultiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth,
      normalizedAffineLorentzConnectionField_smooth _ _,
      gravityAuxiliarySmooth,
      by
        intro internalPair spacetimePair
        change ContDiff ℝ ∞ fun _ : BasePoint =>
          positiveP506MatterCurrentLinearPlebanskiMultiplier
            internalPair spacetimePair
        fun_prop,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩

theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_lorentzSkew
    (point : BasePoint) :
    LorentzSkew
      (positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityConnection
        point) := by
  apply normalizedAffineLorentzConnectionField_lorentzSkew
  rw [
    positiveP506MatterCurrentLinearPlebanskiBaseActual_eq_feedbackActual,
    positiveP506MatterCurrentEinsteinCartanLocalActualLift_connection_origin]
  exact
    lorentzSkewConnectionOfBivectorOneForm_lorentzSkew
      positiveP506MatterCurrentEinsteinCartanContorsionCoordinates

/-! ## Matter action retained at the generated contact -/

/-- Actual continuum field read from `U₂` at the generated contact. -/
def positiveP506MatterCurrentLinearPlebanskiOriginField :
    StageNineContinuumPointField :=
  toContinuumPointField
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0

theorem positiveP506MatterCurrentLinearPlebanskiOriginField_coframe :
    positiveP506MatterCurrentLinearPlebanskiOriginField.coframe = 1 := by
  exact
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_coframe_one 0

theorem
    positiveP506MatterCurrentLinearPlebanskiOriginField_matterDerivative :
    positiveP506MatterCurrentLinearPlebanskiOriginField.matterCovariantDerivative =
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.matterCovariantDerivative := by
  funext direction
  change
    holonomicMatterCovariantDerivative
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 direction =
      holonomicMatterCovariantDerivative
        positiveP506MatterCurrentLinearPlebanskiBaseActual 0 direction
  unfold holonomicMatterCovariantDerivative
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_connection_origin]
  rfl

theorem positiveP506MatterCurrentLinearPlebanskiOriginField_scalar :
    positiveP506MatterCurrentLinearPlebanskiOriginField.scalar =
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.scalar := by
  change
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.scalar 0 =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.scalar 0
  rfl

theorem positiveP506MatterCurrentLinearPlebanskiOriginField_matter :
    positiveP506MatterCurrentLinearPlebanskiOriginField.matter =
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.matter := by
  change
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter 0 =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.matter 0
  rfl

theorem positiveP506MatterCurrentLinearPlebanskiOriginField_conjugate :
    positiveP506MatterCurrentLinearPlebanskiOriginField.conjugateMatter =
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.conjugateMatter := by
  change
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.conjugateMatter 0 =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.conjugateMatter 0
  rfl

theorem
    generatedContinuumMatterVector_positiveP506LinearPlebanski_withCoframe
    (candidate : LorentzianCoframe) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe
          positiveP506MatterCurrentLinearPlebanskiOriginField candidate) =
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
          candidate) := by
  unfold generatedContinuumMatterVector
  simp only [withCoframe]
  rw [
    positiveP506MatterCurrentLinearPlebanskiOriginField_matterDerivative,
    positiveP506MatterCurrentLinearPlebanskiOriginField_scalar,
    positiveP506MatterCurrentLinearPlebanskiOriginField_matter]

theorem
    generatedContinuumMatterDensity_positiveP506LinearPlebanski_withCoframe
    (candidate : LorentzianCoframe) :
    generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
        (withCoframe
          positiveP506MatterCurrentLinearPlebanskiOriginField candidate) =
      generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
        (withCoframe
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
          candidate) := by
  unfold generatedContinuumMatterDensity
  change
    (matterDualFrameRelative positiveSmoothUnifiedSource 0 0
        positiveP506MatterCurrentLinearPlebanskiOriginField.conjugateMatter
      (generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe
          positiveP506MatterCurrentLinearPlebanskiOriginField
          candidate))).re =
      (matterDualFrameRelative positiveSmoothUnifiedSource 0 0
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.conjugateMatter
        (generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe
            positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
            candidate))).re
  rw [
    positiveP506MatterCurrentLinearPlebanskiOriginField_conjugate,
    generatedContinuumMatterVector_positiveP506LinearPlebanski_withCoframe]

theorem
    coframeMatterSectorLocalDensity_positiveP506LinearPlebanski
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentLinearPlebanskiOriginField candidate =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
        candidate := by
  change
    abs (Matrix.det candidate) *
        generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
          (withCoframe
            positiveP506MatterCurrentLinearPlebanskiOriginField candidate) =
      abs (Matrix.det candidate) *
        generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
          (withCoframe
            positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
            candidate)
  rw [
    generatedContinuumMatterDensity_positiveP506LinearPlebanski_withCoframe]

theorem
    coframeMatterSectorStress_positiveP506LinearPlebanski :
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentLinearPlebanskiOriginField =
      positiveP506MatterCurrentEinsteinCartanMatterStress := by
  change
    fderiv ℝ
        (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentLinearPlebanskiOriginField)
        positiveP506MatterCurrentLinearPlebanskiOriginField.coframe =
      fderiv ℝ
        (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField)
        positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.coframe
  rw [
    show
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentLinearPlebanskiOriginField =
        coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField by
      funext candidate
      exact
        coframeMatterSectorLocalDensity_positiveP506LinearPlebanski candidate,
    positiveP506MatterCurrentLinearPlebanskiOriginField_coframe,
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_coframe]

theorem
    positiveP506MatterCurrentLinearPlebanski_coframePrincipalBalance
    (variation : LorentzianCoframe) :
    linearPlebanskiCoframePrincipal
          positiveP506MatterCurrentLinearPlebanskiCoframeResponse variation +
        coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentLinearPlebanskiOriginField variation =
      0 := by
  rw [coframeMatterSectorStress_positiveP506LinearPlebanski]
  have principal :=
    DFunLike.congr_fun
      (linearPlebanskiCoframePrincipal_response_eq_neg
        positiveP506MatterCurrentEinsteinCartanMatterStress)
      variation
  change
    linearPlebanskiCoframePrincipal
        positiveP506MatterCurrentLinearPlebanskiCoframeResponse variation =
      -positiveP506MatterCurrentEinsteinCartanMatterStress variation
    at principal
  rw [principal]
  ring

theorem
    coframeMatterSectorLocalDensity_positiveP506LinearPlebanski_path_hasDerivAt
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentLinearPlebanskiOriginField
          ((1 : LorentzianCoframe) + parameter • variation))
      (coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentLinearPlebanskiOriginField variation)
      0 := by
  have nondegenerate :
      Matrix.det
          positiveP506MatterCurrentLinearPlebanskiOriginField.coframe ≠
        0 := by
    rw [positiveP506MatterCurrentLinearPlebanskiOriginField_coframe]
    simp
  have actionDerivative :=
    coframeMatterSectorLocalDensity_hasFDerivAt positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentLinearPlebanskiOriginField
      nondegenerate
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have coordinateDerivative :=
    identityDerivative.smul_const variation
  have coordinateDerivativeValue :
      (1 : ℝ) • variation = variation := by
    simp
  have coordinateDerivativeAtZero :=
    coordinateDerivative.congr_deriv coordinateDerivativeValue
  have pathDerivative :=
    coordinateDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have pointEquality :
      positiveP506MatterCurrentLinearPlebanskiOriginField.coframe =
        (1 : LorentzianCoframe) + (0 : ℝ) • variation := by
    rw [positiveP506MatterCurrentLinearPlebanskiOriginField_coframe]
    simp
  exact
    actionDerivative.comp_hasDerivAt_of_eq
      (0 : ℝ) pathDerivative pointEquality

/-- The actual matter density and the action-generated linear-Plebanski
constraint have zero combined coframe derivative in every direction. -/
theorem
    positiveP506MatterCurrentLinearPlebanski_coframeActionPath_hasDerivAt
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity
            positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary
            positiveP506MatterCurrentLinearPlebanskiOriginField.gravitySimplicityMultiplier
            ((1 : LorentzianCoframe) + parameter • variation) +
          coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
            positiveP506MatterCurrentLinearPlebanskiOriginField
            ((1 : LorentzianCoframe) + parameter • variation))
      0 0 := by
  have auxiliaryAtOrigin :
      positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary =
        physicalIIPlusBivector (1 : LorentzianCoframe) := by
    exact
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliary_eq 0
  have multiplierAtOrigin :
      positiveP506MatterCurrentLinearPlebanskiOriginField.gravitySimplicityMultiplier =
        positiveP506MatterCurrentLinearPlebanskiMultiplier := by
    exact
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift_multiplier 0
  rw [auxiliaryAtOrigin, multiplierAtOrigin]
  have simplicityDerivative :=
    linearPlebanskiSimplicityDensity_response_path_hasDerivAt
      positiveP506MatterCurrentEinsteinCartanMatterStress variation
  have matterDerivative :=
    coframeMatterSectorLocalDensity_positiveP506LinearPlebanski_path_hasDerivAt
      variation
  have combined := simplicityDerivative.add matterDerivative
  have derivativeZero :
      -positiveP506MatterCurrentEinsteinCartanMatterStress variation +
          coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
            positiveP506MatterCurrentLinearPlebanskiOriginField variation =
        0 := by
    rw [coframeMatterSectorStress_positiveP506LinearPlebanski]
    ring
  exact combined.congr_deriv derivativeZero

/-! ## Auxiliary action principal -/

theorem gravityCoframePairing_one_eq_coordinate
    (first second : PhysicalBivector) :
    gravityCoframePairing (1 : LorentzianCoframe) first second =
      gravityCoordinatePairing first second := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
    gravityCoordinatePairing
  simp_rw [coframeTwoFormLinear_one]
  apply Finset.sum_congr rfl
  intro internalPair _
  simp only [LinearMap.id_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  ring

theorem gravitySpacetimeHodge_one_eq_identity
    (bivector : PhysicalBivector) :
    gravitySpacetimeHodge (1 : LorentzianCoframe) bivector =
      identityCoframeSpacetimeHodge bivector := by
  unfold gravitySpacetimeHodge identityCoframeSpacetimeHodge
  rw [coframeGaugeSpacetimeHodgeLinear,
    inverseCoframeTwoFormLinear, inv_one,
    coframeTwoFormLinear_one]
  rfl

theorem gravityCoordinatePairing_identityHodge_symmetric
    (first second : PhysicalBivector) :
    gravityCoordinatePairing first
        (identityCoframeSpacetimeHodge second) =
      gravityCoordinatePairing
        (identityCoframeSpacetimeHodge first) second := by
  unfold gravityCoordinatePairing identityCoframeSpacetimeHodge
  apply Finset.sum_congr rfl
  intro internalPair _
  calc
    (∑ spacetimePair : Fin 6,
      lorentzianTwoFormSign internalPair *
        lorentzianTwoFormSign spacetimePair *
        first internalPair spacetimePair *
        lorentzianCoframeHodge (second internalPair) spacetimePair) =
        lorentzianTwoFormSign internalPair *
          (∑ spacetimePair : Fin 6,
            lorentzianTwoFormSign spacetimePair *
              first internalPair spacetimePair *
              lorentzianCoframeHodge (second internalPair)
                spacetimePair) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro spacetimePair _
      ring
    _ = lorentzianTwoFormSign internalPair *
          (∑ spacetimePair : Fin 6,
            lorentzianTwoFormSign spacetimePair *
              lorentzianCoframeHodge (first internalPair) spacetimePair *
              second internalPair spacetimePair) := by
      rw [fixedLorentzTwoFormPairing_hodge_symmetric]
    _ = ∑ spacetimePair : Fin 6,
      lorentzianTwoFormSign internalPair *
        lorentzianTwoFormSign spacetimePair *
        lorentzianCoframeHodge (first internalPair) spacetimePair *
        second internalPair spacetimePair := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro spacetimePair _
      ring

theorem identity_linearPlebanskiAuxiliary_pairing_cancel
    (multiplier variation : PhysicalBivector) :
    gravityCoframePairing (1 : LorentzianCoframe) variation
          (gravitySpacetimeHodge (1 : LorentzianCoframe) (-multiplier)) +
        gravityCoordinatePairing multiplier
          (identityCoframeSpacetimeHodge variation) =
      0 := by
  rw [gravityCoframePairing_one_eq_coordinate,
    gravitySpacetimeHodge_one_eq_identity]
  rw [show
      identityCoframeSpacetimeHodge (-multiplier) =
        -identityCoframeSpacetimeHodge multiplier by
    funext internalPair spacetimePair
    simp [identityCoframeSpacetimeHodge, map_neg]]
  rw [show
      gravityCoordinatePairing variation
          (-identityCoframeSpacetimeHodge multiplier) =
        -gravityCoordinatePairing variation
          (identityCoframeSpacetimeHodge multiplier) by
    unfold gravityCoordinatePairing
    simp]
  rw [show
      gravityCoordinatePairing variation
          (identityCoframeSpacetimeHodge multiplier) =
        gravityCoordinatePairing
          (identityCoframeSpacetimeHodge multiplier) variation by
    unfold gravityCoordinatePairing
    apply Finset.sum_congr rfl
    intro internalPair _
    apply Finset.sum_congr rfl
    intro spacetimePair _
    ring]
  rw [← gravityCoordinatePairing_identityHodge_symmetric]
  ring

theorem generatedGravityBFDensity_auxiliary_path_hasDerivAt
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        generatedGravityBFDensity
          (withGravityAuxiliary field
            (field.gravityAuxiliary + parameter • variation)))
      (gravityAuxiliaryBFFirstVariationDensity field variation)
      0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have polynomial :=
    ((identityDerivative.const_mul
      (gravityAuxiliaryBFFirstVariationDensity field variation)).add
    ((identityDerivative.pow 2).const_mul
      (gravityAuxiliaryBFSecondVariationDensity field variation))).const_add
        (generatedGravityBFDensity field)
  have formulaEventually : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun parameter : ℝ =>
        generatedGravityBFDensity
          (withGravityAuxiliary field
            (field.gravityAuxiliary + parameter • variation)))
      (fun parameter : ℝ =>
        generatedGravityBFDensity field +
          (gravityAuxiliaryBFFirstVariationDensity field variation *
              parameter +
            gravityAuxiliaryBFSecondVariationDensity field variation *
              parameter ^ 2)) :=
    Filter.Eventually.of_forall fun parameter => by
      change
        generatedGravityBFDensity
            (withGravityAuxiliary field
              (field.gravityAuxiliary + parameter • variation)) =
          generatedGravityBFDensity field +
            (gravityAuxiliaryBFFirstVariationDensity field variation *
                parameter +
              gravityAuxiliaryBFSecondVariationDensity field variation *
                parameter ^ 2)
      rw [generatedGravityBFDensity_auxiliary_quadratic]
      ring
  have exactDerivative :=
    polynomial.congr_of_eventuallyEq formulaEventually
  simpa using exactDerivative

theorem gravityCoordinatePairing_add_right
    (residual first second : PhysicalBivector) :
    gravityCoordinatePairing residual (first + second) =
      gravityCoordinatePairing residual first +
        gravityCoordinatePairing residual second := by
  calc
    gravityCoordinatePairing residual (first + second) =
        gravityCoframePairing (1 : LorentzianCoframe) residual
          (first + second) := by
      rw [gravityCoframePairing_one_eq_coordinate]
    _ = gravityCoframePairing (1 : LorentzianCoframe) residual first +
          gravityCoframePairing (1 : LorentzianCoframe) residual second := by
      rw [gravityCoframePairing_add_right]
    _ = gravityCoordinatePairing residual first +
          gravityCoordinatePairing residual second := by
      rw [gravityCoframePairing_one_eq_coordinate,
        gravityCoframePairing_one_eq_coordinate]

theorem gravityCoordinatePairing_smul_right
    (parameter : ℝ) (residual bivector : PhysicalBivector) :
    gravityCoordinatePairing residual (parameter • bivector) =
      parameter * gravityCoordinatePairing residual bivector := by
  calc
    gravityCoordinatePairing residual (parameter • bivector) =
        gravityCoframePairing (1 : LorentzianCoframe) residual
          (parameter • bivector) := by
      rw [gravityCoframePairing_one_eq_coordinate]
    _ = parameter *
          gravityCoframePairing (1 : LorentzianCoframe) residual
            bivector := by
      rw [gravityCoframePairing_smul_right]
    _ = parameter * gravityCoordinatePairing residual bivector := by
      rw [gravityCoframePairing_one_eq_coordinate]

theorem identityCoframeSpacetimeHodge_add
    (first second : PhysicalBivector) :
    identityCoframeSpacetimeHodge (first + second) =
      identityCoframeSpacetimeHodge first +
        identityCoframeSpacetimeHodge second := by
  funext internalPair spacetimePair
  simp [identityCoframeSpacetimeHodge, map_add]

theorem identityCoframeSpacetimeHodge_smul
    (parameter : ℝ) (bivector : PhysicalBivector) :
    identityCoframeSpacetimeHodge (parameter • bivector) =
      parameter • identityCoframeSpacetimeHodge bivector := by
  funext internalPair spacetimePair
  simp [identityCoframeSpacetimeHodge, map_smul]

theorem linearPlebanskiSimplicityDensity_auxiliary_path_expansion
    (auxiliary multiplier variation : PhysicalBivector)
    (parameter : ℝ) :
    linearPlebanskiSimplicityDensity
        (auxiliary + parameter • variation) multiplier
        (1 : LorentzianCoframe) =
      linearPlebanskiSimplicityDensity auxiliary multiplier
          (1 : LorentzianCoframe) +
        parameter *
          gravityCoordinatePairing multiplier
            (identityCoframeSpacetimeHodge variation) := by
  unfold linearPlebanskiSimplicityDensity
  rw [show
    auxiliary + parameter • variation -
        physicalIIPlusBivector (1 : LorentzianCoframe) =
      (auxiliary - physicalIIPlusBivector (1 : LorentzianCoframe)) +
        parameter • variation by
    abel]
  rw [identityCoframeSpacetimeHodge_add,
    identityCoframeSpacetimeHodge_smul,
    gravityCoordinatePairing_add_right,
    gravityCoordinatePairing_smul_right]

theorem linearPlebanskiSimplicityDensity_auxiliary_path_hasDerivAt
    (auxiliary multiplier variation : PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity
          (auxiliary + parameter • variation) multiplier
          (1 : LorentzianCoframe))
      (gravityCoordinatePairing multiplier
        (identityCoframeSpacetimeHodge variation))
      0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have polynomial :=
    (identityDerivative.const_mul
      (gravityCoordinatePairing multiplier
        (identityCoframeSpacetimeHodge variation))).const_add
          (linearPlebanskiSimplicityDensity auxiliary multiplier
            (1 : LorentzianCoframe))
  have formulaEventually : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity
          (auxiliary + parameter • variation) multiplier
          (1 : LorentzianCoframe))
      (fun parameter : ℝ =>
        linearPlebanskiSimplicityDensity auxiliary multiplier
            (1 : LorentzianCoframe) +
          gravityCoordinatePairing multiplier
              (identityCoframeSpacetimeHodge variation) *
            parameter) :=
    Filter.Eventually.of_forall fun parameter => by
      change
        linearPlebanskiSimplicityDensity
            (auxiliary + parameter • variation) multiplier
            (1 : LorentzianCoframe) =
          linearPlebanskiSimplicityDensity auxiliary multiplier
              (1 : LorentzianCoframe) +
            gravityCoordinatePairing multiplier
                (identityCoframeSpacetimeHodge variation) *
              parameter
      rw [linearPlebanskiSimplicityDensity_auxiliary_path_expansion]
      ring
  have exactDerivative :=
    polynomial.congr_of_eventuallyEq formulaEventually
  simpa using exactDerivative

theorem
    positiveP506MatterCurrentLinearPlebanskiOriginField_multiplier :
    positiveP506MatterCurrentLinearPlebanskiOriginField.gravitySimplicityMultiplier =
      positiveP506MatterCurrentLinearPlebanskiMultiplier := by
  exact
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_multiplier 0

theorem
    positiveP506MatterCurrentLinearPlebanskiOriginField_auxiliary :
    positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  exact
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliary_eq 0

theorem
    positiveP506MatterCurrentLinearPlebanskiOriginField_auxiliaryResidual :
    gravityAuxiliaryEquationResidual
        positiveP506MatterCurrentLinearPlebanskiOriginField =
      -positiveP506MatterCurrentLinearPlebanskiMultiplier := by
  change
    holonomicGravityCurvature
          positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 -
        gravityInternalDualEquiv
          (positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityAuxiliary
            0) =
      -positiveP506MatterCurrentLinearPlebanskiMultiplier
  rw [
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_origin,
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_auxiliary_eq]
  unfold positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
  abel

theorem
    positiveP506MatterCurrentLinearPlebanskiOriginField_BFAuxiliaryPrincipal
    (variation : PhysicalBivector) :
    gravityAuxiliaryBFFirstVariationDensity
        positiveP506MatterCurrentLinearPlebanskiOriginField variation =
      gravityCoframePairing (1 : LorentzianCoframe) variation
        (gravitySpacetimeHodge (1 : LorentzianCoframe)
          (-positiveP506MatterCurrentLinearPlebanskiMultiplier)) := by
  rw [gravityAuxiliaryBFFirstVariationDensity_eq_residualPairing
    positiveP506MatterCurrentLinearPlebanskiOriginField
    (by
      rw [
        positiveP506MatterCurrentLinearPlebanskiOriginField_coframe]
      simp)
    variation]
  rw [
    positiveP506MatterCurrentLinearPlebanskiOriginField_coframe,
    positiveP506MatterCurrentLinearPlebanskiOriginField_auxiliaryResidual]

/-- The same action-generated multiplier closes the complete BF plus linear
Plebanski auxiliary derivative in every physical-bivector direction. -/
theorem
    positiveP506MatterCurrentLinearPlebanski_auxiliaryActionPath_hasDerivAt
    (variation : PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        generatedGravityBFDensity
            (withGravityAuxiliary
              positiveP506MatterCurrentLinearPlebanskiOriginField
              (positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary +
                parameter • variation)) +
          linearPlebanskiSimplicityDensity
            (positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary +
              parameter • variation)
            positiveP506MatterCurrentLinearPlebanskiOriginField.gravitySimplicityMultiplier
            positiveP506MatterCurrentLinearPlebanskiOriginField.coframe)
      0 0 := by
  rw [
    positiveP506MatterCurrentLinearPlebanskiOriginField_coframe,
    positiveP506MatterCurrentLinearPlebanskiOriginField_multiplier]
  have bfDerivative :=
    generatedGravityBFDensity_auxiliary_path_hasDerivAt
      positiveP506MatterCurrentLinearPlebanskiOriginField variation
  have linearDerivative :=
    linearPlebanskiSimplicityDensity_auxiliary_path_hasDerivAt
      positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary
      positiveP506MatterCurrentLinearPlebanskiMultiplier variation
  have combined := bfDerivative.add linearDerivative
  have derivativeZero :
      gravityAuxiliaryBFFirstVariationDensity
            positiveP506MatterCurrentLinearPlebanskiOriginField variation +
          gravityCoordinatePairing
            positiveP506MatterCurrentLinearPlebanskiMultiplier
            (identityCoframeSpacetimeHodge variation) =
        0 := by
    rw [
      positiveP506MatterCurrentLinearPlebanskiOriginField_BFAuxiliaryPrincipal]
    exact
      identity_linearPlebanskiAuxiliary_pairing_cancel
        positiveP506MatterCurrentLinearPlebanskiMultiplier variation
  exact combined.congr_deriv derivativeZero

/-! ## Bundled no-premise frontier -/

structure PositiveP506MatterCurrentLinearPlebanskiLocalActualLaw : Prop where
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  pathFirstPrimitiveResponseGenerated :
    PositiveP506MatterCurrentEinsteinCartanPrimitiveCauchyUpdateLaw
  retainsBasePrimitiveFields :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.coframe =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.coframe ∧
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityAuxiliary =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityAuxiliary ∧
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gaugeConnection =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.gaugeConnection ∧
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gaugeAuxiliary =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.gaugeAuxiliary ∧
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.scalar =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.scalar ∧
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.matter =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.matter ∧
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift.conjugateMatter =
        positiveP506MatterCurrentLinearPlebanskiBaseActual.conjugateMatter
  coframeResponseNonzero :
    positiveP506MatterCurrentLinearPlebanskiCoframeResponse ≠ 0
  multiplierNonzero :
    positiveP506MatterCurrentLinearPlebanskiMultiplier ≠ 0
  smooth :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.Smooth
  nondegenerate :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.Nondegenerate
  simplicity :
    GravitySimplicityEquation
      positiveP506MatterCurrentLinearPlebanskiLocalActualLift
  lorentzSkew :
    ∀ point,
      LorentzSkew
        (positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityConnection
          point)
  originConnectionRetained :
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentLinearPlebanskiBaseActual.gravityConnection 0
  originCurvatureGenerated :
    holonomicGravityCurvature
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 =
      positiveP506MatterCurrentLinearPlebanskiCurvatureTarget
  curvatureInteractionSensitive :
    holonomicGravityCurvature
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift 0 ≠
      gravityInternalDualEquiv
        (physicalIIPlusBivector (1 : LorentzianCoframe))
  matterStressRetained :
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentLinearPlebanskiOriginField =
      positiveP506MatterCurrentEinsteinCartanMatterStress
  coframeActionPathStationary :
    ∀ variation : LorentzianCoframe,
      HasDerivAt
        (fun parameter : ℝ =>
          linearPlebanskiSimplicityDensity
              positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary
              positiveP506MatterCurrentLinearPlebanskiOriginField.gravitySimplicityMultiplier
              ((1 : LorentzianCoframe) + parameter • variation) +
            coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
              positiveP506MatterCurrentLinearPlebanskiOriginField
              ((1 : LorentzianCoframe) + parameter • variation))
        0 0
  auxiliaryActionPathStationary :
    ∀ variation : PhysicalBivector,
      HasDerivAt
        (fun parameter : ℝ =>
          generatedGravityBFDensity
              (withGravityAuxiliary
                positiveP506MatterCurrentLinearPlebanskiOriginField
                (positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary +
                  parameter • variation)) +
            linearPlebanskiSimplicityDensity
              (positiveP506MatterCurrentLinearPlebanskiOriginField.gravityAuxiliary +
                parameter • variation)
              positiveP506MatterCurrentLinearPlebanskiOriginField.gravitySimplicityMultiplier
              positiveP506MatterCurrentLinearPlebanskiOriginField.coframe)
        0 0

/-- Frontier theorem: the exact P506/L0 source and actual joint dynamics
generate a complete interaction-sensitive local `U₂`.  The theorem accepts
no premise and closes the matter/linear-Plebanski coframe principal together
with the BF/linear-Plebanski auxiliary principal in every local direction. -/
theorem
    positiveP506MatterCurrentLinearPlebanskiLocalActualLift_realizes :
    PositiveP506MatterCurrentLinearPlebanskiLocalActualLaw := by
  exact
    { exactP506L0Lineage :=
        positiveSmoothUnifiedSource_generates_exactP506L0Lineage
      pathFirstPrimitiveResponseGenerated :=
        positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyUpdate_realizes
      retainsBasePrimitiveFields :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      coframeResponseNonzero :=
        positiveP506MatterCurrentLinearPlebanskiCoframeResponse_nonzero
      multiplierNonzero :=
        positiveP506MatterCurrentLinearPlebanskiMultiplier_nonzero
      smooth :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_smooth
      nondegenerate :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_nondegenerate
      simplicity :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_simplicity
      lorentzSkew :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_lorentzSkew
      originConnectionRetained :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_connection_origin
      originCurvatureGenerated :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_origin
      curvatureInteractionSensitive :=
        positiveP506MatterCurrentLinearPlebanskiLocalActualLift_curvature_interactionSensitive
      matterStressRetained :=
        coframeMatterSectorStress_positiveP506LinearPlebanski
      coframeActionPathStationary :=
        positiveP506MatterCurrentLinearPlebanski_coframeActionPath_hasDerivAt
      auxiliaryActionPathStationary :=
        positiveP506MatterCurrentLinearPlebanski_auxiliaryActionPath_hasDerivAt }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
