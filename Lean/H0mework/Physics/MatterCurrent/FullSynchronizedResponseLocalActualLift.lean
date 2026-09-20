import H0mework.Physics.MatterCurrent.P286CompleteResponseLocalActualLift
import H0mework.Physics.Dirac.EinsteinCartanSpinContorsionAction
import H0mework.Physics.Gauge.ConnectionSectorSourceBalance
import H0mework.Physics.Matter.ConjugateMatterActionTimeVelocity
import H0mework.Physics.Coframe.LinearPlebanskiGravityCoupledCoframeActionResponse
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm
import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureScalarLocalStationarity

/-!
# S9-C3h166: full synchronized response on the current P506 actual

C3h165 produces the complete P286 connection response `U₈`.  This module
continues the same path-first/action-first construction in dependency order:

```text
exact P506/L0 source
→ current complete P286 actual U₈
→ actual Dirac spin of U₈
→ unique Einstein--Cartan origin connection
→ current-state primal and adjoint matter germs
→ full non-gravity coframe stress of that updated actual
→ unique gravity-coupled coframe response
→ one synchronized nine-field local actual U*.
```

The intermediate names below are dependency layers of one constructor, not
independent closure claims.  The Lorentz, matter, and coframe equations used
to define their responses are checked downstream only as producer soundness.
Independent equations are stated separately after the final `U*` exists.

No residual, endpoint inverse, shell witness, source value, ansatz
coefficient, boundary constant, branch receipt, or supplied stationarity
certificate is accepted by the constructor.  The normalized affine carrier
is used only to turn an action-generated origin value and curvature into an
actual smooth Lorentz field; its carrier is already proved unique.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeSectorStress
open StageNineCoframeVariation
open StageNineConnectionSectorSourceBalance
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineMatterActionTimeVelocity
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePlebanskiMultiplierVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

/-! ## Current U8 action contact -/

abbrev positiveP506MatterCurrentCompleteBaseActual :
    StageNineHolonomicConfiguration :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift

theorem positiveP506MatterCurrentCompleteBaseActual_coframe_one
    (point : BasePoint) :
    positiveP506MatterCurrentCompleteBaseActual.coframe point = 1 :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift_coframe_one point

theorem positiveP506MatterCurrentCompleteBaseActual_gravityAuxiliary_simple
    (point : BasePoint) :
    positiveP506MatterCurrentCompleteBaseActual.gravityAuxiliary point =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  change
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravityAuxiliary
        point =
      physicalIIPlusBivector (1 : LorentzianCoframe)
  change
    actionGeneratedGravityAuxiliary
        positiveP506MatterCurrentP286GaussCauchyState
        positiveP506MatterCurrentP286AxisContact =
      physicalIIPlusBivector (1 : LorentzianCoframe)
  unfold actionGeneratedGravityAuxiliary
  rw [positiveP506MatterCurrentP286GaussCauchyState_coframe_axis]

/-! ## Action-generated Lorentz origin response -/

/-- The spin is read from the already generated complete P286 actual. -/
def positiveP506MatterCurrentCompleteActualSpin : LorentzBivectorOneForm :=
  actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
    positiveP506MatterCurrentCompleteBaseActual 0

/-- The Einstein--Cartan action fixes this response without a coupling or
branch input. -/
def positiveP506MatterCurrentCompleteActualContorsion :
    LorentzBivectorOneForm :=
  einsteinCartanSpinContorsionCoordinates
    positiveP506MatterCurrentCompleteActualSpin

def positiveP506MatterCurrentCompleteActionLorentzOrigin :
    PointwiseLorentzSpinConnection :=
  lorentzSkewConnectionOfBivectorOneForm
    positiveP506MatterCurrentCompleteActualContorsion

/-- The first internal layer updates the connection origin selected by the
actual spin while preserving the current derived gravity curvature. -/
def positiveP506MatterCurrentLorentzResponseLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentCompleteBaseActual with
    gravityConnection :=
      normalizedAffineLorentzConnectionField
        positiveP506MatterCurrentCompleteActionLorentzOrigin
        (holonomicGravityCurvature
          positiveP506MatterCurrentCompleteBaseActual 0) }

@[simp] theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_coframe :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.coframe =
      positiveP506MatterCurrentCompleteBaseActual.coframe :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentLorentzResponseLocalActualLift_gravityAuxiliary :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityAuxiliary =
      positiveP506MatterCurrentCompleteBaseActual.gravityAuxiliary :=
  rfl

@[simp] theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeConnection :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection =
      positiveP506MatterCurrentCompleteBaseActual.gaugeConnection :=
  rfl

@[simp] theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeAuxiliary :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeAuxiliary =
      positiveP506MatterCurrentCompleteBaseActual.gaugeAuxiliary :=
  rfl

@[simp] theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_scalar :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.scalar =
      positiveP506MatterCurrentCompleteBaseActual.scalar :=
  rfl

@[simp] theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_matter :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.matter =
      positiveP506MatterCurrentCompleteBaseActual.matter :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentLorentzResponseLocalActualLift_conjugateMatter :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter =
      positiveP506MatterCurrentCompleteBaseActual.conjugateMatter :=
  rfl

theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_connection_origin :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentCompleteActionLorentzOrigin :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_curvature_origin :
    holonomicGravityCurvature
        positiveP506MatterCurrentLorentzResponseLocalActualLift 0 =
      holonomicGravityCurvature
        positiveP506MatterCurrentCompleteBaseActual 0 := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          positiveP506MatterCurrentCompleteActionLorentzOrigin
          (holonomicGravityCurvature
            positiveP506MatterCurrentCompleteBaseActual 0)) 0 =
      holonomicGravityCurvature positiveP506MatterCurrentCompleteBaseActual 0
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

theorem positiveP506MatterCurrentLorentzResponseLocalActualLift_smooth :
    positiveP506MatterCurrentLorentzResponseLocalActualLift.Smooth := by
  rcases positiveP506MatterCurrentP286CompleteResponseLocalActualLift_smooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, normalizedAffineLorentzConnectionField_smooth _ _,
      gravityAuxiliarySmooth, multiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

/-! ## Current-state matter and adjoint-matter resynchronization -/

def positiveP506MatterCurrentLorentzResponseCauchyState :
    StageNineCauchyState :=
  canonicalCauchyRestriction 0
    positiveP506MatterCurrentLorentzResponseLocalActualLift

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 0 = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Fields-only action update.  It deliberately does not rebuild or erase
the complete P286 auxiliary germ already generated in C3h165. -/
def positiveP506MatterCurrentMatterResponseLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentLorentzResponseLocalActualLift with
    matter :=
      actionGeneratedMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0
    conjugateMatter :=
      actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0 }

@[simp] theorem positiveP506MatterCurrentMatterResponseLocalActualLift_coframe :
    positiveP506MatterCurrentMatterResponseLocalActualLift.coframe =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.coframe :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentMatterResponseLocalActualLift_gravityConnection :
    positiveP506MatterCurrentMatterResponseLocalActualLift.gravityConnection =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentMatterResponseLocalActualLift_gravityAuxiliary :
    positiveP506MatterCurrentMatterResponseLocalActualLift.gravityAuxiliary =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityAuxiliary :=
  rfl

@[simp] theorem positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeConnection :
    positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection :=
  rfl

@[simp] theorem positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeAuxiliary :
    positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeAuxiliary =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeAuxiliary :=
  rfl

@[simp] theorem positiveP506MatterCurrentMatterResponseLocalActualLift_scalar :
    positiveP506MatterCurrentMatterResponseLocalActualLift.scalar =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.scalar :=
  rfl

theorem positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin :
    positiveP506MatterCurrentMatterResponseLocalActualLift.matter 0 =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.matter 0 := by
  change
    actionGeneratedMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0 0 = _
  rw [actionGeneratedMatterLocalField_origin]
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.matter
        (canonicalCauchySlicePoint 0 0) =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.matter 0
  rw [canonicalCauchySlicePoint_zero_zero]

theorem
    positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin :
    positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter 0 =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
        0 := by
  change
    actionGeneratedConjugateMatterLocalField
        positiveP506MatterCurrentLorentzResponseCauchyState 0 0 = _
  rw [actionGeneratedConjugateMatterLocalField_origin]
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
        (canonicalCauchySlicePoint 0 0) =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
        0
  rw [canonicalCauchySlicePoint_zero_zero]

theorem positiveP506MatterCurrentMatterResponseLocalActualLift_smooth :
    positiveP506MatterCurrentMatterResponseLocalActualLift.Smooth := by
  rcases positiveP506MatterCurrentLorentzResponseLocalActualLift_smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, _conjugateMatterSmooth⟩
  rcases
      sourceActionGeneratedMatterDualLocalActualLift_smooth
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentLorentzResponseCauchyState 0 with
    ⟨_generatedCoframeSmooth, _generatedGravityConnectionSmooth,
      _generatedGravityAuxiliarySmooth, _generatedMultiplierSmooth,
      _generatedGaugeConnectionSmooth, _generatedGaugeAuxiliarySmooth,
      _generatedScalarSmooth, generatedMatterSmooth,
      generatedConjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, generatedMatterSmooth, generatedConjugateMatterSmooth⟩

/-! ## Full coframe response and final synchronized actual -/

def positiveP506MatterCurrentMatterResponseOriginField :
    StageNineContinuumPointField :=
  toContinuumPointField
    positiveP506MatterCurrentMatterResponseLocalActualLift 0

def positiveP506MatterCurrentFullNonGravityCoframeStress :
    LorentzianCoframe →L[ℝ] ℝ :=
  coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField +
    coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField +
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField

def positiveP506MatterCurrentFullCoframeResponse : LorentzianCoframe :=
  gravityCoupledLinearPlebanskiCoframeResponseOfStress
    positiveP506MatterCurrentFullNonGravityCoframeStress

def positiveP506MatterCurrentFullGravityMultiplier : PhysicalBivector :=
  gravityCoupledLinearPlebanskiMultiplier
    positiveP506MatterCurrentFullCoframeResponse

def positiveP506MatterCurrentFullGravityCurvature : PhysicalBivector :=
  gravityCoupledLinearPlebanskiCurvature
    positiveP506MatterCurrentFullCoframeResponse

/-- `U*`: one no-parameter current actual carrying all action-generated
responses in dependency order. -/
def positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentMatterResponseLocalActualLift with
    gravityConnection :=
      normalizedAffineLorentzConnectionField
        positiveP506MatterCurrentCompleteActionLorentzOrigin
        positiveP506MatterCurrentFullGravityCurvature
    gravitySimplicityMultiplier :=
      fun _ => positiveP506MatterCurrentFullGravityMultiplier }

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe =
      positiveP506MatterCurrentMatterResponseLocalActualLift.coframe :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityAuxiliary =
      positiveP506MatterCurrentMatterResponseLocalActualLift.gravityAuxiliary :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeConnection :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeConnection =
      positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeAuxiliary :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary =
      positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeAuxiliary :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_scalar :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar =
      positiveP506MatterCurrentMatterResponseLocalActualLift.scalar :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_matter :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter =
      positiveP506MatterCurrentMatterResponseLocalActualLift.matter :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_conjugateMatter :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter =
      positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter :=
  rfl

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
    (point : BasePoint) :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
        point =
      1 := by
  change positiveP506MatterCurrentCompleteBaseActual.coframe point = 1
  exact positiveP506MatterCurrentCompleteBaseActual_coframe_one point

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple
    (point : BasePoint) :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityAuxiliary
        point =
      physicalIIPlusBivector (1 : LorentzianCoframe) := by
  change positiveP506MatterCurrentCompleteBaseActual.gravityAuxiliary point = _
  exact
    positiveP506MatterCurrentCompleteBaseActual_gravityAuxiliary_simple point

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_connection_origin :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentCompleteActionLorentzOrigin :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_curvature_origin :
    holonomicGravityCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
      positiveP506MatterCurrentFullGravityCurvature := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          positiveP506MatterCurrentCompleteActionLorentzOrigin
          positiveP506MatterCurrentFullGravityCurvature) 0 =
      positiveP506MatterCurrentFullGravityCurvature
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_auxiliaryBalance :
    holonomicGravityCurvature
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 -
        gravityInternalDualEquiv
          (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityAuxiliary
            0) +
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravitySimplicityMultiplier
          0 =
      0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_curvature_origin,
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple]
  unfold positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
    positiveP506MatterCurrentFullGravityCurvature
    gravityCoupledLinearPlebanskiCurvature
    positiveP506MatterCurrentFullGravityMultiplier
  abel

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_simplicity :
    GravitySimplicityEquation
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift := by
  intro point
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple,
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one]

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_nondegenerate :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.Nondegenerate := by
  intro point
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one]
  simp

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.Smooth := by
  rcases positiveP506MatterCurrentMatterResponseLocalActualLift_smooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      _multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, normalizedAffineLorentzConnectionField_smooth _ _,
      gravityAuxiliarySmooth,
      by
        intro internalPair spacetimePair
        change ContDiff ℝ ∞ fun _ : BasePoint =>
          positiveP506MatterCurrentFullGravityMultiplier
            internalPair spacetimePair
        fun_prop,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩

/-! ## Canonical response uniqueness -/

theorem positiveP506MatterCurrentCompleteActualContorsion_response :
    simpleBEinsteinCartanGravityActionCoordinates
        positiveP506MatterCurrentCompleteActualContorsion =
      positiveP506MatterCurrentCompleteActualSpin :=
  simpleBGravityAction_contorsion _

theorem positiveP506MatterCurrentCompleteActualContorsion_unique
    (candidate : LorentzBivectorOneForm)
    (response :
      simpleBEinsteinCartanGravityActionCoordinates candidate =
        positiveP506MatterCurrentCompleteActualSpin) :
    candidate = positiveP506MatterCurrentCompleteActualContorsion := by
  rw [← contorsion_simpleBGravityAction candidate, response]
  rfl

theorem positiveP506MatterCurrentMatterTimeResponse_unique
    (candidate : DiracExteriorMatterCarrier)
    (response :
      IdentityCoframeMatterTimeActionLaw
        positiveP506MatterCurrentLorentzResponseCauchyState 0 candidate) :
    candidate =
      actionGeneratedMatterTimeCovariantDerivative
        positiveP506MatterCurrentLorentzResponseCauchyState 0 := by
  exact
    identityCoframeMatterTimeActionLaw_unique
      positiveP506MatterCurrentLorentzResponseCauchyState 0 candidate _
      response
      (actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw _ _)

theorem positiveP506MatterCurrentConjugateMatterTimeResponse_unique
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (response :
      IdentityCoframeConjugateMatterTimeActionLaw
        positiveP506MatterCurrentLorentzResponseCauchyState 0 candidate) :
    candidate =
      actionGeneratedConjugateMatterTimeDerivative
        positiveP506MatterCurrentLorentzResponseCauchyState 0 := by
  exact
    identityCoframeConjugateMatterTimeActionLaw_unique
      positiveP506MatterCurrentLorentzResponseCauchyState 0 candidate _
      response
      (actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw _ _)

theorem positiveP506MatterCurrentFullCoframeResponse_actionBalance
    (variation : LorentzianCoframe) :
    linearPlebanskiCoframePrincipal
          positiveP506MatterCurrentFullCoframeResponse variation +
        gravityBFCoframeFeedback
          positiveP506MatterCurrentFullCoframeResponse variation +
        positiveP506MatterCurrentFullNonGravityCoframeStress variation =
      0 :=
  gravityCoupledLinearPlebanskiCoframeResponse_actionBalance_apply _ _

theorem positiveP506MatterCurrentFullCoframeResponse_unique
    (candidate : LorentzianCoframe)
    (response :
      linearPlebanskiCoframePrincipal candidate +
          gravityBFCoframeFeedback candidate +
          positiveP506MatterCurrentFullNonGravityCoframeStress =
        0) :
    candidate = positiveP506MatterCurrentFullCoframeResponse :=
  gravityCoupledLinearPlebanskiCoframeResponse_unique _ candidate response

/-! ## Lorentz producer soundness on the final actual -/

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_spin :
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
      positiveP506MatterCurrentCompleteActualSpin := by
  unfold positiveP506MatterCurrentCompleteActualSpin
  apply actualMatterSpinActionCoordinates_eq_of_origin_fields
  · rfl
  · calc
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter
            0 =
          positiveP506MatterCurrentMatterResponseLocalActualLift.matter 0 :=
        rfl
      _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.matter 0 :=
        positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin
      _ = positiveP506MatterCurrentCompleteBaseActual.matter 0 := rfl
  · calc
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
            0 =
          positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter
            0 := rfl
      _ =
          positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
            0 :=
        positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin
      _ = positiveP506MatterCurrentCompleteBaseActual.conjugateMatter 0 := rfl

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzAlgebraicBalance
    (direction : LorentzBivectorOneForm) :
    lorentzGravityBFAlgebraicCoefficient
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 +
        lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
      0 := by
  exact
    actualSimpleBContorsion_algebraicBalance
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
      positiveP506MatterCurrentCompleteActualSpin
      (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
        0)
      (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple
        0)
      (by
        rw [
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_connection_origin]
        rfl)
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_spin
      direction

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzMomentum_constant
    (direction : PhysicalBivector) :
    lorentzConnectionBFDifferentialMomentum
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction =
      fun _ =>
        lorentzConnectionBFDifferentialMomentum
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 := by
  funext point
  unfold lorentzConnectionBFDifferentialMomentum
    generatedVolumeDensity toContinuumPointField
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
      point,
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple
      point,
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one
      0,
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gravityAuxiliary_simple
      0]

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzDivergence_zero
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionBFDifferentialMomentumDivergence
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0 := by
  unfold lorentzConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzMomentum_constant]
  simp [fieldDirectionalDerivative]

/-- This is producer consistency: the same actual spin selected the
Einstein--Cartan origin response installed above. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzEuler_origin
    (direction : LorentzBivectorOneForm) :
    lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0 := by
  rw [lorentzConnectionEulerLagrangeCoefficient,
    lorentzConnectionAlgebraicSpinCurrentCoefficient_eq_sectors,
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzDivergence_zero]
  simpa only [sub_zero] using
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzAlgebraicBalance
      direction

/-! ## Matter and adjoint-matter producer soundness -/

/-- Same-state action comparison object.  It is never used as the producer
output because doing so would erase the C3h165 P286 auxiliary response. -/
private abbrev positiveP506MatterCurrentMatterActionComparisonActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedMatterDualLocalActualLift
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentLorentzResponseCauchyState 0

theorem positiveP506MatterCurrentLorentzResponseCauchyState_coframe_zero :
    positiveP506MatterCurrentLorentzResponseCauchyState.coframe 0 = 1 := by
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.coframe
        (canonicalCauchySlicePoint 0 0) =
      1
  rw [canonicalCauchySlicePoint_zero_zero]
  change positiveP506MatterCurrentCompleteBaseActual.coframe 0 = 1
  exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0

private theorem final_matter_eq_comparison :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter =
      positiveP506MatterCurrentMatterActionComparisonActual.matter :=
  rfl

private theorem final_conjugateMatter_eq_comparison :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter =
      positiveP506MatterCurrentMatterActionComparisonActual.conjugateMatter :=
  rfl

private theorem final_coframe_eq_comparison :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe =
      positiveP506MatterCurrentMatterActionComparisonActual.coframe := by
  funext point
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one]
  change
    1 = positiveP506MatterCurrentLorentzResponseCauchyState.coframe 0
  exact
    positiveP506MatterCurrentLorentzResponseCauchyState_coframe_zero.symm

private theorem final_gravityConnection_origin_eq_comparison :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentMatterActionComparisonActual.gravityConnection
        0 := by
  have finalToState :
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityConnection
          0 =
        positiveP506MatterCurrentLorentzResponseCauchyState.gravityConnection
          0 := by
    rw [
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_connection_origin]
    unfold positiveP506MatterCurrentLorentzResponseCauchyState
      canonicalCauchyRestriction
    change
      positiveP506MatterCurrentCompleteActionLorentzOrigin =
        positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
          (canonicalCauchySlicePoint 0 0)
    rw [canonicalCauchySlicePoint_zero_zero,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_connection_origin]
  exact finalToState.trans
    (sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentLorentzResponseCauchyState 0).symm

private theorem final_gaugeConnection_origin_eq_comparison :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeConnection
        0 =
      positiveP506MatterCurrentMatterActionComparisonActual.gaugeConnection
        0 := by
  funext direction
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeConnection
          0 direction =
        positiveP506MatterCurrentLorentzResponseCauchyState.gaugeConnection
          0 direction := by
      unfold positiveP506MatterCurrentLorentzResponseCauchyState
        canonicalCauchyRestriction
      change
        positiveP506MatterCurrentCompleteBaseActual.gaugeConnection 0 direction =
          positiveP506MatterCurrentCompleteBaseActual.gaugeConnection
            (canonicalCauchySlicePoint 0 0) direction
      rw [canonicalCauchySlicePoint_zero_zero]
    _ =
        positiveP506MatterCurrentMatterActionComparisonActual.gaugeConnection
          0 direction :=
      (sourceGeneratedP286ActionLocalConnection_origin
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentLorentzResponseCauchyState 0 direction).symm

private theorem final_scalar_origin_eq_comparison :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar 0 =
      positiveP506MatterCurrentMatterActionComparisonActual.scalar 0 := by
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar 0 =
        positiveP506MatterCurrentLorentzResponseCauchyState.scalar 0 := by
      unfold positiveP506MatterCurrentLorentzResponseCauchyState
        canonicalCauchyRestriction
      change
        positiveP506MatterCurrentCompleteBaseActual.scalar 0 =
          positiveP506MatterCurrentCompleteBaseActual.scalar
            (canonicalCauchySlicePoint 0 0)
      rw [canonicalCauchySlicePoint_zero_zero]
    _ = positiveP506MatterCurrentMatterActionComparisonActual.scalar 0 :=
      (sourceGeneratedP286ActionLocalActualLift_scalar_origin
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentLorentzResponseCauchyState 0).symm

private theorem final_matterCovariantDerivative_origin_eq_comparison :
    holonomicMatterCovariantDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
      holonomicMatterCovariantDerivative
        positiveP506MatterCurrentMatterActionComparisonActual 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [final_matter_eq_comparison,
    final_gravityConnection_origin_eq_comparison,
    final_gaugeConnection_origin_eq_comparison]

/-- The primal Dirac--Yukawa equation is the forward check of the temporal
matter response generated above. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_diracYukawa_origin :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0) =
      0 := by
  have vectorEquality :
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
            0) =
        generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            positiveP506MatterCurrentMatterActionComparisonActual 0) := by
    unfold generatedContinuumMatterVector toContinuumPointField
    rw [final_coframe_eq_comparison, final_matter_eq_comparison,
      final_scalar_origin_eq_comparison,
      final_matterCovariantDerivative_origin_eq_comparison]
  rw [vectorEquality]
  exact
    sourceActionGeneratedMatterDualLocalActualLift_diracYukawa_origin
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentLorentzResponseCauchyState 0
      positiveP506MatterCurrentLorentzResponseCauchyState_coframe_zero

private theorem final_matterAlgebraic_origin_eq_comparison
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterActionComparisonActual direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
        holonomicMatterVariationAlgebraicDirection
          positiveP506MatterCurrentMatterActionComparisonActual direction 0 := by
    funext formDirection
    unfold holonomicMatterVariationAlgebraicDirection
    rw [final_gravityConnection_origin_eq_comparison,
      final_gaugeConnection_origin_eq_comparison]
  have vectorEquality :
      matterAlgebraicVariationVector positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
        matterAlgebraicVariationVector positiveSmoothUnifiedSource
          positiveP506MatterCurrentMatterActionComparisonActual direction 0 := by
    unfold matterAlgebraicVariationVector matterFieldVariationVector
    rw [matterGaugeKineticSum_zeroChart, matterGaugeKineticSum_zeroChart]
    simp only [toContinuumPointField]
    rw [final_coframe_eq_comparison, final_scalar_origin_eq_comparison,
      variationEquality]
  unfold matterAlgebraicDirectionalCoefficient generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [vectorEquality, final_coframe_eq_comparison,
    final_conjugateMatter_eq_comparison]

private theorem final_matterMomentum_eq_comparison
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterActionComparisonActual direction
        derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_comparison, final_conjugateMatter_eq_comparison]

private theorem final_matterDivergence_origin_eq_comparison
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterActionComparisonActual direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [final_matterMomentum_eq_comparison]

/-- The adjoint equation is likewise a forward consistency check of the
action-generated dual first jet. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_matterEuler_origin
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [final_matterAlgebraic_origin_eq_comparison,
    final_matterDivergence_origin_eq_comparison]
  exact
    sourceActionGeneratedMatterDualLocalActualLift_matterEulerLagrange_origin
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentLorentzResponseCauchyState 0
      positiveP506MatterCurrentLorentzResponseCauchyState_coframe_zero
      direction

/-! ## Same-actual coframe contact and producer soundness -/

def positiveP506MatterCurrentFullSynchronizedOriginField :
    StageNineContinuumPointField :=
  toContinuumPointField
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0

/-- Proof-only projection forgetting precisely the gravity slots unused by
the three non-gravity coframe sectors.  It is not a quotient or producer. -/
private def fullSynchronizedNonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

@[simp] private theorem gaugeDensity_projection
    (source : SmoothUnifiedSource) (field : StageNineContinuumPointField)
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity source
        (fullSynchronizedNonGravityContactProjection field) candidate =
      coframeGaugeSectorLocalDensity source field candidate :=
  rfl

@[simp] private theorem scalarDensity_projection
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity source point
        (fullSynchronizedNonGravityContactProjection field) candidate =
      coframeScalarSectorLocalDensity source point field candidate :=
  rfl

@[simp] private theorem matterDensity_projection
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity source point
        (fullSynchronizedNonGravityContactProjection field) candidate =
      coframeMatterSectorLocalDensity source point field candidate :=
  rfl

private theorem final_connection_origin_eq_matterResponse :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityConnection
        0 =
      positiveP506MatterCurrentMatterResponseLocalActualLift.gravityConnection
        0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_connection_origin]
  change
    positiveP506MatterCurrentCompleteActionLorentzOrigin =
      positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
        0
  exact
    positiveP506MatterCurrentLorentzResponseLocalActualLift_connection_origin.symm

private theorem final_matterCovariantDerivative_eq_matterResponse :
    positiveP506MatterCurrentFullSynchronizedOriginField.matterCovariantDerivative =
      positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative := by
  funext direction
  change
    holonomicMatterCovariantDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0
        direction =
      holonomicMatterCovariantDerivative
        positiveP506MatterCurrentMatterResponseLocalActualLift 0 direction
  unfold holonomicMatterCovariantDerivative
  rw [final_connection_origin_eq_matterResponse]
  rfl

theorem positiveP506MatterCurrentFullSynchronized_nonGravityContact_eq_base :
    fullSynchronizedNonGravityContactProjection
        positiveP506MatterCurrentFullSynchronizedOriginField =
      fullSynchronizedNonGravityContactProjection
        positiveP506MatterCurrentMatterResponseOriginField := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact final_matterCovariantDerivative_eq_matterResponse
  · rfl

private theorem final_gaugeDensity_eq_base
    (candidate : LorentzianCoframe) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedOriginField candidate =
      coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField candidate := by
  calc
    _ = coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          (fullSynchronizedNonGravityContactProjection
            positiveP506MatterCurrentFullSynchronizedOriginField)
          candidate := by rw [gaugeDensity_projection]
    _ = coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          (fullSynchronizedNonGravityContactProjection
            positiveP506MatterCurrentMatterResponseOriginField)
          candidate := by
      rw [positiveP506MatterCurrentFullSynchronized_nonGravityContact_eq_base]
    _ = _ := gaugeDensity_projection _ _ _

private theorem final_scalarDensity_eq_base
    (candidate : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentFullSynchronizedOriginField candidate =
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField candidate := by
  calc
    _ = coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
          (fullSynchronizedNonGravityContactProjection
            positiveP506MatterCurrentFullSynchronizedOriginField)
          candidate := by rw [scalarDensity_projection]
    _ = coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
          (fullSynchronizedNonGravityContactProjection
            positiveP506MatterCurrentMatterResponseOriginField)
          candidate := by
      rw [positiveP506MatterCurrentFullSynchronized_nonGravityContact_eq_base]
    _ = _ := scalarDensity_projection _ _ _ _

private theorem final_matterDensity_eq_base
    (candidate : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentFullSynchronizedOriginField candidate =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField candidate := by
  calc
    _ = coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          (fullSynchronizedNonGravityContactProjection
            positiveP506MatterCurrentFullSynchronizedOriginField)
          candidate := by rw [matterDensity_projection]
    _ = coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          (fullSynchronizedNonGravityContactProjection
            positiveP506MatterCurrentMatterResponseOriginField)
          candidate := by
      rw [positiveP506MatterCurrentFullSynchronized_nonGravityContact_eq_base]
    _ = _ := matterDensity_projection _ _ _ _

/-- The forward density on the dependency layer that generated the response. -/
def positiveP506MatterCurrentFullGeneratedCoframeActionDensity
    (candidate : LorentzianCoframe) : ℝ :=
  gravityCoupledLinearPlebanskiBFCoframeDensity
      positiveP506MatterCurrentFullCoframeResponse candidate +
    linearPlebanskiSimplicityDensity
      (physicalIIPlusBivector (1 : LorentzianCoframe))
      positiveP506MatterCurrentFullGravityMultiplier candidate +
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField candidate +
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField candidate +
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField candidate

/-- The same complete density read directly from the final actual contact. -/
def positiveP506MatterCurrentFullSynchronizedCoframeActionDensity
    (candidate : LorentzianCoframe) : ℝ :=
  gravityCoupledLinearPlebanskiBFCoframeDensity
      positiveP506MatterCurrentFullCoframeResponse candidate +
    linearPlebanskiSimplicityDensity
      (physicalIIPlusBivector (1 : LorentzianCoframe))
      positiveP506MatterCurrentFullGravityMultiplier candidate +
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedOriginField candidate +
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentFullSynchronizedOriginField candidate +
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentFullSynchronizedOriginField candidate

theorem positiveP506MatterCurrentFullSynchronizedCoframeActionDensity_eq_generated
    (candidate : LorentzianCoframe) :
    positiveP506MatterCurrentFullSynchronizedCoframeActionDensity candidate =
      positiveP506MatterCurrentFullGeneratedCoframeActionDensity candidate := by
  unfold positiveP506MatterCurrentFullSynchronizedCoframeActionDensity
    positiveP506MatterCurrentFullGeneratedCoframeActionDensity
  rw [final_gaugeDensity_eq_base, final_scalarDensity_eq_base,
    final_matterDensity_eq_base]

theorem positiveP506MatterCurrentFullSynchronizedCoframeActionDensity_function_eq :
    positiveP506MatterCurrentFullSynchronizedCoframeActionDensity =
      positiveP506MatterCurrentFullGeneratedCoframeActionDensity := by
  funext candidate
  exact
    positiveP506MatterCurrentFullSynchronizedCoframeActionDensity_eq_generated
      candidate

private theorem coframeDensity_affinePath_hasDerivAt
    (density : LorentzianCoframe → ℝ)
    (derivative : LorentzianCoframe →L[ℝ] ℝ)
    (hasDerivative : HasFDerivAt density derivative
      (1 : LorentzianCoframe))
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        density ((1 : LorentzianCoframe) + parameter • variation))
      (derivative variation) 0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative := identityDerivative.smul_const variation
  have variationDerivativeValue :
      (1 : ℝ) • variation = variation := by simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have pathDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have pointEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) + (0 : ℝ) • variation := by simp
  exact
    hasDerivative.comp_hasDerivAt_of_eq
      (0 : ℝ) pathDerivative pointEquality

/-- Forward derivative on the dependency layer that generated the unique
coframe response. -/
theorem
    positiveP506MatterCurrentFullGeneratedCoframeAction_path_hasDerivAt
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        positiveP506MatterCurrentFullGeneratedCoframeActionDensity
          ((1 : LorentzianCoframe) + parameter • variation))
      0 0 := by
  have gravityDerivative :=
    gravityCoupledLinearPlebanskiBFCoframeDensity_path_hasDerivAt
      positiveP506MatterCurrentFullCoframeResponse variation
  have linearDerivative :=
    linearPlebanskiSimplicityDensity_path_hasDerivAt
      positiveP506MatterCurrentFullCoframeResponse variation
  have baseCoframe :
      positiveP506MatterCurrentMatterResponseOriginField.coframe = 1 := by
    change positiveP506MatterCurrentCompleteBaseActual.coframe 0 = 1
    exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0
  have baseNondegenerate :
      Matrix.det positiveP506MatterCurrentMatterResponseOriginField.coframe ≠
        0 := by
    rw [baseCoframe]
    simp
  have gaugeHasDerivative :=
    coframeGaugeSectorLocalDensity_hasFDerivAt positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField baseNondegenerate
  rw [baseCoframe] at gaugeHasDerivative
  have gaugeDerivative :=
    coframeDensity_affinePath_hasDerivAt
      (coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField)
      (coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField)
      gaugeHasDerivative variation
  have scalarHasDerivative :=
    coframeScalarSectorLocalDensity_hasFDerivAt positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField baseNondegenerate
  rw [baseCoframe] at scalarHasDerivative
  have scalarDerivative :=
    coframeDensity_affinePath_hasDerivAt
      (coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField)
      (coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField)
      scalarHasDerivative variation
  have matterHasDerivative :=
    coframeMatterSectorLocalDensity_hasFDerivAt positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField baseNondegenerate
  rw [baseCoframe] at matterHasDerivative
  have matterDerivative :=
    coframeDensity_affinePath_hasDerivAt
      (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField)
      (coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField)
      matterHasDerivative variation
  have combined :=
    (((gravityDerivative.add linearDerivative).add gaugeDerivative).add
      scalarDerivative).add matterDerivative
  have derivativeZero :
      gravityBFCoframeFeedback
            positiveP506MatterCurrentFullCoframeResponse variation +
          linearPlebanskiCoframePrincipalValue
            positiveP506MatterCurrentFullCoframeResponse variation +
          coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
              positiveP506MatterCurrentMatterResponseOriginField variation +
          coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
              positiveP506MatterCurrentMatterResponseOriginField variation +
          coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
              positiveP506MatterCurrentMatterResponseOriginField variation =
        0 := by
    have balance :=
      positiveP506MatterCurrentFullCoframeResponse_actionBalance variation
    rw [linearPlebanskiCoframePrincipalValue_eq_principal]
    change
      linearPlebanskiCoframePrincipal
            positiveP506MatterCurrentFullCoframeResponse variation +
          gravityBFCoframeFeedback
            positiveP506MatterCurrentFullCoframeResponse variation +
          ((coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
                positiveP506MatterCurrentMatterResponseOriginField +
              coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
                positiveP506MatterCurrentMatterResponseOriginField) +
            coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
              positiveP506MatterCurrentMatterResponseOriginField) variation =
        0 at balance
    simp only [add_apply] at balance
    linarith
  exact combined.congr_deriv derivativeZero

theorem
    positiveP506MatterCurrentFullSynchronizedCoframeAction_path_hasDerivAt
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        positiveP506MatterCurrentFullSynchronizedCoframeActionDensity
          ((1 : LorentzianCoframe) + parameter • variation))
      0 0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedCoframeActionDensity_function_eq]
  exact
    positiveP506MatterCurrentFullGeneratedCoframeAction_path_hasDerivAt
      variation

/-- Full coframe producer consistency on the same final `U*` contact.  The
preceding contact theorem is what makes this a same-actual statement rather
than transport from an obsolete endpoint. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframeEuler_origin
    (variation : LorentzianCoframe) :
    HasDerivAt
      (fun parameter : ℝ =>
        positiveP506MatterCurrentFullSynchronizedCoframeActionDensity
          (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
              0 +
            parameter • variation))
      0 0 := by
  simpa only [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframe_one]
    using
      positiveP506MatterCurrentFullSynchronizedCoframeAction_path_hasDerivAt
        variation

/-! ## Exact dependency transport to current constraints -/

private theorem final_coframe_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.1

private theorem final_gaugeConnection_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeConnection =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.1

private theorem final_scalar_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.scalar =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.1

private theorem final_matter_origin_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.matter 0 := by
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter 0 =
        positiveP506MatterCurrentMatterResponseLocalActualLift.matter 0 := rfl
    _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.matter 0 :=
      positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin
    _ = positiveP506MatterCurrentCompleteBaseActual.matter 0 := rfl
    _ = positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.matter 0 :=
      congrFun
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.1
        0

private theorem final_conjugate_origin_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
        0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.conjugateMatter
        0 := by
  calc
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
          0 =
        positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter
          0 := rfl
    _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
          0 :=
      positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin
    _ = positiveP506MatterCurrentCompleteBaseActual.conjugateMatter 0 := rfl
    _ =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.conjugateMatter
          0 :=
      congrFun
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.2
        0

private theorem final_gaugeAuxiliary_origin_eq_U7 :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
        0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0 :=
  positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeAuxiliary_origin

private theorem final_scalarCovariantDerivative_eq_U7 :
    holonomicScalarCovariantDerivative
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      holonomicScalarCovariantDerivative
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [final_scalar_eq_U7, final_gaugeConnection_eq_U7]

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeCurvature_origin :
    holonomicGaugeCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
      holonomicGaugeCurvature
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0 := by
  unfold holonomicGaugeCurvature p286ConnectionDerivative
  rw [final_gaugeConnection_eq_U7]

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeCurvature_ne_zero :
    holonomicGaugeCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 ≠
      0 := by
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeCurvature_origin]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeCurvature_ne_zero

/-- P286 auxiliary producer consistency at the common final contact.  The
curvature was already generated from this auxiliary equation in the U7
action layer, so this readback is deliberately not counted as an independent
constraint. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286AuxiliaryEquation_origin :
    holonomicGaugeCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
              0))
        (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
          0) := by
  rw [
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeCurvature_origin,
    final_coframe_eq_U7, final_gaugeAuxiliary_origin_eq_U7]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_p286AuxiliaryEquation_origin

private theorem p286ActionCurrent_eq_of_contact
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe 0 = second.coframe 0)
    (gaugeConnectionEq : first.gaugeConnection 0 = second.gaugeConnection 0)
    (gaugeAuxiliaryEq : first.gaugeAuxiliary 0 = second.gaugeAuxiliary 0)
    (scalarEq : first.scalar 0 = second.scalar 0)
    (scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative first 0 =
        holonomicScalarCovariantDerivative second 0)
    (matterEq : first.matter 0 = second.matter 0)
    (conjugateEq : first.conjugateMatter 0 = second.conjugateMatter 0)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource first direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource second direction 0 := by
  have curvatureVariationEq :
      p286GaugeConnectionAlgebraicCurvatureDirection first direction 0 =
        p286GaugeConnectionAlgebraicCurvatureDirection second direction 0 := by
    unfold p286GaugeConnectionAlgebraicCurvatureDirection
      p286GaugeConnectionAlgebraicCurvatureVariation
      holonomicP286GaugeConnectionCoordinate
    rw [gaugeConnectionEq]
  have scalarVariationEq :
      holonomicScalarGaugeConnectionVariation first (fun _ => direction) 0 =
        holonomicScalarGaugeConnectionVariation second (fun _ => direction)
          0 := by
    unfold holonomicScalarGaugeConnectionVariation
    rw [scalarEq]
  have matterVariationEq :
      holonomicMatterGaugeConnectionVariation first (fun _ => direction) 0 =
        holonomicMatterGaugeConnectionVariation second (fun _ => direction)
          0 := by
    unfold holonomicMatterGaugeConnectionVariation
    rw [matterEq]
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity generatedVolumeDensity
    p286AuxiliaryCoordinate
    scalarGaugeConnectionKineticFirstVariationDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [curvatureVariationEq, scalarVariationEq, matterVariationEq]
  simp only [toContinuumPointField]
  rw [coframeEq, gaugeAuxiliaryEq, scalarCovariantDerivativeEq,
    conjugateEq]

private theorem final_p286ActionCurrent_eq_U8
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteBaseActual direction 0 := by
  apply p286ActionCurrent_eq_of_contact
  · rfl
  · rfl
  · rfl
  · rfl
  · funext formDirection
    rfl
  · calc
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.matter
            0 =
          positiveP506MatterCurrentMatterResponseLocalActualLift.matter 0 := rfl
      _ = positiveP506MatterCurrentLorentzResponseLocalActualLift.matter 0 :=
        positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin
      _ = positiveP506MatterCurrentCompleteBaseActual.matter 0 := rfl
  · calc
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.conjugateMatter
            0 =
          positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter
            0 := rfl
      _ =
          positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
            0 :=
        positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin
      _ = positiveP506MatterCurrentCompleteBaseActual.conjugateMatter 0 := rfl

/-- The final synchronized actual and its complete-P286 base read the same
P286 algebraic action current at the canonical contact.  This is a narrow
dependency readout: it uses only the seven fields consumed by that current,
not equality of the complete point fields. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286ActionCurrent_eq_completeBase
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteBaseActual direction 0 :=
  final_p286ActionCurrent_eq_U8 direction

private theorem final_p286Momentum_eq_U8
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction =
      p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterCurrentCompleteBaseActual direction := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  simp only [toContinuumPointField]
  rfl

private theorem final_p286Divergence_origin_eq_U8
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveP506MatterCurrentCompleteBaseActual direction 0 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [final_p286Momentum_eq_U8]

/-- C3h165 producer consistency survives on the same final actual because
the synchronized updates preserve its exact P286 dependencies. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286ConnectionEquation_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [final_p286ActionCurrent_eq_U8, final_p286Divergence_origin_eq_U8]
  exact
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_connectionEquation_origin
      direction

/-! ## Independent scalar equation on the same synchronized actual -/

private theorem final_scalarDifferentialMomentum_eq_U7
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [final_coframe_eq_U7, final_scalarCovariantDerivative_eq_U7]

private theorem final_scalarDifferentialMomentumDivergence_origin_eq_U7
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [final_scalarDifferentialMomentum_eq_U7]

private theorem final_scalarAlgebraic_origin_eq_U7
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0 := by
  unfold scalarAlgebraicDirectionalCoefficient generatedVolumeDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    scalarPotentialFirstVariation scalarYukawaFirstVariationDensity
    scalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [final_coframe_eq_U7, final_scalarCovariantDerivative_eq_U7,
    final_gaugeConnection_eq_U7, final_scalar_eq_U7,
    final_matter_origin_eq_U7, final_conjugate_origin_eq_U7]

private theorem final_scalarEuler_origin_eq_U7
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [final_scalarAlgebraic_origin_eq_U7,
    final_scalarDifferentialMomentumDivergence_origin_eq_U7]

/-- Independent current constraint: none of the Lorentz, matter, P286, or
coframe response constructors solved the scalar Euler--Lagrange equation.
Its exact dependencies are recomputed on the final `U*` contact before the
C3h164 source-generated scalar theorem is consumed. -/
theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_scalarEuler_origin
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
        direction 0 =
      0 := by
  calc
    _ =
        scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          direction 0 :=
      final_scalarEuler_origin_eq_U7 direction
    _ = 0 :=
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_scalarEuler_origin
        direction

/-! ## No-premise C3h166 synchronized producer law -/

/-- The dependency-ordered, no-parameter construction and every forward
readback of an equation used by that construction. -/
structure
    PositiveP506MatterCurrentFullSynchronizedResponseProducerSoundnessLaw :
    Prop where
  sourceGeneratedU8 :
    PositiveP506MatterCurrentP286CompleteResponseProducerSoundnessLaw
  exactP506L0Lineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  spinReadFromU8 :
    positiveP506MatterCurrentCompleteActualSpin =
      actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
        positiveP506MatterCurrentCompleteBaseActual 0
  contorsionActionResponse :
    simpleBEinsteinCartanGravityActionCoordinates
        positiveP506MatterCurrentCompleteActualContorsion =
      positiveP506MatterCurrentCompleteActualSpin
  contorsionActionResponseUnique :
    ∀ candidate : LorentzBivectorOneForm,
      simpleBEinsteinCartanGravityActionCoordinates candidate =
          positiveP506MatterCurrentCompleteActualSpin →
        candidate = positiveP506MatterCurrentCompleteActualContorsion
  matterOriginFaithful :
    positiveP506MatterCurrentMatterResponseLocalActualLift.matter 0 =
        positiveP506MatterCurrentLorentzResponseLocalActualLift.matter 0 ∧
      positiveP506MatterCurrentMatterResponseLocalActualLift.conjugateMatter
          0 =
        positiveP506MatterCurrentLorentzResponseLocalActualLift.conjugateMatter
          0
  matterTimeResponseUnique :
    ∀ candidate : DiracExteriorMatterCarrier,
      IdentityCoframeMatterTimeActionLaw
          positiveP506MatterCurrentLorentzResponseCauchyState 0 candidate →
        candidate =
          actionGeneratedMatterTimeCovariantDerivative
            positiveP506MatterCurrentLorentzResponseCauchyState 0
  conjugateMatterTimeResponseUnique :
    ∀ candidate : Module.Dual ℂ DiracExteriorMatterCarrier,
      IdentityCoframeConjugateMatterTimeActionLaw
          positiveP506MatterCurrentLorentzResponseCauchyState 0 candidate →
        candidate =
          actionGeneratedConjugateMatterTimeDerivative
            positiveP506MatterCurrentLorentzResponseCauchyState 0
  coframeStressReadFromCurrentMatter :
    positiveP506MatterCurrentFullNonGravityCoframeStress =
      coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
          positiveP506MatterCurrentMatterResponseOriginField +
        coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField +
        coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField
  coframeActionResponse :
    ∀ variation : LorentzianCoframe,
      linearPlebanskiCoframePrincipal
            positiveP506MatterCurrentFullCoframeResponse variation +
          gravityBFCoframeFeedback
            positiveP506MatterCurrentFullCoframeResponse variation +
          positiveP506MatterCurrentFullNonGravityCoframeStress variation =
        0
  coframeActionResponseUnique :
    ∀ candidate : LorentzianCoframe,
      linearPlebanskiCoframePrincipal candidate +
            gravityBFCoframeFeedback candidate +
            positiveP506MatterCurrentFullNonGravityCoframeStress =
          0 →
        candidate = positiveP506MatterCurrentFullCoframeResponse
  generatedActual :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift =
      { positiveP506MatterCurrentMatterResponseLocalActualLift with
        gravityConnection :=
          normalizedAffineLorentzConnectionField
            positiveP506MatterCurrentCompleteActionLorentzOrigin
            positiveP506MatterCurrentFullGravityCurvature
        gravitySimplicityMultiplier :=
          fun _ => positiveP506MatterCurrentFullGravityMultiplier }
  synchronizedSmooth :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.Smooth
  synchronizedNondegenerate :
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.Nondegenerate
  producerGravitySimplicityConsistency :
    GravitySimplicityEquation
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
  gaugeCurvatureNonzeroReadout :
    holonomicGaugeCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 ≠ 0
  sameActualCoframeDensity :
    positiveP506MatterCurrentFullSynchronizedCoframeActionDensity =
      positiveP506MatterCurrentFullGeneratedCoframeActionDensity
  producerGravityAuxiliaryConsistency :
    holonomicGravityCurvature
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 -
        gravityInternalDualEquiv
          (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravityAuxiliary
            0) +
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gravitySimplicityMultiplier
          0 =
      0
  producerLorentzConsistency :
    ∀ direction : LorentzBivectorOneForm,
      lorentzConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
        0
  producerPrimalMatterConsistency :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0) =
      0
  producerAdjointMatterConsistency :
    ∀ direction : MatterCoordinateCarrier,
      matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
        0
  producerCoframeConsistency :
    ∀ variation : LorentzianCoframe,
      HasDerivAt
        (fun parameter : ℝ =>
          positiveP506MatterCurrentFullSynchronizedCoframeActionDensity
            (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
                0 +
              parameter • variation))
        0 0
  producerP286AuxiliaryConsistency :
    holonomicGaugeCurvature
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.coframe
              0))
        (positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift.gaugeAuxiliary
          0)
  producerP286ConnectionConsistency :
    ∀ direction : P286GaugeOneForm,
      p286GaugeConnectionEulerLagrangeCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
        0

/-- The full C3h166 checkpoint keeps the genuinely independent scalar
constraint in a separate field from constructor soundness. -/
structure PositiveP506MatterCurrentFullSynchronizedResponseLocalActualLaw :
    Prop where
  producerSoundness :
    PositiveP506MatterCurrentFullSynchronizedResponseProducerSoundnessLaw
  independentScalarConstraint :
    ∀ direction : ScalarCoordinateCarrier,
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift
          direction 0 =
        0

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_producerSoundness :
    PositiveP506MatterCurrentFullSynchronizedResponseProducerSoundnessLaw := by
  exact
    { sourceGeneratedU8 :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_realizes_C3h165
      exactP506L0Lineage :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_realizes_C3h165.sourceGeneratedU7.exactP506L0Lineage
      spinReadFromU8 := rfl
      contorsionActionResponse :=
        positiveP506MatterCurrentCompleteActualContorsion_response
      contorsionActionResponseUnique := fun candidate response =>
        positiveP506MatterCurrentCompleteActualContorsion_unique
          candidate response
      matterOriginFaithful :=
        ⟨positiveP506MatterCurrentMatterResponseLocalActualLift_matter_origin,
          positiveP506MatterCurrentMatterResponseLocalActualLift_conjugate_origin⟩
      matterTimeResponseUnique := fun candidate response =>
        positiveP506MatterCurrentMatterTimeResponse_unique candidate response
      conjugateMatterTimeResponseUnique := fun candidate response =>
        positiveP506MatterCurrentConjugateMatterTimeResponse_unique
          candidate response
      coframeStressReadFromCurrentMatter := rfl
      coframeActionResponse :=
        positiveP506MatterCurrentFullCoframeResponse_actionBalance
      coframeActionResponseUnique := fun candidate response =>
        positiveP506MatterCurrentFullCoframeResponse_unique candidate response
      generatedActual := rfl
      synchronizedSmooth :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_smooth
      synchronizedNondegenerate :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_nondegenerate
      producerGravitySimplicityConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_simplicity
      gaugeCurvatureNonzeroReadout :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeCurvature_ne_zero
      sameActualCoframeDensity :=
        positiveP506MatterCurrentFullSynchronizedCoframeActionDensity_function_eq
      producerGravityAuxiliaryConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_auxiliaryBalance
      producerLorentzConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_lorentzEuler_origin
      producerPrimalMatterConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_diracYukawa_origin
      producerAdjointMatterConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_matterEuler_origin
      producerCoframeConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_coframeEuler_origin
      producerP286AuxiliaryConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286AuxiliaryEquation_origin
      producerP286ConnectionConsistency :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_p286ConnectionEquation_origin }

theorem
    positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_realizes_C3h166 :
    PositiveP506MatterCurrentFullSynchronizedResponseLocalActualLaw := by
  exact
    { producerSoundness :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_producerSoundness
      independentScalarConstraint :=
        positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_scalarEuler_origin }

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
