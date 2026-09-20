import H0mework.Physics.Coframe.CoframeSectorStress
import H0mework.Physics.Matter.ConjugateMatterActionTimeVelocity
import H0mework.Physics.Dirac.EinsteinCartanSpinContorsionAction
import H0mework.Physics.Coframe.LinearPlebanskiGravityCoupledCoframeActionResponse
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# Stage-9 full synchronized action-response operator

This dependency-light module extracts the action graph used concretely by
C3h166 into a reusable operator:

```text
(source, current actual)
→ actual spin
→ unique Einstein--Cartan contorsion and Lorentz origin
→ current-state primal/adjoint matter germs
→ complete non-gravity coframe stress
→ unique coframe response
→ generated multiplier and curvature
→ one full synchronized local actual.
```

The operator is total, but accepts only `source` and `current`.  It has no
slot for a response, residual, endpoint, stress, curvature target,
multiplier, inverse, range witness, coefficient, branch choice, boundary
constant, stationarity receipt, or equation certificate.  Domain-specific
facts such as identity coframe, simple B, smoothness, exact lineage, and
independent constraints belong to specialization theorems, not to this
constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFullSynchronizedActionResponseOperator

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeSectorStress
open StageNineConjugateMatterActionTimeVelocity
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

/-! ## Dependency-ordered constructor -/

def fullSynchronizedActionSpin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    LorentzBivectorOneForm :=
  actualMatterSpinActionCoordinates source current 0

def fullSynchronizedActionContorsion
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    LorentzBivectorOneForm :=
  einsteinCartanSpinContorsionCoordinates
    (fullSynchronizedActionSpin source current)

def fullSynchronizedActionLorentzOrigin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    PointwiseLorentzSpinConnection :=
  lorentzSkewConnectionOfBivectorOneForm
    (fullSynchronizedActionContorsion source current)

/-- First update the action-generated Lorentz origin while preserving the
current derived gravity curvature at the distinguished contact. -/
def fullSynchronizedActionLorentzActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gravityConnection :=
      normalizedAffineLorentzConnectionField
        (fullSynchronizedActionLorentzOrigin source current)
        (holonomicGravityCurvature current 0) }

def fullSynchronizedActionMatterCauchyState
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineCauchyState :=
  canonicalCauchyRestriction 0
    (fullSynchronizedActionLorentzActual source current)

/-- Resynchronize only primal and adjoint matter germs from the current
Lorentz-updated state. -/
def fullSynchronizedActionMatterActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { fullSynchronizedActionLorentzActual source current with
    matter :=
      actionGeneratedMatterLocalField
        (fullSynchronizedActionMatterCauchyState source current) 0
    conjugateMatter :=
      actionGeneratedConjugateMatterLocalField
        (fullSynchronizedActionMatterCauchyState source current) 0 }

def fullSynchronizedActionMatterOriginField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineContinuumPointField :=
  toContinuumPointField
    (fullSynchronizedActionMatterActual source current) 0

/-- The stress is read forward from the already resynchronized actual. -/
def fullSynchronizedActionNonGravityCoframeStress
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    LorentzianCoframe →L[ℝ] ℝ :=
  coframeGaugeSectorStressCovector source
      (fullSynchronizedActionMatterOriginField source current) +
    coframeScalarSectorStressCovector source 0
      (fullSynchronizedActionMatterOriginField source current) +
    coframeMatterSectorStressCovector source 0
      (fullSynchronizedActionMatterOriginField source current)

def fullSynchronizedActionCoframeResponse
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    LorentzianCoframe :=
  gravityCoupledLinearPlebanskiCoframeResponseOfStress
    (fullSynchronizedActionNonGravityCoframeStress source current)

def fullSynchronizedActionGravityMultiplier
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    PhysicalBivector :=
  gravityCoupledLinearPlebanskiMultiplier
    (fullSynchronizedActionCoframeResponse source current)

def fullSynchronizedActionGravityCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    PhysicalBivector :=
  gravityCoupledLinearPlebanskiCurvature
    (fullSynchronizedActionCoframeResponse source current)

/-- The complete synchronized action response.  Its body follows only the
forward dependency graph above. -/
def fullSynchronizedActionResponseOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { fullSynchronizedActionMatterActual source current with
    gravityConnection :=
      normalizedAffineLorentzConnectionField
        (fullSynchronizedActionLorentzOrigin source current)
        (fullSynchronizedActionGravityCurvature source current)
    gravitySimplicityMultiplier :=
      fun _ => fullSynchronizedActionGravityMultiplier source current }

/-! ## Canonical response uniqueness -/

theorem fullSynchronizedActionContorsion_response
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    simpleBEinsteinCartanGravityActionCoordinates
        (fullSynchronizedActionContorsion source current) =
      fullSynchronizedActionSpin source current :=
  simpleBGravityAction_contorsion _

theorem fullSynchronizedActionContorsion_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : LorentzBivectorOneForm)
    (response :
      simpleBEinsteinCartanGravityActionCoordinates candidate =
        fullSynchronizedActionSpin source current) :
    candidate = fullSynchronizedActionContorsion source current := by
  rw [← contorsion_simpleBGravityAction candidate, response]
  rfl

theorem fullSynchronizedActionMatterTimeResponse_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : DiracExteriorMatterCarrier)
    (response :
      IdentityCoframeMatterTimeActionLaw
        (fullSynchronizedActionMatterCauchyState source current) 0
        candidate) :
    candidate =
      actionGeneratedMatterTimeCovariantDerivative
        (fullSynchronizedActionMatterCauchyState source current) 0 := by
  exact
    identityCoframeMatterTimeActionLaw_unique
      (fullSynchronizedActionMatterCauchyState source current) 0 candidate _
      response
      (actionGeneratedMatterTimeCovariantDerivative_satisfies_actionLaw _ _)

theorem fullSynchronizedActionConjugateMatterTimeResponse_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : Module.Dual ℂ DiracExteriorMatterCarrier)
    (response :
      IdentityCoframeConjugateMatterTimeActionLaw
        (fullSynchronizedActionMatterCauchyState source current) 0
        candidate) :
    candidate =
      actionGeneratedConjugateMatterTimeDerivative
        (fullSynchronizedActionMatterCauchyState source current) 0 := by
  exact
    identityCoframeConjugateMatterTimeActionLaw_unique
      (fullSynchronizedActionMatterCauchyState source current) 0 candidate _
      response
      (actionGeneratedConjugateMatterTimeDerivative_satisfies_actionLaw _ _)

theorem fullSynchronizedActionCoframeResponse_actionBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : LorentzianCoframe) :
    linearPlebanskiCoframePrincipal
          (fullSynchronizedActionCoframeResponse source current) variation +
        gravityBFCoframeFeedback
          (fullSynchronizedActionCoframeResponse source current) variation +
        fullSynchronizedActionNonGravityCoframeStress source current
          variation =
      0 :=
  gravityCoupledLinearPlebanskiCoframeResponse_actionBalance_apply _ _

theorem fullSynchronizedActionCoframeResponse_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : LorentzianCoframe)
    (response :
      linearPlebanskiCoframePrincipal candidate +
          gravityBFCoframeFeedback candidate +
          fullSynchronizedActionNonGravityCoframeStress source current =
        0) :
    candidate = fullSynchronizedActionCoframeResponse source current :=
  gravityCoupledLinearPlebanskiCoframeResponse_unique _ candidate response

/-! ## Exact field responsibility of the generated actual -/

@[simp] theorem fullSynchronizedActionResponseOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem fullSynchronizedActionResponseOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).gravityAuxiliary =
      current.gravityAuxiliary :=
  rfl

@[simp] theorem fullSynchronizedActionResponseOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).gaugeConnection =
      current.gaugeConnection :=
  rfl

@[simp] theorem fullSynchronizedActionResponseOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).gaugeAuxiliary =
      current.gaugeAuxiliary :=
  rfl

@[simp] theorem fullSynchronizedActionResponseOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).scalar =
      current.scalar :=
  rfl

/-- The canonical affine matter germ is anchored at the current matter value.
This is origin fidelity only; its first jet is generated by the action. -/
theorem fullSynchronizedActionResponseOperator_preserves_matter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).matter 0 =
      current.matter 0 := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint,
        StageNineP286ActionCauchySplit.canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  change actionGeneratedMatterLocalField
      (fullSynchronizedActionMatterCauchyState source current) 0 0 = _
  rw [actionGeneratedMatterLocalField_origin]
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual source current).matter
        (canonicalCauchySlicePoint 0 0) = current.matter 0
  rw [contactZero]
  rfl

/-- The adjoint affine germ has the same canonical-origin anchor fidelity. -/
theorem fullSynchronizedActionResponseOperator_preserves_conjugateMatter_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).conjugateMatter 0 =
      current.conjugateMatter 0 := by
  have contactZero : canonicalCauchySlicePoint 0 0 = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint,
        StageNineP286ActionCauchySplit.canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  change actionGeneratedConjugateMatterLocalField
      (fullSynchronizedActionMatterCauchyState source current) 0 0 = _
  rw [actionGeneratedConjugateMatterLocalField_origin]
  unfold fullSynchronizedActionMatterCauchyState canonicalCauchyRestriction
  change
    (fullSynchronizedActionLorentzActual source current).conjugateMatter
        (canonicalCauchySlicePoint 0 0) = current.conjugateMatter 0
  rw [contactZero]
  rfl

/-- The dependency-ordered response preserves smoothness.  Every unchanged
sector reuses the current proof; the regenerated Lorentz field is normalized
affine, the multiplier is constant, and the matter/adjoint germs are the
canonical affine action germs. -/
theorem fullSynchronizedActionResponseOperator_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (fullSynchronizedActionResponseOperator source current).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, _gravityConnectionSmooth, gravityAuxiliarySmooth,
      _multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, _conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, normalizedAffineLorentzConnectionField_smooth _ _,
      gravityAuxiliarySmooth,
      by
        intro internalPair spacetimePair
        change ContDiff ℝ ∞
          (fun _ : BasePoint =>
            fullSynchronizedActionGravityMultiplier source current
              internalPair spacetimePair)
        fun_prop,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      actionGeneratedMatterLocalField_smooth
        (fullSynchronizedActionMatterCauchyState source current) 0,
      fun index =>
        actionGeneratedConjugateMatterLocalField_smooth
          (fullSynchronizedActionMatterCauchyState source current) 0 index⟩

/-- Nondegeneracy is inherited because the full response leaves the current
coframe field unchanged. -/
theorem fullSynchronizedActionResponseOperator_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (fullSynchronizedActionResponseOperator source current).Nondegenerate := by
  intro point
  change Matrix.det (current.coframe point) ≠ 0
  exact nondegenerate point

theorem fullSynchronizedActionResponseOperator_connection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (fullSynchronizedActionResponseOperator source current).gravityConnection
        0 =
      fullSynchronizedActionLorentzOrigin source current :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem fullSynchronizedActionResponseOperator_curvature_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (fullSynchronizedActionResponseOperator source current) 0 =
      fullSynchronizedActionGravityCurvature source current := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          (fullSynchronizedActionLorentzOrigin source current)
          (fullSynchronizedActionGravityCurvature source current)) 0 =
      fullSynchronizedActionGravityCurvature source current
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

end

end
  SaturationMonoid.PhysicsCore.StageNineFullSynchronizedActionResponseOperator
