import H0mework.Physics.MatterCurrent.P286NonzeroCurvatureSynchronizedLocalActualLift

/-!
# S9-C3h165: complete current-action P286 response on the nonzero-curvature actual

C3h163 first produces the synchronized nonzero-curvature actual `U₇`.  This
module then resumes the path-first/action-first construction:

```text
exact P506/L0 source
→ current source/action-generated U₇ with Fₐ(0) ≠ 0
→ the complete P286 connection-action dual J₇ on U₇
→ its spatial and temporal restrictions
→ unique BF-Legendre velocity V₇ and unique Lie-pairing charge Q₇
→ B₈(x) = B₇(0) + x⁰ embed(V₇) + radial(Q₇,x)
→ one synchronized nine-field local actual U₈.
```

The constructor accepts no residual, endpoint, auxiliary value, first jet,
velocity, charge, coefficient, source knob, branch choice, or stationarity
receipt.  In particular it does not translate the old `U₆` response and it
does not reconstruct fields from a residual coordinate.

The final connection equation theorem is deliberately classified as
**producer soundness / consistency**: `V₇` and `Q₇` are defined by the same
action equation that is checked after installation.  Its nontrivial content
is the action provenance, invertible principal symbols, response uniqueness,
parameter-free actual realization, and full-direction forward momentum
calculation.  It is not counted as an independent Stage-9 constraint closure.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget : Module.Dual ℝ P286GaugeOneForm where
  toFun direction :=
    p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      direction 0
  map_add' := by
    intro first second
    exact p286GaugeConnectionAlgebraicCurrentCoefficient_add_action
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      first second 0
  map_smul' := by
    intro parameter direction
    rw [p286GaugeConnectionAlgebraicCurrentCoefficient_smul_action]
    rfl

private theorem spatial_add
    (first second : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (first + second) =
      canonicalP286SpatialGaugeOneForm first +
        canonicalP286SpatialGaugeOneForm second := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.add_apply]

private theorem spatial_smul
    (parameter : ℝ) (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (parameter • direction) =
      parameter • canonicalP286SpatialGaugeOneForm direction := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.smul_apply]

def positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionInclusion :
    P286SpatialGaugeDirection →ₗ[ℝ] P286GaugeOneForm where
  toFun := canonicalP286SpatialGaugeOneForm
  map_add' := by
    intro first second
    exact spatial_add first second
  map_smul' := by
    intro parameter direction
    exact spatial_smul parameter direction

def positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget : Module.Dual ℝ P286SpatialGaugeDirection :=
  positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget.comp positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionInclusion

private theorem temporal_add
    (first second : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (first + second) =
      p286TemporalGaugeOneForm first + p286TemporalGaugeOneForm second := by
  funext direction
  by_cases isTime : direction = canonicalLorentzianTimeDirection
  · simp [p286TemporalGaugeOneForm, isTime]
  · simp [p286TemporalGaugeOneForm, isTime]

private theorem temporal_smul
    (parameter : ℝ) (component : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (parameter • component) =
      parameter • p286TemporalGaugeOneForm component := by
  funext direction
  simp [p286TemporalGaugeOneForm, Pi.smul_apply]

def positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionInclusion : P286CoordinateCarrier →ₗ[ℝ] P286GaugeOneForm where
  toFun := p286TemporalGaugeOneForm
  map_add' := by
    intro first second
    exact temporal_add first second
  map_smul' := by
    intro parameter component
    exact temporal_smul parameter component

def positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget : Module.Dual ℝ P286CoordinateCarrier :=
  positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget.comp positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionInclusion

@[simp] theorem positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget_apply (direction : P286SpatialGaugeDirection) :
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget direction =
      positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget (canonicalP286SpatialGaugeOneForm direction) :=
  rfl

@[simp] theorem positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget_apply (component : P286CoordinateCarrier) :
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget component = positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget (p286TemporalGaugeOneForm component) :=
  rfl

def positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity : P286SpatialGaugeDirection :=
  p286SpatialBFLegendreEquiv.symm positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget

theorem positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_response :
    p286SpatialBFLegendreDualOperator
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget := by
  exact p286SpatialBFLegendreEquiv.apply_symm_apply _

theorem
    positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_unique
    (candidate : P286SpatialGaugeDirection)
    (response :
      p286SpatialBFLegendreDualOperator candidate =
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget) :
    candidate =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity :=
  p286SpatialBFLegendreEquiv_unique _ candidate response

def positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge : P286CoordinateCarrier :=
  p286CoordinateLiePairingEquiv.symm positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget

theorem positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge component = positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget component := by
  change p286CoordinateLiePairingEquiv
      (p286CoordinateLiePairingEquiv.symm positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget) component =
    positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget component
  rw [p286CoordinateLiePairingEquiv.apply_symm_apply]

theorem positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_unique
    (candidate : P286CoordinateCarrier)
    (response : ∀ component,
      p286CoordinateLiePairing candidate component =
        positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
          component) :
    candidate = positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
  apply p286CoordinateLiePairingDualOperator_injective
  apply LinearMap.ext
  intro component
  rw [p286CoordinateLiePairingDualOperator_apply,
    p286CoordinateLiePairingDualOperator_apply,
    response,
    positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response]

def positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate : P286GaugeTwoForm := fun pair =>
  p286CoordinateEquiv
    (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
      0 pair)

def positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate (point : BasePoint) : P286GaugeTwoForm :=
  positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate +
    point canonicalLorentzianTimeDirection •
      p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity +
    p286GaussRadialAuxiliaryProfile positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge point

/-- Install a generated auxiliary germ without changing another field. -/
def installGeneratedGaugeAuxiliaryGerm
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    StageNineHolonomicConfiguration :=
  { base with gaugeAuxiliary := auxiliary }

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_gaugeAuxiliary
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).gaugeAuxiliary = auxiliary :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_coframe
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).coframe = base.coframe :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_gravityConnection
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).gravityConnection =
      base.gravityConnection :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_gravityAuxiliary
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).gravityAuxiliary =
      base.gravityAuxiliary :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_multiplier
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary
      |>.gravitySimplicityMultiplier) =
      base.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_gaugeConnection
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).gaugeConnection =
      base.gaugeConnection :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_scalar
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).scalar = base.scalar :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_matter
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).matter = base.matter :=
  rfl

@[simp] theorem installGeneratedGaugeAuxiliaryGerm_conjugateMatter
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData) :
    (installGeneratedGaugeAuxiliaryGerm base auxiliary).conjugateMatter =
      base.conjugateMatter :=
  rfl

def positiveP506MatterCurrentP286CompleteResponseAuxiliaryField : BasePoint → Fin 6 → P286LieBlockData :=
  fun point pair => p286CoordinateEquiv.symm (positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point pair)

def positiveP506MatterCurrentP286CompleteResponseLocalActualLift : StageNineHolonomicConfiguration :=
  installGeneratedGaugeAuxiliaryGerm
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryField

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeConnection :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeConnection =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift,
    installGeneratedGaugeAuxiliaryGerm_gaugeConnection]

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.coframe =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gravityConnection =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravityConnection ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gravityAuxiliary =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravityAuxiliary ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gravitySimplicityMultiplier =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravitySimplicityMultiplier ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeConnection =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.scalar =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.matter =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.matter ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.conjugateMatter =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.conjugateMatter := by
  simp [positiveP506MatterCurrentP286CompleteResponseLocalActualLift]

@[simp] theorem positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_origin : positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate 0 = positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate := by
  simp [positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate]

theorem positiveP506MatterCurrentP286CompleteResponseAuxiliaryField_origin :
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryField 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [positiveP506MatterCurrentP286CompleteResponseAuxiliaryField, positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate]

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeAuxiliary_origin :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeAuxiliary 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0 := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm_gaugeAuxiliary]
  exact positiveP506MatterCurrentP286CompleteResponseAuxiliaryField_origin

theorem positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_contDiff (pair : Fin 6) :
    ContDiff ℝ ∞ fun point : BasePoint => positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point pair := by
  have originSmooth : ContDiff ℝ ∞ fun _ : BasePoint => positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate pair :=
    contDiff_const
  have timeSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      point canonicalLorentzianTimeDirection •
        p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity pair := by
    simpa only [localBaseCoordinate_apply] using
      ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff
        |>.smul_const (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity pair))
  have radialSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      p286GaussRadialAuxiliaryProfile positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge point pair :=
    p286GaussRadialAuxiliaryProfile_contDiff positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge pair
  change ContDiff ℝ ∞ fun point : BasePoint =>
    (positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate +
      point canonicalLorentzianTimeDirection •
        p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity +
      p286GaussRadialAuxiliaryProfile positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge point) pair
  simpa only [Pi.add_apply, Pi.smul_apply] using
    ((originSmooth.add timeSmooth).add radialSmooth)

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_smooth : positiveP506MatterCurrentP286CompleteResponseLocalActualLift.Smooth := by
  rcases positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using coframe
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using gravityConnection
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using gravityAuxiliary
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using multiplier
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using gaugeConnection
  · intro pair
    change ContDiff ℝ ∞ fun point : BasePoint =>
      p286CoordinateEquiv (positiveP506MatterCurrentP286CompleteResponseAuxiliaryField point pair)
    rw [show (fun point : BasePoint =>
      p286CoordinateEquiv (positiveP506MatterCurrentP286CompleteResponseAuxiliaryField point pair)) =
        (fun point : BasePoint => positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point pair) by
      funext point
      exact p286CoordinateEquiv.apply_symm_apply _]
    exact positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_contDiff pair
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using scalar
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using matter
  · simpa only [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm] using conjugate

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_coframe_one (point : BasePoint) :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.coframe point = 1 := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm_coframe]
  change
    positiveP506MatterCurrentP286GaussCauchyState.coframe
        positiveP506MatterCurrentP286AxisContact = 1
  exact positiveP506MatterCurrentP286GaussCauchyState_coframe_axis

theorem installGeneratedGaugeAuxiliaryGerm_pointField_eq_of_contact
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint)
    (contact : auxiliary point = base.gaugeAuxiliary point) :
    toContinuumPointField (installGeneratedGaugeAuxiliaryGerm base auxiliary) point =
      toContinuumPointField base point := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact contact
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_pointField_origin :
    toContinuumPointField positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 =
      toContinuumPointField
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0 := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift]
  exact installGeneratedGaugeAuxiliaryGerm_pointField_eq_of_contact _ _ 0
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryField_origin

theorem installGeneratedGaugeAuxiliaryGerm_actionCurrent_eq_of_contact
    (source : SmoothUnifiedSource)
    (base : StageNineHolonomicConfiguration)
    (auxiliary : BasePoint → Fin 6 → P286LieBlockData)
    (point : BasePoint)
    (contact : auxiliary point = base.gaugeAuxiliary point)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (installGeneratedGaugeAuxiliaryGerm base auxiliary) direction point =
      p286GaugeConnectionAlgebraicCurrentCoefficient source base direction
        point := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [installGeneratedGaugeAuxiliaryGerm_pointField_eq_of_contact
    base auxiliary point contact]
  rfl

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_actionCurrent_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget direction := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift]
  exact installGeneratedGaugeAuxiliaryGerm_actionCurrent_eq_of_contact
    positiveSmoothUnifiedSource _ _ 0 positiveP506MatterCurrentP286CompleteResponseAuxiliaryField_origin direction

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_nondegenerate : positiveP506MatterCurrentP286CompleteResponseLocalActualLift.Nondegenerate := by
  intro point
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm_coframe]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_nondegenerate
      point

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeCurvature_origin :
    holonomicGaugeCurvature
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 =
      holonomicGaugeCurvature
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift 0 := by
  exact holonomicGaugeCurvature_eq_of_connection_eq_current _ _
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeConnection
    0

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeCurvature_ne_zero :
    holonomicGaugeCurvature
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 ≠ 0 := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeCurvature_origin]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeCurvature_ne_zero

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeConnection_ne_zero :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeConnection ≠
      0 := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeConnection]
  exact
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeConnection_ne_zero

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_auxiliaryCoordinate (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate positiveP506MatterCurrentP286CompleteResponseLocalActualLift point = positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point := by
  funext pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift, installGeneratedGaugeAuxiliaryGerm_gaugeAuxiliary]
  exact p286CoordinateEquiv.apply_symm_apply _

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_normalForm
    (direction : P286GaugeTwoForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction point =
      p286GaugeAuxiliaryHodgePairingPolynomial 1 (positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point)
        direction := by
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
  rw [show (toContinuumPointField positiveP506MatterCurrentP286CompleteResponseLocalActualLift point).coframe = 1 by
    exact positiveP506MatterCurrentP286CompleteResponseLocalActualLift_coframe_one point]
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_coframe_one, positiveP506MatterCurrentP286CompleteResponseLocalActualLift_auxiliaryCoordinate]
  simp

private theorem hodgePairing_add_left
    (first second test : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1 (first + second) test =
      p286GaugeAuxiliaryHodgePairingPolynomial 1 first test +
        p286GaugeAuxiliaryHodgePairingPolynomial 1 second test := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_add_p286]
  simp_rw [Pi.add_apply, p286CoordinateLiePairing_add_left]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

private theorem hodgePairing_smul_left
    (parameter : ℝ) (first test : P286GaugeTwoForm) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1 (parameter • first)
        test =
      parameter *
        p286GaugeAuxiliaryHodgePairingPolynomial 1 first test := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [liftGaugeTwoFormOperator_smul_p286]
  simp_rw [Pi.smul_apply, p286CoordinateLiePairing_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

private def hodgePairingLinear (test : P286GaugeTwoForm) :
    P286GaugeTwoForm →ₗ[ℝ] ℝ where
  toFun first := p286GaugeAuxiliaryHodgePairingPolynomial 1 first test
  map_add' := fun first second => hodgePairing_add_left first second test
  map_smul' := by
    intro parameter first
    simpa [smul_eq_mul] using
      hodgePairing_smul_left parameter first test

@[simp] private theorem hodgePairingLinear_apply
    (test first : P286GaugeTwoForm) :
    hodgePairingLinear test first =
      p286GaugeAuxiliaryHodgePairingPolynomial 1 first test :=
  rfl

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_affineNormalForm
    (direction : P286GaugeTwoForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentum positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction point =
      p286GaugeAuxiliaryHodgePairingPolynomial 1 positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate direction +
        point canonicalLorentzianTimeDirection *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) direction +
        ∑ axis : Fin 3,
          ((1 / 3 : ℝ) * point axis.succ) *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis) direction := by
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_normalForm]
  change hodgePairingLinear direction (positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate point) = _
  rw [positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate, map_add, map_add, map_smul,
    p286GaussRadialAuxiliaryProfile, map_sum]
  simp only [map_smul, smul_eq_mul, hodgePairingLinear_apply]

private theorem fieldDirectionalDerivative_add_real
    (first second : BasePoint → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (first + second) 0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  change
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction = _
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) 0)
    (secondSmooth.differentiable (by simp) 0)]
  rfl

private theorem fieldDirectionalDerivative_finset_sum_real
    {Index : Type*} [Fintype Index]
    (field : Index → BasePoint → ℝ)
    (fieldSmooth : ∀ index, ContDiff ℝ ∞ (field index))
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => ∑ index, field index point)
        0 direction =
      ∑ index, fieldDirectionalDerivative (field index) 0 direction := by
  have sumDerivative :
      HasFDerivAt
        (∑ index, field index)
        (∑ index, fderiv ℝ (field index) 0) 0 :=
    HasFDerivAt.sum (u := Finset.univ) fun index _ =>
      ((fieldSmooth index).differentiable (by simp)).differentiableAt
        |>.hasFDerivAt
  have sumDerivativePointwise :
      HasFDerivAt
        (fun point => ∑ index, field index point)
        (∑ index, fderiv ℝ (field index) 0) 0 := by
    convert sumDerivative using 1
    funext point
    simp
  unfold fieldDirectionalDerivative
  rw [sumDerivativePointwise.fderiv]
  simp

private theorem fieldDirectionalDerivative_coordinate_mul_constant
    (coordinate direction : LorentzianIndex) (coefficient : ℝ) :
    fieldDirectionalDerivative
        (fun point : BasePoint => point coordinate * coefficient)
        0 direction =
      if coordinate = direction then coefficient else 0 := by
  let coordinateField := localBaseCoordinate coordinate
  have coordinateDifferentiable :
      DifferentiableAt ℝ coordinateField 0 :=
    coordinateField.differentiable.differentiableAt
  have coefficientDifferentiable :
      DifferentiableAt ℝ (fun _ : BasePoint => coefficient) 0 :=
    differentiableAt_const coefficient
  unfold fieldDirectionalDerivative
  change
    fderiv ℝ (fun point => coordinateField point * coefficient) 0
        (coordinateDirection direction) = _
  rw [fderiv_fun_mul coordinateDifferentiable coefficientDifferentiable,
    coordinateField.hasFDerivAt.fderiv]
  by_cases sameDirection : coordinate = direction
  · subst direction
    simp [coordinateField, localBaseCoordinate, coordinateDirection]
  · simp [coordinateField, localBaseCoordinate, coordinateDirection,
      sameDirection]

private theorem fieldDirectionalDerivative_spatialCoordinate_mul_constant
    (coefficient : ℝ) (axis : Fin 3)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point : BasePoint =>
          ((1 / 3 : ℝ) * point axis.succ) * coefficient)
        0 direction =
      if axis.succ = direction then (1 / 3 : ℝ) * coefficient else 0 := by
  rw [show (fun point : BasePoint =>
      ((1 / 3 : ℝ) * point axis.succ) * coefficient) =
      (fun point : BasePoint =>
        point axis.succ * ((1 / 3 : ℝ) * coefficient)) by
    funext point
    ring]
  exact fieldDirectionalDerivative_coordinate_mul_constant
    axis.succ direction ((1 / 3 : ℝ) * coefficient)

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_derivative
    (direction : P286GaugeTwoForm)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (p286GaugeConnectionBFDifferentialMomentum positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction)
        0 derivativeDirection =
      (if canonicalLorentzianTimeDirection = derivativeDirection then
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) direction
      else 0) +
        ∑ axis : Fin 3,
          if axis.succ = derivativeDirection then
            (1 / 3 : ℝ) *
              p286GaugeAuxiliaryHodgePairingPolynomial 1
                (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis) direction
          else 0 := by
  let baseField : BasePoint → ℝ := fun point =>
    p286GaugeAuxiliaryHodgePairingPolynomial 1 positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate direction +
      point canonicalLorentzianTimeDirection *
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) direction
  let radialField : BasePoint → ℝ := fun point =>
    ∑ axis : Fin 3,
      ((1 / 3 : ℝ) * point axis.succ) *
        p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis) direction
  have momentumEquality :
      p286GaugeConnectionBFDifferentialMomentum positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction =
        baseField + radialField := by
    funext point
    exact positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_affineNormalForm direction point
  have baseSmooth : ContDiff ℝ ∞ baseField := by
    dsimp [baseField]
    fun_prop
  have radialSummandSmooth (axis : Fin 3) :
      ContDiff ℝ ∞ fun point : BasePoint =>
        ((1 / 3 : ℝ) * point axis.succ) *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis) direction := by
    fun_prop
  have radialSmooth : ContDiff ℝ ∞ radialField := by
    dsimp [radialField]
    apply ContDiff.sum
    intro axis _
    exact radialSummandSmooth axis
  rw [momentumEquality,
    fieldDirectionalDerivative_add_real baseField radialField baseSmooth
      radialSmooth derivativeDirection]
  have baseDerivative :
      fieldDirectionalDerivative baseField 0 derivativeDirection =
        if canonicalLorentzianTimeDirection = derivativeDirection then
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) direction
        else 0 := by
    dsimp [baseField]
    rw [show (fun point : BasePoint =>
        p286GaugeAuxiliaryHodgePairingPolynomial 1 positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate direction +
          point canonicalLorentzianTimeDirection *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) direction) =
        (fun _ : BasePoint =>
          p286GaugeAuxiliaryHodgePairingPolynomial 1 positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate direction) +
        (fun point : BasePoint =>
          point canonicalLorentzianTimeDirection *
            p286GaugeAuxiliaryHodgePairingPolynomial 1
              (p286SpatialAuxiliaryVelocityEmbedding positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) direction) by
      rfl]
    rw [fieldDirectionalDerivative_add_real _ _ contDiff_const (by fun_prop)]
    rw [show fieldDirectionalDerivative
        (fun _ : BasePoint =>
          p286GaugeAuxiliaryHodgePairingPolynomial 1 positiveP506MatterCurrentP286NonzeroCurvatureOriginAuxiliaryCoordinate direction)
        0 derivativeDirection = 0 by
      simp [fieldDirectionalDerivative]]
    rw [fieldDirectionalDerivative_coordinate_mul_constant]
    simp
  rw [baseDerivative]
  apply congrArg₂ (fun first second : ℝ => first + second) rfl
  dsimp [radialField]
  rw [fieldDirectionalDerivative_finset_sum_real _ radialSummandSmooth]
  apply Finset.sum_congr rfl
  intro axis _
  exact fieldDirectionalDerivative_spatialCoordinate_mul_constant
    _ axis derivativeDirection

private theorem liftGaugeTwoFormOperator_id_p286
    (form : P286GaugeTwoForm) :
    liftGaugeTwoFormOperator
        (LinearMap.id : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm) form = form := by
  funext pair
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> simp

private theorem liftGaugeTwoFormOperator_fixedHodge_apply
    (form : P286GaugeTwoForm) (pair : Fin 6) :
    liftGaugeTwoFormOperator lorentzianCoframeHodge form pair =
      ![form 3, form 4, form 5, -form 0, -form 1, -form 2] pair := by
  rw [WithLp.ext_iff]
  funext internal
  rw [liftGaugeTwoFormOperator_p286Coordinate_apply]
  fin_cases pair <;> rfl

private theorem p286TimeExterior_fullDirection
    (direction : P286GaugeOneForm) :
    p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        direction =
      p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        (canonicalP286SpatialGaugeOneForm (fun index => direction index.succ)) := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection, pairFirst, pairSecond]

private theorem p286TimeExteriorSpatialDirection_normalForm
    (direction : P286SpatialGaugeDirection) :
    p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        (canonicalP286SpatialGaugeOneForm direction) =
      ![direction 0, direction 1, direction 2, 0, 0, 0] := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection, pairFirst, pairSecond]

private theorem p286CoordinateLiePairing_neg_right
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

private theorem identityP286SpatialBFLegendre_normalForm
    (candidate direction : P286SpatialGaugeDirection) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286SpatialAuxiliaryVelocityEmbedding candidate)
        (p286GaugeExteriorDerivativeDirection
          canonicalLorentzianTimeDirection
          (canonicalP286SpatialGaugeOneForm direction)) =
      -(∑ index : Fin 3,
        p286CoordinateLiePairing (candidate index) (direction index)) := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286]
  rw [p286TimeExteriorSpatialDirection_normalForm,
    Fin.sum_univ_six, Fin.sum_univ_three]
  simp [p286SpatialAuxiliaryVelocityEmbedding,
    liftGaugeTwoFormOperator_fixedHodge_apply,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond, p286CoordinateLiePairing_neg_right]
  ring

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_temporalBFMomentumResponse
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionTemporalBFMomentumDerivative positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget (fun index => direction index.succ) := by
  unfold p286GaugeConnectionTemporalBFMomentumDerivative
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_derivative]
  rw [show (∑ axis : Fin 3,
      if axis.succ = canonicalLorentzianTimeDirection then
        (1 / 3 : ℝ) *
          p286GaugeAuxiliaryHodgePairingPolynomial 1
            (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge axis)
            (p286GaugeExteriorDerivativeDirection
              canonicalLorentzianTimeDirection direction)
      else 0) = 0 by
    rw [Fin.sum_univ_three]
    simp [canonicalLorentzianTimeDirection]]
  simp only [if_pos, add_zero]
  rw [p286TimeExterior_fullDirection,
    identityP286SpatialBFLegendre_normalForm]
  change
    p286SpatialBFLegendreDualOperator positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity
        (fun index => direction index.succ) =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget (fun index => direction index.succ)
  rw [positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_response]

private theorem identityP286GaussAxisMomentum_fullDirection
    (candidate : P286CoordinateCarrier)
    (direction : P286GaugeOneForm) (axis : Fin 3) :
    p286GaugeAuxiliaryHodgePairingPolynomial 1
        (p286GaussAuxiliaryAxisEmbedding candidate axis)
        (p286GaugeExteriorDerivativeDirection axis.succ direction) =
      p286CoordinateLiePairing candidate
        (direction canonicalLorentzianTimeDirection) := by
  unfold p286GaugeAuxiliaryHodgePairingPolynomial
  rw [coframeTwoFormLinear_one]
  simp_rw [liftGaugeTwoFormOperator_id_p286]
  rw [Fin.sum_univ_six]
  fin_cases axis <;>
    simp [p286GaussAuxiliaryAxisEmbedding,
      p286SpatialAuxiliaryVelocityEmbedding,
      p286GaugeExteriorDerivativeDirection,
      canonicalLorentzianTimeDirection,
      liftGaugeTwoFormOperator_fixedHodge_apply,
      lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond]

theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_spatialBFMomentumResponse
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionSpatialBFMomentumDivergence positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget (direction canonicalLorentzianTimeDirection) := by
  unfold p286GaugeConnectionSpatialBFMomentumDivergence
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_derivative
      (p286GaugeExteriorDerivativeDirection 1 direction) 1,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_derivative
      (p286GaugeExteriorDerivativeDirection 2 direction) 2,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_bfMomentum_derivative
      (p286GaugeExteriorDerivativeDirection 3 direction) 3]
  simp only [canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  simp
  rw [show
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge 0)
          (p286GaugeExteriorDerivativeDirection 1 direction) =
        p286CoordinateLiePairing positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge (direction 0) by
      simpa [canonicalLorentzianTimeDirection] using
        identityP286GaussAxisMomentum_fullDirection positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge direction 0,
    show
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge 1)
          (p286GaugeExteriorDerivativeDirection 2 direction) =
        p286CoordinateLiePairing positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge (direction 0) by
      simpa [canonicalLorentzianTimeDirection] using
        identityP286GaussAxisMomentum_fullDirection positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge direction 1,
    show
      p286GaugeAuxiliaryHodgePairingPolynomial 1
          (p286GaussAuxiliaryAxisEmbedding positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge 2)
          (p286GaugeExteriorDerivativeDirection 3 direction) =
        p286CoordinateLiePairing positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge (direction 0) by
      simpa [canonicalLorentzianTimeDirection] using
        identityP286GaussAxisMomentum_fullDirection positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge direction 2]
  calc
    _ = p286CoordinateLiePairing positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge (direction 0) := by ring
    _ = positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget (direction 0) := positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response (direction 0)

theorem p286GaugeOneForm_eq_temporal_add_canonicalSpatial
    (direction : P286GaugeOneForm) :
    direction =
      p286TemporalGaugeOneForm
          (direction canonicalLorentzianTimeDirection) +
        canonicalP286SpatialGaugeOneForm
          (fun index => direction index.succ) := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [p286TemporalGaugeOneForm,
      canonicalP286SpatialGaugeOneForm,
      canonicalLorentzianTimeDirection]
  · simp [p286TemporalGaugeOneForm,
      canonicalP286SpatialGaugeOneForm_spatial,
      canonicalLorentzianTimeDirection]

theorem positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget_decomposition
    (direction : P286GaugeOneForm) :
    positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget direction =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget (direction canonicalLorentzianTimeDirection) +
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget (fun index => direction index.succ) := by
  calc
    positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget direction =
        positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget
          (p286TemporalGaugeOneForm
              (direction canonicalLorentzianTimeDirection) +
            canonicalP286SpatialGaugeOneForm
              (fun index => direction index.succ)) :=
      congrArg positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget
        (p286GaugeOneForm_eq_temporal_add_canonicalSpatial direction)
    _ = positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget
          (p286TemporalGaugeOneForm
            (direction canonicalLorentzianTimeDirection)) +
        positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget
          (canonicalP286SpatialGaugeOneForm
            (fun index => direction index.succ)) := by
      rw [map_add]
    _ = _ := by
      rw [positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget_apply, positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget_apply]

/-- Producer-soundness check: the current full action dual uniquely generates
the complete auxiliary first jet, and substituting that forward response in
the same connection equation closes every one-form direction. -/
theorem positiveP506MatterCurrentP286CompleteResponseLocalActualLift_connectionEquation_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource positiveP506MatterCurrentP286CompleteResponseLocalActualLift direction 0 = 0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [positiveP506MatterCurrentP286CompleteResponseLocalActualLift_actionCurrent_origin,
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_temporalBFMomentumResponse,
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_spatialBFMomentumResponse,
    positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget_decomposition]
  ring

/-! ## No-premise C3h165 producer-soundness law -/

/-- C3h165 records the parameter-free producer and its forward consistency
check.  The connection equation field is intentionally not classified as an
independent constraint: it checks the equation that defined `V₇` and `Q₇`.
-/
structure PositiveP506MatterCurrentP286CompleteResponseProducerSoundnessLaw :
    Prop where
  sourceGeneratedU7 :
    PositiveP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLaw
  fullActionReadFromU7 : ∀ direction : P286GaugeOneForm,
    positiveP506MatterCurrentP286NonzeroCurvatureFullActionTarget direction =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        direction 0
  spatialResponse :
    p286SpatialBFLegendreDualOperator
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget
  spatialResponseUnique : ∀ candidate : P286SpatialGaugeDirection,
    p286SpatialBFLegendreDualOperator candidate =
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget →
      candidate =
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity
  temporalResponse : ∀ component : P286CoordinateCarrier,
    p286CoordinateLiePairing
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge component =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
        component
  temporalResponseUnique : ∀ candidate : P286CoordinateCarrier,
    (∀ component,
      p286CoordinateLiePairing candidate component =
        positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
          component) →
      candidate = positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge
  generatedActual :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift =
      installGeneratedGaugeAuxiliaryGerm
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        positiveP506MatterCurrentP286CompleteResponseAuxiliaryField
  originFaithful :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeAuxiliary
        0 =
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeAuxiliary
        0
  synchronizedSmooth :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.Smooth
  synchronizedNondegenerate :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.Nondegenerate
  retainsU7Fields :
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift.coframe =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.coframe ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gravityConnection =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravityConnection ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gravityAuxiliary =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravityAuxiliary ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gravitySimplicityMultiplier =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gravitySimplicityMultiplier ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeConnection =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.gaugeConnection ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.scalar =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.scalar ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.matter =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.matter ∧
      positiveP506MatterCurrentP286CompleteResponseLocalActualLift.conjugateMatter =
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift.conjugateMatter
  retainedCurvatureNonzero :
    holonomicGaugeCurvature
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift 0 ≠ 0
  completeTemporalMomentumResponse : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionTemporalBFMomentumDerivative
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift
        direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureSpatialActionTarget
        (fun index => direction index.succ)
  completeSpatialMomentumResponse : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionSpatialBFMomentumDivergence
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift
        direction 0 =
      positiveP506MatterCurrentP286NonzeroCurvatureTemporalActionTarget
        (direction canonicalLorentzianTimeDirection)
  producerConsistency : ∀ direction : P286GaugeOneForm,
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift
        direction 0 = 0

theorem
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_realizes_C3h165 :
    PositiveP506MatterCurrentP286CompleteResponseProducerSoundnessLaw := by
  exact
    { sourceGeneratedU7 :=
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_realizes_C3h163
      fullActionReadFromU7 := fun _ => rfl
      spatialResponse :=
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_response
      spatialResponseUnique := fun candidate response =>
        positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity_unique
          candidate response
      temporalResponse :=
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_response
      temporalResponseUnique := fun candidate response =>
        positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge_unique
          candidate response
      generatedActual := rfl
      originFaithful :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeAuxiliary_origin
      synchronizedSmooth :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_smooth
      synchronizedNondegenerate :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_nondegenerate
      retainsU7Fields :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields
      retainedCurvatureNonzero :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeCurvature_ne_zero
      completeTemporalMomentumResponse :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_temporalBFMomentumResponse
      completeSpatialMomentumResponse :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_spatialBFMomentumResponse
      producerConsistency :=
        positiveP506MatterCurrentP286CompleteResponseLocalActualLift_connectionEquation_origin }

end
end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
