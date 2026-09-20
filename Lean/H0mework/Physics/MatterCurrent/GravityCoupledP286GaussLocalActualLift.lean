import H0mework.Physics.ActionGeneration.P286GaussJointLocalActualLift
import H0mework.Physics.MatterCurrent.GravityCoupledLinearPlebanskiLocalActualLift

/-!
# S9-C3h158: gravity-coupled P506 current with action-generated P286 response

C3h157b first produces the complete gravity-coupled P506/L0 local actual
`U₅`.  This module continues from that actual, rather than reconstructing an
endpoint from a residual:

```text
U₅
→ its current spatial P286 connection-action functional
→ unique BF-Legendre auxiliary velocity
→ the resulting time-linear auxiliary actual
→ its current temporal Gauss-action functional
→ unique Lie-pairing charge and canonical radial profile
→ one complete local actual U₆.
```

Both targets are read from the actual action before their responses are
constructed.  The constructor accepts no residual coordinate, endpoint,
preimage, range witness, stationarity certificate, source knob, coefficient,
or branch receipt.  Equality with the earlier universal P286 response is a
downstream action/contact theorem, used only to transport the already proved
forward differentiation identities.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePlebanskiMultiplierVariation
open StageNineSourceActionGeneratedCartanConnectionLocalActualLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Contact-locality of the P286 algebraic action current -/

/-- The algebraic P286 connection current only sees the listed fields at the
tested contact.  In particular it does not see the gravity curvature or the
linear-Plebanski multiplier, so changing those fields does not change the
P286 action target when the genuine P286/scalar/matter contact is retained. -/
private theorem
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe 0 = second.coframe 0)
    (gaugeConnectionEq :
      first.gaugeConnection 0 = second.gaugeConnection 0)
    (gaugeAuxiliaryEq :
      first.gaugeAuxiliary 0 = second.gaugeAuxiliary 0)
    (scalarEq : first.scalar 0 = second.scalar 0)
    (scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative first 0 =
        holonomicScalarCovariantDerivative second 0)
    (matterEq : first.matter 0 = second.matter 0)
    (conjugateEq :
      first.conjugateMatter 0 = second.conjugateMatter 0)
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

/-! ## Spatial action target and unique response generated from `U₅` -/

private theorem canonicalP286SpatialGaugeOneForm_add_current
    (first second : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (first + second) =
      canonicalP286SpatialGaugeOneForm first +
        canonicalP286SpatialGaugeOneForm second := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.add_apply]

private theorem canonicalP286SpatialGaugeOneForm_smul_current
    (parameter : ℝ) (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (parameter • direction) =
      parameter • canonicalP286SpatialGaugeOneForm direction := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.smul_apply]

/-- The spatial P286 action target read from the already generated `U₅`. -/
def positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget :
    Module.Dual ℝ P286SpatialGaugeDirection where
  toFun direction :=
    p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentGravityCoupledLocalActualLift
      (canonicalP286SpatialGaugeOneForm direction) 0
  map_add' := by
    intro first second
    rw [canonicalP286SpatialGaugeOneForm_add_current,
      p286GaugeConnectionAlgebraicCurrentCoefficient_add_action]
  map_smul' := by
    intro parameter direction
    rw [canonicalP286SpatialGaugeOneForm_smul_current,
      p286GaugeConnectionAlgebraicCurrentCoefficient_smul_action]
    rfl

/-- The unique spatial auxiliary velocity generated by the current action. -/
def positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity :
    P286SpatialGaugeDirection :=
  p286SpatialBFLegendreEquiv.symm
    positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget

theorem
    positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity_response :
    p286SpatialBFLegendreDualOperator
        positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity =
      positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget := by
  change
    p286SpatialBFLegendreEquiv
        (p286SpatialBFLegendreEquiv.symm
          positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget) =
      positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget
  exact
    p286SpatialBFLegendreEquiv.apply_symm_apply
      positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget

theorem
    positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity_unique
    (candidate : P286SpatialGaugeDirection)
    (response :
      p286SpatialBFLegendreDualOperator candidate =
        positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget) :
    candidate =
      positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity := by
  exact
    p286SpatialBFLegendreEquiv_unique
      positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget
      candidate response

private theorem
    positiveP506MatterCurrentGravityCoupledLocalActualLift_actionCurrent_eq_C3h109
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource positiveC3h109Actual direction 0 := by
  apply p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
  · rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one]
    simp [positiveC3h109Actual]
  · rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeConnection_zero,
      positiveC3h109Actual,
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_gaugeConnection_eq_zero]
  · rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeAuxiliary_zero,
      positiveC3h109Actual_gaugeAuxiliary_eq_zero]
  · rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_scalar_vacuum,
      positiveC3h109Actual,
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_scalar_eq_sourceVacuum]
  · funext formDirection
    rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_scalarCovariantDerivative_zero]
    rw [positiveC3h109Actual,
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_scalarCovariantDerivative_eq_zero]
    rfl
  · rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin,
      positiveC3h109Actual,
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_matter_origin]
  · rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugate_origin,
      positiveC3h109Actual,
      positiveSourceActionGeneratedCartanConnectionLocalActualLift_conjugate_origin]

/-- Proof-side comparison only: the new target is extensionally the earlier
specialization because both are evaluations of the same action at the same
P286-relevant contact.  The old target is not an input to the new producer. -/
theorem
    positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget_eq_C3h109 :
    positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget =
      positiveC3h109P286SpatialActionTarget := by
  apply LinearMap.ext
  intro direction
  exact
    positiveP506MatterCurrentGravityCoupledLocalActualLift_actionCurrent_eq_C3h109
      (canonicalP286SpatialGaugeOneForm direction)

theorem
    positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity_eq_C3h117 :
    positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity =
      positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity := by
  unfold positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity
    positiveSourceActionGeneratedP286SpatialAuxiliaryVelocity
  rw [positiveP506MatterCurrentGravityCoupledP286SpatialActionTarget_eq_C3h109]

/-! ## Current momentum actual and temporal Gauss target -/

/-- Install only the current action-generated spatial auxiliary velocity on
`U₅`.  All other primitive fields are retained from `U₅`. -/
def positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentGravityCoupledLocalActualLift with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        ((point canonicalLorentzianTimeDirection) •
          p286SpatialAuxiliaryVelocityEmbedding
            positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity
            pair) }

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift_gaugeAuxiliary_origin :
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift.gaugeAuxiliary
        0 =
      0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift]

private theorem p286TemporalGaugeOneForm_add_current
    (first second : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (first + second) =
      p286TemporalGaugeOneForm first + p286TemporalGaugeOneForm second := by
  funext direction
  by_cases isTime : direction = canonicalLorentzianTimeDirection
  · simp [p286TemporalGaugeOneForm, isTime]
  · simp [p286TemporalGaugeOneForm, isTime]

private theorem p286TemporalGaugeOneForm_smul_current
    (parameter : ℝ) (component : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (parameter • component) =
      parameter • p286TemporalGaugeOneForm component := by
  funext direction
  simp [p286TemporalGaugeOneForm, Pi.smul_apply]

/-- The temporal Gauss target is read from the newly generated momentum
actual, not from the historical C3h110 specialization. -/
def positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget :
    Module.Dual ℝ P286CoordinateCarrier where
  toFun component :=
    p286GaugeConnectionAlgebraicCurrentCoefficient
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
      (p286TemporalGaugeOneForm component) 0
  map_add' := by
    intro first second
    rw [p286TemporalGaugeOneForm_add_current,
      p286GaugeConnectionAlgebraicCurrentCoefficient_add_action]
  map_smul' := by
    intro parameter component
    rw [p286TemporalGaugeOneForm_smul_current,
      p286GaugeConnectionAlgebraicCurrentCoefficient_smul_action]
    rfl

/-- The unique charge coordinate generated by the current temporal action. -/
def positiveP506MatterCurrentGravityCoupledP286GaussCharge :
    P286CoordinateCarrier :=
  p286CoordinateLiePairingEquiv.symm
    positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget

theorem positiveP506MatterCurrentGravityCoupledP286GaussCharge_response
    (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        positiveP506MatterCurrentGravityCoupledP286GaussCharge component =
      positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget
        component := by
  change
    p286CoordinateLiePairingEquiv
        (p286CoordinateLiePairingEquiv.symm
          positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget)
        component =
      positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget
        component
  rw [p286CoordinateLiePairingEquiv.apply_symm_apply]

theorem positiveP506MatterCurrentGravityCoupledP286GaussCharge_unique
    (candidate : P286CoordinateCarrier)
    (response :
      ∀ component,
        p286CoordinateLiePairing candidate component =
          positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget
            component) :
    candidate = positiveP506MatterCurrentGravityCoupledP286GaussCharge := by
  apply p286CoordinateLiePairingDualOperator_injective
  apply LinearMap.ext
  intro component
  rw [p286CoordinateLiePairingDualOperator_apply,
    p286CoordinateLiePairingDualOperator_apply,
    response,
    positiveP506MatterCurrentGravityCoupledP286GaussCharge_response]

private theorem
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift_pointField_origin :
    toContinuumPointField
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift 0 =
      toContinuumPointField
        positiveP506MatterCurrentGravityCoupledLocalActualLift 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift.gaugeAuxiliary
          0 =
        positiveP506MatterCurrentGravityCoupledLocalActualLift.gaugeAuxiliary 0
    rw [positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift_gaugeAuxiliary_origin,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeAuxiliary_zero]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift_actionCurrent_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift_pointField_origin]
  rfl

theorem
    positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget_eq_C3h110 :
    positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget =
      positiveC3h110P286TemporalGaussActionTarget := by
  apply LinearMap.ext
  intro component
  change
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
        (p286TemporalGaugeOneForm component) 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286MomentumJointLocalActualLift
        (p286TemporalGaugeOneForm component) 0
  calc
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledLocalActualLift
          (p286TemporalGaugeOneForm component) 0 :=
      positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift_actionCurrent_origin
        _
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource positiveC3h109Actual
          (p286TemporalGaugeOneForm component) 0 :=
      positiveP506MatterCurrentGravityCoupledLocalActualLift_actionCurrent_eq_C3h109
        _
    _ = _ :=
      (positiveSourceActionGeneratedP286MomentumJointLocalActualLift_actionCurrent_origin
        _).symm

theorem positiveP506MatterCurrentGravityCoupledP286GaussCharge_eq_C3h118 :
    positiveP506MatterCurrentGravityCoupledP286GaussCharge =
      positiveSourceActionGeneratedP286GaussCharge := by
  unfold positiveP506MatterCurrentGravityCoupledP286GaussCharge
    positiveSourceActionGeneratedP286GaussCharge
  rw [positiveP506MatterCurrentGravityCoupledP286TemporalGaussActionTarget_eq_C3h110]

/-! ## Complete current P286 actual `U₆` -/

/-- The full auxiliary path combines the current action-generated time
velocity and the current action-generated radial Gauss profile. -/
def positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate
    (point : BasePoint) : P286GaugeTwoForm :=
  point canonicalLorentzianTimeDirection •
      p286SpatialAuxiliaryVelocityEmbedding
        positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity +
    p286GaussRadialAuxiliaryProfile
      positiveP506MatterCurrentGravityCoupledP286GaussCharge point

/-- `U₆`: the gravity-coupled P506 current actual with both P286 action
responses installed.  Its record base is `U₅`, not the historical P286
specialization used later in the proof-side transport. -/
def positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift :
    StageNineHolonomicConfiguration :=
  { positiveP506MatterCurrentGravityCoupledLocalActualLift with
    gaugeAuxiliary := fun point pair =>
      p286CoordinateEquiv.symm
        (positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate
          point pair) }

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeAuxiliary_origin :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeAuxiliary
        0 =
      0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift,
    positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate]

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate_eq_C3h118
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate point =
      positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate point := by
  unfold positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate
    positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate
  rw [positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity_eq_C3h117,
    positiveP506MatterCurrentGravityCoupledP286GaussCharge_eq_C3h118]

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeAuxiliary_eq_C3h118 :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeAuxiliary =
      positiveSourceActionGeneratedP286GaussJointLocalActualLift.gaugeAuxiliary := by
  funext point pair
  change
    p286CoordinateEquiv.symm
        (positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate
          point pair) =
      p286CoordinateEquiv.symm
        (positiveSourceActionGeneratedP286GaussAuxiliaryCoordinate point pair)
  rw [positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate_eq_C3h118]

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_coframe_one
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.coframe
        point =
      1 :=
  positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one point

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gravityConnection
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gravityConnection
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.gravityConnection
        point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gravityAuxiliary
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gravityAuxiliary
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.gravityAuxiliary
        point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_multiplier
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gravitySimplicityMultiplier
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.gravitySimplicityMultiplier
        point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeConnection
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeConnection
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.gaugeConnection
        point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_scalar
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.scalar
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.scalar point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_matter
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.matter
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.matter point :=
  rfl

@[simp] theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_conjugateMatter
    (point : BasePoint) :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.conjugateMatter
        point =
      positiveP506MatterCurrentGravityCoupledLocalActualLift.conjugateMatter
        point :=
  rfl

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_curvature_origin :
    holonomicGravityCurvature
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
        0 =
      positiveP506MatterCurrentGravityCoupledCurvatureTarget :=
  positiveP506MatterCurrentGravityCoupledLocalActualLift_curvature_origin

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_auxiliaryBalance :
    holonomicGravityCurvature
          positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
          0 -
        gravityInternalDualEquiv
          (positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gravityAuxiliary
            0) +
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gravitySimplicityMultiplier
          0 =
      0 :=
  positiveP506MatterCurrentGravityCoupledLocalActualLift_auxiliaryBalance

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_simplicity :
    GravitySimplicityEquation
      positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift :=
  positiveP506MatterCurrentGravityCoupledLocalActualLift_simplicity

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_nondegenerate :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.Nondegenerate :=
  positiveP506MatterCurrentGravityCoupledLocalActualLift_nondegenerate

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_smooth :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.Smooth := by
  rcases positiveP506MatterCurrentGravityCoupledLocalActualLift_smooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  exact
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, fun pair => by
        have timeSmooth :
            ContDiff ℝ ∞ fun point : BasePoint =>
              point canonicalLorentzianTimeDirection •
                p286SpatialAuxiliaryVelocityEmbedding
                  positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity
                  pair := by
          simpa only [localBaseCoordinate_apply] using
            ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff
              |>.smul_const
                (p286SpatialAuxiliaryVelocityEmbedding
                  positiveP506MatterCurrentGravityCoupledP286SpatialAuxiliaryVelocity
                  pair))
        have radialSmooth :=
          p286GaussRadialAuxiliaryProfile_contDiff
            positiveP506MatterCurrentGravityCoupledP286GaussCharge pair
        simpa only [
          positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift,
          positiveP506MatterCurrentGravityCoupledP286GaussAuxiliaryCoordinate,
          p286CoordinateEquiv.apply_symm_apply, Pi.add_apply,
          Pi.smul_apply] using
          timeSmooth.add radialSmooth,
      scalar, matter, conjugate⟩

theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_pointField_origin :
    toContinuumPointField
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
        0 =
      toContinuumPointField
        positiveP506MatterCurrentGravityCoupledLocalActualLift 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change
      positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.gaugeAuxiliary
          0 =
        positiveP506MatterCurrentGravityCoupledLocalActualLift.gaugeAuxiliary 0
    rw [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeAuxiliary_origin,
      positiveP506MatterCurrentGravityCoupledLocalActualLift_gaugeAuxiliary_zero]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_actionCurrent_origin_eq_C3h118
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
        direction 0 =
      p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 := by
  calc
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledLocalActualLift direction 0 := by
      unfold p286GaugeConnectionAlgebraicCurrentCoefficient
      rw [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_pointField_origin]
      rfl
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource positiveC3h109Actual direction 0 :=
      positiveP506MatterCurrentGravityCoupledLocalActualLift_actionCurrent_eq_C3h109
        direction
    _ = p286GaugeConnectionAlgebraicCurrentCoefficient
          positiveSmoothUnifiedSource
          positiveSourceActionGeneratedP286MomentumJointLocalActualLift
          direction 0 :=
      (positiveSourceActionGeneratedP286MomentumJointLocalActualLift_actionCurrent_origin
        direction).symm
    _ = _ :=
      (positiveSourceActionGeneratedP286GaussJointLocalActualLift_actionCurrent_origin
        direction).symm

private theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_coframe_eq_C3h118 :
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift.coframe =
      positiveSourceActionGeneratedP286GaussJointLocalActualLift.coframe := by
  funext point
  change
    positiveP506MatterCurrentGravityCoupledLocalActualLift.coframe point =
      positiveC3h109Actual.coframe point
  rw [positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one]
  simp [positiveC3h109Actual]

private theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_bfMomentum_eq_C3h118
    (direction : P286GaugeTwoForm) :
    p286GaugeConnectionBFDifferentialMomentum
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
        direction =
      p286GaugeConnectionBFDifferentialMomentum
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction := by
  funext point
  unfold p286GaugeConnectionBFDifferentialMomentum generatedVolumeDensity
    holonomicP286GaugeAuxiliaryCoordinate
  simp only [toContinuumPointField]
  rw [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_coframe_eq_C3h118,
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_gaugeAuxiliary_eq_C3h118]

private theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_divergence_eq_C3h118
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
        direction 0 =
      p286GaugeConnectionBFDifferentialMomentumDivergence
        positiveSourceActionGeneratedP286GaussJointLocalActualLift
        direction 0 := by
  unfold p286GaugeConnectionBFDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_bfMomentum_eq_C3h118]

/-- Frontier theorem: the proof-free P506/L0 path and the complete action
first generate `U₆`; the P286 Euler--Lagrange coefficient is then read from
that same actual and vanishes in every one-form direction. -/
theorem
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_connectionEquation_origin
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionEulerLagrangeCoefficient
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift
        direction 0 =
      0 := by
  unfold p286GaugeConnectionEulerLagrangeCoefficient
  rw [positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_actionCurrent_origin_eq_C3h118,
    positiveP506MatterCurrentGravityCoupledP286GaussJointLocalActualLift_divergence_eq_C3h118]
  exact
    positiveSourceActionGeneratedP286GaussJointLocalActualLift_connectionEquation_origin
      direction

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
