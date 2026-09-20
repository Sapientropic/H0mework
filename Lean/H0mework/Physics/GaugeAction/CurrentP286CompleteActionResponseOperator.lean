import H0mework.Physics.ActionGeneration.P286GaussJointLocalActualLift

/-!
# Stage-9 current P286 complete action-response operator

This module extracts the complete P286 connection-action response into a
canonical-origin operator:

```text
(proof-free source, current actual)
→ current P286 connection-action dual at the origin
→ its fixed spatial and temporal restrictions
→ unique BF-Legendre velocity and unique Lie-pairing charge
→ the dimension-normalized, equal-axis Gauss profile
→ one origin-faithful complete P286 auxiliary germ.
```

The producer has no slot for a residual, endpoint, velocity, charge,
coefficient, radial profile, inverse witness, range witness, branch choice,
stationarity receipt, or equation certificate.  The coefficient of the
equal-axis profile is generated from `card (Fin 3)` and is proved unique
inside the explicitly stated symmetric affine carrier class.

The operator itself is total.  Its fixed identity-coframe BF-momentum
first-jet response laws live in the companion first-jet module; no
coframe-dependent Legendre inverse for arbitrary current coframes is claimed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentP286CompleteActionResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
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

/-! ## Current action dual and its canonical restrictions -/

/-- The complete P286 connection-action dual is read from the current actual
at the already fixed canonical origin. -/
def currentP286FullActionTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    Module.Dual ℝ P286GaugeOneForm where
  toFun direction :=
    p286GaugeConnectionAlgebraicCurrentCoefficient source current direction 0
  map_add' := by
    intro first second
    exact
      p286GaugeConnectionAlgebraicCurrentCoefficient_add_action
        source current first second 0
  map_smul' := by
    intro parameter direction
    rw [p286GaugeConnectionAlgebraicCurrentCoefficient_smul_action]
    rfl

private theorem canonicalP286SpatialGaugeOneForm_add
    (first second : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (first + second) =
      canonicalP286SpatialGaugeOneForm first +
        canonicalP286SpatialGaugeOneForm second := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.add_apply]

private theorem canonicalP286SpatialGaugeOneForm_smul
    (parameter : ℝ) (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm (parameter • direction) =
      parameter • canonicalP286SpatialGaugeOneForm direction := by
  funext formDirection
  refine Fin.cases ?_ (fun index => ?_) formDirection
  · simp [canonicalP286SpatialGaugeOneForm]
  · simp only [canonicalP286SpatialGaugeOneForm_spatial, Pi.smul_apply]

/-- The fixed inclusion of the three spatial P286 connection directions. -/
def canonicalP286SpatialActionInclusion :
    P286SpatialGaugeDirection →ₗ[ℝ] P286GaugeOneForm where
  toFun := canonicalP286SpatialGaugeOneForm
  map_add' := canonicalP286SpatialGaugeOneForm_add
  map_smul' := canonicalP286SpatialGaugeOneForm_smul

private theorem p286TemporalGaugeOneForm_add
    (first second : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (first + second) =
      p286TemporalGaugeOneForm first + p286TemporalGaugeOneForm second := by
  funext direction
  by_cases isTime : direction = canonicalLorentzianTimeDirection
  · simp [p286TemporalGaugeOneForm, isTime]
  · simp [p286TemporalGaugeOneForm, isTime]

private theorem p286TemporalGaugeOneForm_smul
    (parameter : ℝ) (component : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm (parameter • component) =
      parameter • p286TemporalGaugeOneForm component := by
  funext direction
  simp [p286TemporalGaugeOneForm, Pi.smul_apply]

/-- The fixed inclusion of the temporal P286 connection component. -/
def canonicalP286TemporalActionInclusion :
    P286CoordinateCarrier →ₗ[ℝ] P286GaugeOneForm where
  toFun := p286TemporalGaugeOneForm
  map_add' := p286TemporalGaugeOneForm_add
  map_smul' := p286TemporalGaugeOneForm_smul

def currentP286SpatialActionTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    Module.Dual ℝ P286SpatialGaugeDirection :=
  (currentP286FullActionTarget source current).comp
    canonicalP286SpatialActionInclusion

def currentP286TemporalActionTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    Module.Dual ℝ P286CoordinateCarrier :=
  (currentP286FullActionTarget source current).comp
    canonicalP286TemporalActionInclusion

@[simp] theorem currentP286SpatialActionTarget_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : P286SpatialGaugeDirection) :
    currentP286SpatialActionTarget source current direction =
      currentP286FullActionTarget source current
        (canonicalP286SpatialGaugeOneForm direction) :=
  rfl

@[simp] theorem currentP286TemporalActionTarget_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (component : P286CoordinateCarrier) :
    currentP286TemporalActionTarget source current component =
      currentP286FullActionTarget source current
        (p286TemporalGaugeOneForm component) :=
  rfl

/-! ## Unique action-generated velocity and charge -/

def currentP286SpatialAuxiliaryVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    P286SpatialGaugeDirection :=
  p286SpatialBFLegendreEquiv.symm
    (currentP286SpatialActionTarget source current)

theorem currentP286SpatialAuxiliaryVelocity_response
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    p286SpatialBFLegendreDualOperator
        (currentP286SpatialAuxiliaryVelocity source current) =
      currentP286SpatialActionTarget source current := by
  exact p286SpatialBFLegendreEquiv.apply_symm_apply _

theorem currentP286SpatialAuxiliaryVelocity_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : P286SpatialGaugeDirection)
    (response :
      p286SpatialBFLegendreDualOperator candidate =
        currentP286SpatialActionTarget source current) :
    candidate = currentP286SpatialAuxiliaryVelocity source current :=
  p286SpatialBFLegendreEquiv_unique _ candidate response

def currentP286GaussCharge
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    P286CoordinateCarrier :=
  p286CoordinateLiePairingEquiv.symm
    (currentP286TemporalActionTarget source current)

theorem currentP286GaussCharge_response
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (component : P286CoordinateCarrier) :
    p286CoordinateLiePairing (currentP286GaussCharge source current)
        component =
      currentP286TemporalActionTarget source current component := by
  change
    p286CoordinateLiePairingEquiv
        (p286CoordinateLiePairingEquiv.symm
          (currentP286TemporalActionTarget source current)) component =
      currentP286TemporalActionTarget source current component
  rw [p286CoordinateLiePairingEquiv.apply_symm_apply]

theorem currentP286GaussCharge_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : P286CoordinateCarrier)
    (response : ∀ component,
      p286CoordinateLiePairing candidate component =
        currentP286TemporalActionTarget source current component) :
    candidate = currentP286GaussCharge source current := by
  apply p286CoordinateLiePairingDualOperator_injective
  apply LinearMap.ext
  intro component
  rw [p286CoordinateLiePairingDualOperator_apply,
    p286CoordinateLiePairingDualOperator_apply,
    response, currentP286GaussCharge_response]

/-! ## Dimension-generated equal-axis Gauss profile -/

/-- A proof-side comparison family.  The physical producer below does not
accept this coefficient as an input. -/
def symmetricP286GaussRadialAuxiliaryProfile
    (coefficient : ℝ)
    (charge : P286CoordinateCarrier)
    (point : BasePoint) : P286GaugeTwoForm :=
  ∑ axis : Fin 3,
    (coefficient * point axis.succ) •
      p286GaussAuxiliaryAxisEmbedding charge axis

/-- The unique symmetric normalization determined by the three spatial
axes. -/
def canonicalP286EqualAxisCoefficient : ℝ :=
  ((Fintype.card (Fin 3) : ℕ) : ℝ)⁻¹

@[simp] theorem canonicalP286EqualAxisCoefficient_eq_one_third :
    canonicalP286EqualAxisCoefficient = (1 / 3 : ℝ) := by
  norm_num [canonicalP286EqualAxisCoefficient]

theorem canonicalP286EqualAxisCoefficient_normalized :
    ∑ _axis : Fin 3, canonicalP286EqualAxisCoefficient = 1 := by
  rw [Fin.sum_univ_three]
  norm_num [canonicalP286EqualAxisCoefficient]

theorem canonicalP286EqualAxisCoefficient_unique
    (candidate : ℝ)
    (normalized : ∑ _axis : Fin 3, candidate = 1) :
    candidate = canonicalP286EqualAxisCoefficient := by
  rw [Fin.sum_univ_three] at normalized
  rw [canonicalP286EqualAxisCoefficient_eq_one_third]
  linarith

/-- The producer-owned radial profile.  Its coefficient is generated from
`card (Fin 3)` and is not caller supplied. -/
def currentP286CanonicalGaussRadialAuxiliaryProfile
    (charge : P286CoordinateCarrier)
    (point : BasePoint) : P286GaugeTwoForm :=
  symmetricP286GaussRadialAuxiliaryProfile
    canonicalP286EqualAxisCoefficient charge point

theorem symmetricP286GaussRadialAuxiliaryProfile_unique
    (candidate : ℝ)
    (normalized : ∑ _axis : Fin 3, candidate = 1)
    (charge : P286CoordinateCarrier) :
    symmetricP286GaussRadialAuxiliaryProfile candidate charge =
      currentP286CanonicalGaussRadialAuxiliaryProfile charge := by
  rw [canonicalP286EqualAxisCoefficient_unique candidate normalized]
  rfl

theorem currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing
    (charge : P286CoordinateCarrier) :
    currentP286CanonicalGaussRadialAuxiliaryProfile charge =
      p286GaussRadialAuxiliaryProfile charge := by
  funext point pair
  simp only [currentP286CanonicalGaussRadialAuxiliaryProfile,
    symmetricP286GaussRadialAuxiliaryProfile,
    p286GaussRadialAuxiliaryProfile, Pi.smul_apply,
    Finset.sum_apply]
  rw [canonicalP286EqualAxisCoefficient_eq_one_third]

@[simp] theorem currentP286CanonicalGaussRadialAuxiliaryProfile_origin
    (charge : P286CoordinateCarrier) :
    currentP286CanonicalGaussRadialAuxiliaryProfile charge 0 = 0 := by
  rw [currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing]
  exact p286GaussRadialAuxiliaryProfile_origin charge

theorem currentP286CanonicalGaussRadialAuxiliaryProfile_contDiff
    (charge : P286CoordinateCarrier)
    (pair : Fin 6) :
    ContDiff ℝ ∞
      (fun point =>
        currentP286CanonicalGaussRadialAuxiliaryProfile charge point pair) := by
  rw [currentP286CanonicalGaussRadialAuxiliaryProfile_eq_existing]
  exact p286GaussRadialAuxiliaryProfile_contDiff charge pair

/-! ## Origin-faithful complete auxiliary germ -/

def currentP286OriginAuxiliaryCoordinate
    (current : StageNineHolonomicConfiguration) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (current.gaugeAuxiliary 0 pair)

def currentP286CompleteResponseAuxiliaryCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : P286GaugeTwoForm :=
  currentP286OriginAuxiliaryCoordinate current +
    point canonicalLorentzianTimeDirection •
      p286SpatialAuxiliaryVelocityEmbedding
        (currentP286SpatialAuxiliaryVelocity source current) +
    currentP286CanonicalGaussRadialAuxiliaryProfile
      (currentP286GaussCharge source current) point

def currentP286CompleteResponseAuxiliaryField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    BasePoint → Fin 6 → P286LieBlockData :=
  fun point pair =>
    p286CoordinateEquiv.symm
      (currentP286CompleteResponseAuxiliaryCoordinate source current point pair)

/-- The canonical-origin complete P286 action response. -/
def currentP286CompleteActionResponseOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gaugeAuxiliary :=
      currentP286CompleteResponseAuxiliaryField source current }

@[simp] theorem currentP286CompleteResponseAuxiliaryCoordinate_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    currentP286CompleteResponseAuxiliaryCoordinate source current 0 =
      currentP286OriginAuxiliaryCoordinate current := by
  simp [currentP286CompleteResponseAuxiliaryCoordinate]

theorem currentP286CompleteResponseAuxiliaryField_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    currentP286CompleteResponseAuxiliaryField source current 0 =
      current.gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  simp [currentP286CompleteResponseAuxiliaryField,
    currentP286OriginAuxiliaryCoordinate]

@[simp] theorem currentP286CompleteActionResponseOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current).gaugeAuxiliary =
      currentP286CompleteResponseAuxiliaryField source current :=
  rfl

theorem currentP286CompleteActionResponseOperator_gaugeAuxiliary_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current).gaugeAuxiliary
        0 =
      current.gaugeAuxiliary 0 :=
  currentP286CompleteResponseAuxiliaryField_origin source current

@[simp] theorem currentP286CompleteActionResponseOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current
      |>.gravityConnection) =
      current.gravityConnection :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current
      |>.gravityAuxiliary) =
      current.gravityAuxiliary :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_multiplier
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current
      |>.gravitySimplicityMultiplier) =
      current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current
      |>.gaugeConnection) =
      current.gaugeConnection :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current).scalar =
      current.scalar :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current).matter =
      current.matter :=
  rfl

@[simp] theorem currentP286CompleteActionResponseOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (currentP286CompleteActionResponseOperator source current
      |>.conjugateMatter) =
      current.conjugateMatter :=
  rfl

theorem currentP286CompleteResponseAuxiliaryCoordinate_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (pair : Fin 6) :
    ContDiff ℝ ∞ fun point : BasePoint =>
      currentP286CompleteResponseAuxiliaryCoordinate source current point pair := by
  have originSmooth :
      ContDiff ℝ ∞ fun _ : BasePoint =>
        currentP286OriginAuxiliaryCoordinate current pair :=
    contDiff_const
  have timeSmooth :
      ContDiff ℝ ∞ fun point : BasePoint =>
        point canonicalLorentzianTimeDirection •
          p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source current) pair := by
    simpa only [localBaseCoordinate_apply] using
      ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff
        |>.smul_const
          (p286SpatialAuxiliaryVelocityEmbedding
            (currentP286SpatialAuxiliaryVelocity source current) pair))
  have radialSmooth :
      ContDiff ℝ ∞ fun point : BasePoint =>
        currentP286CanonicalGaussRadialAuxiliaryProfile
          (currentP286GaussCharge source current) point pair :=
    currentP286CanonicalGaussRadialAuxiliaryProfile_contDiff _ pair
  change ContDiff ℝ ∞ fun point : BasePoint =>
    (currentP286OriginAuxiliaryCoordinate current +
      point canonicalLorentzianTimeDirection •
        p286SpatialAuxiliaryVelocityEmbedding
          (currentP286SpatialAuxiliaryVelocity source current) +
      currentP286CanonicalGaussRadialAuxiliaryProfile
        (currentP286GaussCharge source current) point) pair
  simpa only [Pi.add_apply, Pi.smul_apply] using
    ((originSmooth.add timeSmooth).add radialSmooth)

theorem currentP286CompleteActionResponseOperator_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSmooth : current.Smooth) :
    (currentP286CompleteActionResponseOperator source current).Smooth := by
  rcases currentSmooth with
    ⟨coframe, gravityConnection, gravityAuxiliary, multiplier,
      gaugeConnection, _gaugeAuxiliary, scalar, matter, conjugate⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [currentP286CompleteActionResponseOperator] using coframe
  · simpa only [currentP286CompleteActionResponseOperator] using
      gravityConnection
  · simpa only [currentP286CompleteActionResponseOperator] using
      gravityAuxiliary
  · simpa only [currentP286CompleteActionResponseOperator] using multiplier
  · simpa only [currentP286CompleteActionResponseOperator] using
      gaugeConnection
  · intro pair
    change ContDiff ℝ ∞ fun point : BasePoint =>
      p286CoordinateEquiv
        (currentP286CompleteResponseAuxiliaryField source current point pair)
    rw [show
      (fun point : BasePoint =>
        p286CoordinateEquiv
          (currentP286CompleteResponseAuxiliaryField source current point pair)) =
        (fun point : BasePoint =>
          currentP286CompleteResponseAuxiliaryCoordinate source current point
            pair) by
      funext point
      exact p286CoordinateEquiv.apply_symm_apply _]
    exact currentP286CompleteResponseAuxiliaryCoordinate_contDiff
      source current pair
  · simpa only [currentP286CompleteActionResponseOperator] using scalar
  · simpa only [currentP286CompleteActionResponseOperator] using matter
  · simpa only [currentP286CompleteActionResponseOperator] using conjugate

theorem currentP286CompleteActionResponseOperator_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentNondegenerate : current.Nondegenerate) :
    (currentP286CompleteActionResponseOperator source current).Nondegenerate := by
  intro point
  rw [currentP286CompleteActionResponseOperator_coframe]
  exact currentNondegenerate point

theorem currentP286CompleteActionResponseOperator_auxiliaryCoordinate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (currentP286CompleteActionResponseOperator source current) point =
      currentP286CompleteResponseAuxiliaryCoordinate source current point := by
  funext pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [currentP286CompleteActionResponseOperator_gaugeAuxiliary]
  exact p286CoordinateEquiv.apply_symm_apply _

theorem currentP286CompleteActionResponseOperator_pointField_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (currentP286CompleteActionResponseOperator source current) 0 =
      toContinuumPointField current 0 := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact currentP286CompleteActionResponseOperator_gaugeAuxiliary_origin
      source current
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem currentP286CompleteActionResponseOperator_actionCurrent_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient source
        (currentP286CompleteActionResponseOperator source current) direction 0 =
      currentP286FullActionTarget source current direction := by
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
  rw [currentP286CompleteActionResponseOperator_pointField_origin]
  rfl

/-!
The fixed identity-coframe first-jet response laws and producer-consistency
theorem are kept in
`StageNineCurrentP286CompleteActionResponseFirstJet`, which imports this
core operator without adding a producer-side certificate slot.
-/

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentP286CompleteActionResponseOperator
