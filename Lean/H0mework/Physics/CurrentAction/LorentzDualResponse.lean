import H0mework.Physics.CurrentAction.PrimitiveCauchyUpdate

/-!
# Stage-9 current canonical full-action Lorentz dual response

This module continues the C3h187 path/action-first construction without
replaying the full synchronized response.  At every spatial contact it uses
the already generated C3h153 linear-Plebanski base actual, then installs only
the direct P286 and two primal-matter responses:

```text
(proof-free source, current Cauchy state, spatial contact)
-> C3h153 linear-Plebanski base actual
-> direct complete P286 response
-> temporal primal-matter first-germ response
-> complete primal-matter first-germ response
-> gravity-preserving fresh actual.
```

The Lorentz BF momentum, its coherent spatial divergence, and the algebraic
spin-current term are all read from that same final actual family.  The
connection leg is generated independently by the linear-Plebanski action law
on the same current Cauchy state.  Their affine canonical-pair update therefore
accepts no residual, response coefficient, branch, event, scheduler, endpoint,
or equation receipt.

The substitution theorems below are producer-soundness and uniqueness facts
for this source-generated update.  They do not claim a holonomic actual lift,
an independent Euler--Lagrange closure, a branch selection, or a global
source-time evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzDualResponse

open StageNineCanonicalCauchyState
open StageNineCurrentCanonicalFullActionPrimitiveCauchyUpdate
open StageNineCurrentFullSynchronizedCompleteP286PrimitiveCauchyUpdate
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## Gravity-preserving fresh actual family -/

/-- Install the direct complete P286 response on the C3h153 base actual.
Unlike the former full-synchronized replay, this leg does not replace the
linear-Plebanski gravity fields. -/
def currentCanonicalGravityPreservingP286Actual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  currentP286CompleteActionResponseOperator source
    (currentCanonicalFullActionBaseActual source current space)

/-- Install the temporal primal-matter first-germ response while retaining
the C3h153 gravity sector. -/
def currentCanonicalGravityPreservingTemporalMatterActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  actionGeneratedMatterTemporalFirstGermActual source
    (currentCanonicalGravityPreservingP286Actual source current space)

/-- The final fresh actual at one contact.  Its P286 and matter responses are
newly generated, while its coframe, Lorentz connection, gravity auxiliary,
and multiplier remain those of the C3h153 base actual. -/
def currentCanonicalGravityPreservingActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  actionGeneratedMatterCompleteFirstGermActual source
    (currentCanonicalGravityPreservingTemporalMatterActual source current
      space)

@[simp] theorem currentCanonicalGravityPreservingActual_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current space).coframe =
      (currentCanonicalFullActionBaseActual source current space).coframe :=
  rfl

@[simp] theorem currentCanonicalGravityPreservingActual_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current
        space).gravityConnection =
      (currentCanonicalFullActionBaseActual source current
        space).gravityConnection :=
  rfl

@[simp] theorem currentCanonicalGravityPreservingActual_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current
        space).gravityAuxiliary =
      (currentCanonicalFullActionBaseActual source current
        space).gravityAuxiliary :=
  rfl

@[simp] theorem currentCanonicalGravityPreservingActual_multiplier
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current
        space).gravitySimplicityMultiplier =
      (currentCanonicalFullActionBaseActual source current
        space).gravitySimplicityMultiplier :=
  rfl

/-- The gravity-preserving fresh actual retains the input Cauchy coframe at
the selected contact.  This is an origin-field bridge, not a transported
equation receipt. -/
@[simp] theorem
    currentCanonicalGravityPreservingActual_coframe_origin_eq_currentSlice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current space).coframe 0 =
      current.coframe space := by
  change
    (currentCanonicalFullActionBaseActual source current space).coframe 0 =
      current.coframe space
  exact sourceActionGeneratedLinearPlebanskiJointLocalActualLift_coframe
    source current space 0

/-- The complete fresh matter installers preserve the input primal field at
their common contact origin. -/
@[simp] theorem
    currentCanonicalGravityPreservingActual_matter_origin_eq_currentSlice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current space).matter 0 =
      current.matter space := by
  change
    (actionGeneratedMatterCompleteFirstGermActual source
      (actionGeneratedMatterTemporalFirstGermActual source
        (currentP286CompleteActionResponseOperator source
          (currentCanonicalFullActionBaseActual source current
            space)))).matter 0 =
      current.matter space
  rw [actionGeneratedMatterCompleteFirstGermActual_matter_origin,
    actionGeneratedMatterTemporalFirstGermActual_matter_origin,
    currentP286CompleteActionResponseOperator_matter]
  exact currentFullSynchronizedCompleteP286BaseActual_matter_origin
    source current space

/-- The complete fresh matter installers preserve the input adjoint field at
their common contact origin. -/
@[simp] theorem
    currentCanonicalGravityPreservingActual_conjugateMatter_origin_eq_currentSlice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current
        space).conjugateMatter 0 =
      current.conjugateMatter space := by
  change
    (currentP286CompleteActionResponseOperator source
      (currentCanonicalFullActionBaseActual source current
        space)).conjugateMatter 0 =
      current.conjugateMatter space
  rw [currentP286CompleteActionResponseOperator_conjugateMatter]
  exact currentFullSynchronizedCompleteP286BaseActual_conjugateMatter_origin
    source current space

/-- The final fresh actual retains the current slice's Lorentz connection at
the contact origin.  This is the exact generic bridge needed before an exact
specialization may restart from a generated C3h187 zero-response state. -/
@[simp] theorem currentCanonicalGravityPreservingActual_gravityConnection_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (currentCanonicalGravityPreservingActual source current
        space).gravityConnection 0 =
      current.gravityConnection space := by
  rw [currentCanonicalGravityPreservingActual_gravityConnection]
  exact
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_initialConnection
      source current space

/-- Since every outer leg preserves the complete Lorentz connection field,
the final fresh actual retains the linear-Plebanski curvature generated by
the C3h153 base actual at the same contact. -/
theorem currentCanonicalGravityPreservingActual_curvature_origin
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    holonomicGravityCurvature
        (currentCanonicalGravityPreservingActual source current space) 0 =
      linearPlebanskiActionGeneratedGravityCurvature current space := by
  change
    holonomicGravityCurvature
        (currentCanonicalFullActionBaseActual source current space) 0 =
      linearPlebanskiActionGeneratedGravityCurvature current space
  exact
    sourceActionGeneratedLinearPlebanskiJointLocalActualLift_curvature_origin
      source current space

theorem currentCanonicalGravityPreservingTemporalMatterActual_faithfulZeroFiber
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalGravityPreservingTemporalMatterActual source current
          space =
        currentCanonicalGravityPreservingP286Actual source current space ↔
      matterTemporalDiracYukawaFirstGermResidual source
          (currentCanonicalGravityPreservingP286Actual source current space) =
        0 := by
  unfold currentCanonicalGravityPreservingTemporalMatterActual
    actionGeneratedMatterTemporalFirstGermActual
    actionGeneratedMatterTemporalFirstGermAcceleration
  rw [installMatterTemporalFirstGermResponse_eq_iff,
    actionGeneratedMatterTemporalAcceleration_eq_zero_iff]

theorem currentCanonicalGravityPreservingActual_faithfulCompleteZeroFiber
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    currentCanonicalGravityPreservingActual source current space =
          currentCanonicalGravityPreservingTemporalMatterActual source current
            space ↔
      matterCompleteDiracYukawaFirstGermResidual source
          (currentCanonicalGravityPreservingTemporalMatterActual source current
            space) =
        0 := by
  unfold currentCanonicalGravityPreservingActual
  exact actionGeneratedMatterCompleteFirstGermActual_eq_iff source
    (currentCanonicalGravityPreservingTemporalMatterActual source current space)

/-! ## Lorentz dual of the same final actual family -/

/-- Lorentz BF momentum evaluated on the final fresh actual at every contact.
The derivative direction selects the member of the coherent momentum field. -/
def currentCanonicalFullActionLorentzBFMomentumEvaluation
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (derivativeDirection : LorentzianIndex) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real :=
  fun space direction =>
    let actual := currentCanonicalGravityPreservingActual source current space
    lorentzConnectionBFDifferentialMomentum actual
      (lorentzConnectionExteriorDerivativeDirection derivativeDirection
        (canonicalLorentzSpatialBivectorOneForm direction))
      0

/-- Canonical Lorentz BF momentum conjugate to the spatial connection: the
time-direction member of the coherent final-actual momentum field. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real :=
  currentCanonicalFullActionLorentzBFMomentumEvaluation source current
    canonicalLorentzianTimeDirection

/-! ## Canonical finite spatial dual

The Cauchy state intentionally stores arbitrary spatial fields, not a
differentiability receipt.  Consequently the raw `fderiv` action readout
below cannot be treated as additive in a test direction merely because its
formula looks linear: `fderiv_add` would require regularity not present in the
primitive state type.  The Lorentz spatial cotangent response is therefore
defined by evaluating the action on the fixed 18 coordinate directions and
taking their unique linear extension.  This is the finite canonical dual of
the action, not a supplied response or a choice of preimage.
-/

/-- One of the 18 fixed coordinate directions of the spatial Lorentz
connection carrier. -/
def canonicalLorentzSpatialBivectorCoordinateDirection
    (spatialDirection : Fin 3)
    (internalPair : Fin 6) : LorentzSpatialBivectorDirection :=
  fun candidateSpatial candidatePair =>
    if candidateSpatial = spatialDirection ∧ candidatePair = internalPair then
      1
    else
      0

/-- Every spatial Lorentz direction has its canonical 18-coordinate
expansion. -/
theorem canonicalLorentzSpatialBivectorCoordinateExpansion
    (direction : LorentzSpatialBivectorDirection) :
    (∑ spatialDirection : Fin 3,
      ∑ internalPair : Fin 6,
        direction spatialDirection internalPair •
          canonicalLorentzSpatialBivectorCoordinateDirection
            spatialDirection internalPair) =
      direction := by
  funext candidateSpatial candidatePair
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single candidateSpatial]
  · rw [Finset.sum_eq_single candidatePair]
    · simp [canonicalLorentzSpatialBivectorCoordinateDirection]
    · intro other _ other_ne
      simp [canonicalLorentzSpatialBivectorCoordinateDirection,
        other_ne.symm]
    · simp
  · intro other _ other_ne
    apply Finset.sum_eq_zero
    intro internalPair _
    simp [canonicalLorentzSpatialBivectorCoordinateDirection,
      other_ne.symm]
  · simp

/-- Canonical linear extension of 18 real coordinate responses. -/
def lorentzSpatialBivectorLinearExtension
    (coordinates : Fin 3 → Fin 6 → Real) :
    Module.Dual Real LorentzSpatialBivectorDirection where
  toFun := fun direction =>
    ∑ spatialDirection : Fin 3,
      ∑ internalPair : Fin 6,
        direction spatialDirection internalPair *
          coordinates spatialDirection internalPair
  map_add' := by
    intro first second
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro spatialDirection _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro internalPair _
    ring
  map_smul' := by
    intro scalar direction
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro spatialDirection _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro internalPair _
    simp only [RingHom.id_apply]
    ring

@[simp] theorem lorentzSpatialBivectorLinearExtension_coordinateDirection
    (coordinates : Fin 3 → Fin 6 → Real)
    (spatialDirection : Fin 3)
    (internalPair : Fin 6) :
    lorentzSpatialBivectorLinearExtension coordinates
        (canonicalLorentzSpatialBivectorCoordinateDirection
          spatialDirection internalPair) =
      coordinates spatialDirection internalPair := by
  fin_cases spatialDirection <;> fin_cases internalPair <;>
    simp [lorentzSpatialBivectorLinearExtension,
      canonicalLorentzSpatialBivectorCoordinateDirection,
      Fin.sum_univ_three, Fin.sum_univ_six]

/-- The canonical extension loses no coordinate information. -/
theorem lorentzSpatialBivectorLinearExtension_eq_zero_iff
    (coordinates : Fin 3 → Fin 6 → Real) :
    lorentzSpatialBivectorLinearExtension coordinates = 0 ↔
      coordinates = 0 := by
  constructor
  · intro extensionZero
    funext spatialDirection internalPair
    have coordinateZero := congrArg
      (fun response : Module.Dual Real LorentzSpatialBivectorDirection =>
        response
          (canonicalLorentzSpatialBivectorCoordinateDirection
            spatialDirection internalPair))
      extensionZero
    simpa using coordinateZero
  · intro coordinatesZero
    rw [coordinatesZero]
    apply LinearMap.ext
    intro direction
    simp [lorentzSpatialBivectorLinearExtension]

/-- One spatial derivative summand from the whole contact family.  This is
taken in `StageNineSpatialPoint`; it is not the derivative of one isolated
constant local germ. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (direction : LorentzSpatialBivectorDirection) : Real :=
  fderiv Real
    (currentCanonicalFullActionLorentzBFMomentumEvaluation source current
      derivativeDirection.succ · direction)
    space (canonicalSpatialCoordinateDirection derivativeDirection)

/-- Spatial divergence across the whole contact family.  Each summand is
named separately so provenance transport can match the action derivative
without unfolding the complete current-state actualizer. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) : Real :=
  ∑ derivativeDirection : Fin 3,
    currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
      source current space derivativeDirection direction

theorem currentCanonicalFullActionLorentzSpatialBFMomentumDivergence_eq_sum
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
        source current space direction =
      ∑ derivativeDirection : Fin 3,
        currentCanonicalFullActionLorentzSpatialBFMomentumDerivative
          source current space derivativeDirection direction := by
  rfl

/-- The unbundled action response on one spatial Lorentz test direction.
This is sampled only on the canonical basis below; it is not asserted to be
linear for an arbitrary primitive Cauchy state. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) : Real :=
  let actual := currentCanonicalGravityPreservingActual source current space
  let fullDirection := canonicalLorentzSpatialBivectorOneForm direction
  lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
      fullDirection 0 -
    currentCanonicalFullActionLorentzSpatialBFMomentumDivergence
      source current space direction

/-- The 18 action-owned coordinates of the Lorentz BF-momentum velocity. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) : Fin 3 → Fin 6 → Real :=
  fun spatialDirection internalPair =>
    currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
      source current space
      (canonicalLorentzSpatialBivectorCoordinateDirection
        spatialDirection internalPair)

/-- The genuine finite Lorentz spatial dual generated from the 18 canonical
action responses at one contact. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumVelocityDual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Module.Dual Real LorentzSpatialBivectorDirection :=
  lorentzSpatialBivectorLinearExtension
    (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
      source current space)

/-- The Lorentz BF-momentum action velocity.  Both its algebraic term and its
spatial divergence come from the same final fresh actual family, sampled on
all 18 canonical directions and uniquely extended as a finite linear dual. -/
def currentCanonicalFullActionLorentzSpatialBFMomentumVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real :=
  fun space =>
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocityDual
      source current space

@[simp] theorem
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_coordinateDirection
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (spatialDirection : Fin 3)
    (internalPair : Fin 6) :
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source current
        space
        (canonicalLorentzSpatialBivectorCoordinateDirection
          spatialDirection internalPair) =
      currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
        source current space
        (canonicalLorentzSpatialBivectorCoordinateDirection
          spatialDirection internalPair) := by
  exact
    lorentzSpatialBivectorLinearExtension_coordinateDirection
      (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
        source current space)
      spatialDirection internalPair

/-- Faithful zero fiber of the complete 18-coordinate Lorentz momentum
operator.  Vanishing is neither inferred from one probe nor hidden in a
stored receipt: every canonical action response must vanish. -/
theorem
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_eq_zero_iff
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source current =
          0 ↔
      ∀ space spatialDirection internalPair,
        currentCanonicalFullActionLorentzSpatialBFMomentumRawActionReadout
            source current space
            (canonicalLorentzSpatialBivectorCoordinateDirection
              spatialDirection internalPair) =
          0 := by
  constructor
  · intro velocityZero space spatialDirection internalPair
    have coordinateZero := congrArg
      (fun velocity :
          StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real =>
        velocity space
          (canonicalLorentzSpatialBivectorCoordinateDirection
            spatialDirection internalPair))
      velocityZero
    simpa using coordinateZero
  · intro coordinatesZero
    funext space direction
    change
      lorentzSpatialBivectorLinearExtension
          (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
            source current space)
          direction =
        0
    have coordinateFunctionZero :
        currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
            source current space =
          0 := by
      funext spatialDirection internalPair
      exact coordinatesZero space spatialDirection internalPair
    rw [coordinateFunctionZero]
    simp [lorentzSpatialBivectorLinearExtension]

/-- Downstream action equation for a candidate momentum velocity.  The final
actual is not a parameter of this mouth; source and current generate it. -/
def CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (velocity :
      StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real) : Prop :=
  ∀ space direction,
    velocity space direction =
      lorentzSpatialBivectorLinearExtension
        (currentCanonicalFullActionLorentzSpatialBFMomentumActionCoordinates
          source current space)
        direction

/-- Producer-soundness: the generated dual velocity satisfies the same action
equation from which it was constructed. -/
theorem currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw source current
      (currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
        current) := by
  intro space direction
  rfl

/-- Once source and current are fixed, the Lorentz BF-momentum action equation
leaves no branch choice. -/
theorem currentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw_unique
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (first second :
      StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real)
    (firstLaw :
      CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw source
        current first)
    (secondLaw :
      CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw source
        current second) :
    first = second := by
  funext space direction
  exact (firstLaw space direction).trans (secondLaw space direction).symm

/-! ## Affine Lorentz canonical-pair update -/

/-- Canonical phase point built from the current slice connection and the BF
dual of the fresh final actual family. -/
def currentCanonicalFullActionLorentzCanonicalPhaseState
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection :=
    sourceActionGeneratedLorentzSpatialConnectionCoordinate current
  spatialBFMomentumEvaluation :=
    currentCanonicalFullActionLorentzSpatialBFMomentumEvaluation source current

/-- The complete Lorentz canonical velocity.  Its connection leg is the
linear-Plebanski response of `current`; its momentum leg is the dual of the
same gravity-preserving final actual family used above. -/
def currentCanonicalFullActionLorentzCanonicalPhaseVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection :=
    linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity current
  spatialBFMomentumEvaluation :=
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source current

/-- The explicit zero element used only to state the faithful zero fiber.  It
is kept as a named value instead of installing a new global `Zero` instance
for the imported canonical-phase type. -/
def zeroLorentzCanonicalPhaseVelocity :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection := 0
  spatialBFMomentumEvaluation := 0

/-- Affine action-generated Lorentz canonical-pair update. -/
def currentCanonicalFullActionLorentzCanonicalPhaseUpdate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection := fun space direction internalPair =>
    (currentCanonicalFullActionLorentzCanonicalPhaseState source
        current).spatialConnection space direction internalPair +
      time *
        (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
          current).spatialConnection space direction internalPair
  spatialBFMomentumEvaluation := fun space direction =>
    (currentCanonicalFullActionLorentzCanonicalPhaseState source
        current).spatialBFMomentumEvaluation space direction +
      time *
        (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
          current).spatialBFMomentumEvaluation space direction

/-- The unit response is named separately because its exact fixed-point fiber
is the canonical branch-free acceptance gate. -/
def currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineLorentzCanonicalPhaseState :=
  currentCanonicalFullActionLorentzCanonicalPhaseUpdate source current 1

@[simp] theorem currentCanonicalFullActionLorentzCanonicalPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzCanonicalPhaseUpdate source current 0 =
      currentCanonicalFullActionLorentzCanonicalPhaseState source current := by
  apply StageNineLorentzCanonicalPhaseState.ext
  · funext space direction internalPair
    simp [currentCanonicalFullActionLorentzCanonicalPhaseUpdate]
  · funext space direction
    simp [currentCanonicalFullActionLorentzCanonicalPhaseUpdate]

/-- Read the connection velocity from the already generated unit update. -/
def currentCanonicalFullActionLorentzUnitConnectionVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → Fin 6 → Real :=
  fun space direction internalPair =>
    (currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate source
          current).spatialConnection space direction internalPair -
      (currentCanonicalFullActionLorentzCanonicalPhaseState source
          current).spatialConnection space direction internalPair

theorem currentCanonicalFullActionLorentzUnitConnectionVelocity_eq
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzUnitConnectionVelocity source current =
      linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity
        current := by
  funext space direction internalPair
  simp [currentCanonicalFullActionLorentzUnitConnectionVelocity,
    currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate,
    currentCanonicalFullActionLorentzCanonicalPhaseUpdate,
    currentCanonicalFullActionLorentzCanonicalPhaseVelocity]

/-- The connection component of the unit update satisfies the
linear-Plebanski temporal-spatial curvature law on the current state. -/
theorem currentCanonicalFullActionLorentzUnitConnection_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    LinearPlebanskiLorentzActionGeneratedSpatialVelocityLaw current
      (currentCanonicalFullActionLorentzUnitConnectionVelocity source
        current) := by
  rw [currentCanonicalFullActionLorentzUnitConnectionVelocity_eq]
  exact
    linearPlebanskiActionGeneratedLorentzSpatialConnectionVelocity_satisfies_actionLaw
      current

/-- The same linear-Plebanski law uniquely determines the connection
increment read from the unit update. -/
theorem currentCanonicalFullActionLorentzUnitConnectionVelocityLaw_unique
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (candidate : StageNineSpatialPoint → Fin 3 → Fin 6 → Real)
    (candidateLaw :
      LinearPlebanskiLorentzActionGeneratedSpatialVelocityLaw current
        candidate) :
    candidate =
      currentCanonicalFullActionLorentzUnitConnectionVelocity source current :=
  linearPlebanskiLorentzActionGeneratedSpatialVelocityLaw_unique current
    candidate
    (currentCanonicalFullActionLorentzUnitConnectionVelocity source current)
    candidateLaw
    (currentCanonicalFullActionLorentzUnitConnection_satisfies_actionLaw
      source current)

/-- Read the momentum velocity from the already generated unit update. -/
def currentCanonicalFullActionLorentzUnitMomentumVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → Real :=
  fun space direction =>
    (currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate source
          current).spatialBFMomentumEvaluation space direction -
      (currentCanonicalFullActionLorentzCanonicalPhaseState source
          current).spatialBFMomentumEvaluation space direction

theorem currentCanonicalFullActionLorentzUnitMomentumVelocity_eq
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzUnitMomentumVelocity source current =
      currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
        current := by
  funext space direction
  simp [currentCanonicalFullActionLorentzUnitMomentumVelocity,
    currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate,
    currentCanonicalFullActionLorentzCanonicalPhaseUpdate,
    currentCanonicalFullActionLorentzCanonicalPhaseVelocity]

theorem currentCanonicalFullActionLorentzUnitMomentum_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw source current
      (currentCanonicalFullActionLorentzUnitMomentumVelocity source current) := by
  rw [currentCanonicalFullActionLorentzUnitMomentumVelocity_eq]
  exact
    currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_satisfies_actionLaw
      source current

/-- Genuine faithful zero fiber of the complete Lorentz phase velocity: the
unit update is fixed exactly when both the connection and BF-momentum velocity
fields vanish. -/
theorem currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate_eq_initial_iff
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate source current =
          currentCanonicalFullActionLorentzCanonicalPhaseState source current ↔
      currentCanonicalFullActionLorentzCanonicalPhaseVelocity source current =
        zeroLorentzCanonicalPhaseVelocity := by
  constructor
  · intro updateFixed
    apply StageNineLorentzCanonicalPhaseState.ext
    · funext space direction internalPair
      have componentFixed := congrArg
        (fun phase : StageNineLorentzCanonicalPhaseState =>
          phase.spatialConnection space direction internalPair)
        updateFixed
      simp only [currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate,
        currentCanonicalFullActionLorentzCanonicalPhaseUpdate, one_mul]
        at componentFixed
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialConnection space direction internalPair +
            (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
              current).spatialConnection space direction internalPair =
          (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialConnection space direction internalPair
        at componentFixed
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
          current).spatialConnection space direction internalPair = 0
      linarith
    · funext space direction
      have componentFixed := congrArg
        (fun phase : StageNineLorentzCanonicalPhaseState =>
          phase.spatialBFMomentumEvaluation space direction)
        updateFixed
      simp only [currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate,
        currentCanonicalFullActionLorentzCanonicalPhaseUpdate, one_mul]
        at componentFixed
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialBFMomentumEvaluation space direction +
            (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
              current).spatialBFMomentumEvaluation space direction =
          (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialBFMomentumEvaluation space direction
        at componentFixed
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
          current).spatialBFMomentumEvaluation space direction = 0
      linarith
  · intro velocityZero
    apply StageNineLorentzCanonicalPhaseState.ext
    · funext space direction internalPair
      have componentZero := congrArg
        (fun phase : StageNineLorentzCanonicalPhaseState =>
          phase.spatialConnection space direction internalPair)
        velocityZero
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
          current).spatialConnection space direction internalPair = 0
        at componentZero
      simp only [currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate,
        currentCanonicalFullActionLorentzCanonicalPhaseUpdate, one_mul]
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialConnection space direction internalPair +
            (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
              current).spatialConnection space direction internalPair =
          (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialConnection space direction internalPair
      rw [componentZero]
      simp
    · funext space direction
      have componentZero := congrArg
        (fun phase : StageNineLorentzCanonicalPhaseState =>
          phase.spatialBFMomentumEvaluation space direction)
        velocityZero
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
          current).spatialBFMomentumEvaluation space direction = 0
        at componentZero
      simp only [currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate,
        currentCanonicalFullActionLorentzCanonicalPhaseUpdate, one_mul]
      change
        (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialBFMomentumEvaluation space direction +
            (currentCanonicalFullActionLorentzCanonicalPhaseVelocity source
              current).spatialBFMomentumEvaluation space direction =
          (currentCanonicalFullActionLorentzCanonicalPhaseState source
              current).spatialBFMomentumEvaluation space direction
      rw [componentZero]
      simp

/-! ## No-premise producer authority -/

/-- Generic authority for the C3h188 Lorentz dual response.  Its theorem
mouth contains only the proof-free source and current Cauchy state.  The law
records constructor soundness, uniqueness, and the exact unit fixed-point
fiber; none of these fields is counted as an independent EL closure. -/
structure StageNineCurrentCanonicalFullActionLorentzDualResponseLaw
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) : Prop where
  gravityConnectionOriginFaithful : ∀ space,
    (currentCanonicalGravityPreservingActual source current
        space).gravityConnection 0 =
      current.gravityConnection space
  gravityCurvatureGenerated : ∀ space,
    holonomicGravityCurvature
        (currentCanonicalGravityPreservingActual source current space) 0 =
      linearPlebanskiActionGeneratedGravityCurvature current space
  temporalMatterFaithfulZeroFiber : ∀ space,
    currentCanonicalGravityPreservingTemporalMatterActual source current
          space =
        currentCanonicalGravityPreservingP286Actual source current space ↔
      matterTemporalDiracYukawaFirstGermResidual source
          (currentCanonicalGravityPreservingP286Actual source current space) =
        0
  completeMatterFaithfulZeroFiber : ∀ space,
    currentCanonicalGravityPreservingActual source current space =
          currentCanonicalGravityPreservingTemporalMatterActual source current
            space ↔
      matterCompleteDiracYukawaFirstGermResidual source
          (currentCanonicalGravityPreservingTemporalMatterActual source current
            space) =
        0
  momentumActionLaw :
    CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw source current
      (currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
        current)
  momentumActionUnique : ∀ candidate,
    CurrentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw source current
        candidate →
      candidate =
        currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
          current
  connectionActionLaw :
    LinearPlebanskiLorentzActionGeneratedSpatialVelocityLaw current
      (currentCanonicalFullActionLorentzUnitConnectionVelocity source current)
  connectionActionUnique : ∀ candidate,
    LinearPlebanskiLorentzActionGeneratedSpatialVelocityLaw current candidate →
      candidate =
        currentCanonicalFullActionLorentzUnitConnectionVelocity source current
  zeroTimeIdentity :
    currentCanonicalFullActionLorentzCanonicalPhaseUpdate source current 0 =
      currentCanonicalFullActionLorentzCanonicalPhaseState source current
  unitFaithfulZeroFiber :
    currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate source current =
          currentCanonicalFullActionLorentzCanonicalPhaseState source current ↔
      currentCanonicalFullActionLorentzCanonicalPhaseVelocity source current =
        zeroLorentzCanonicalPhaseVelocity

theorem currentCanonicalFullActionLorentzDualResponse_realizes
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    StageNineCurrentCanonicalFullActionLorentzDualResponseLaw source current := by
  exact
    { gravityConnectionOriginFaithful :=
        currentCanonicalGravityPreservingActual_gravityConnection_origin
          source current
      gravityCurvatureGenerated :=
        currentCanonicalGravityPreservingActual_curvature_origin source current
      temporalMatterFaithfulZeroFiber :=
        currentCanonicalGravityPreservingTemporalMatterActual_faithfulZeroFiber
          source current
      completeMatterFaithfulZeroFiber :=
        currentCanonicalGravityPreservingActual_faithfulCompleteZeroFiber
          source current
      momentumActionLaw :=
        currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_satisfies_actionLaw
          source current
      momentumActionUnique := fun candidate candidateLaw =>
        currentCanonicalFullActionLorentzSpatialBFMomentumVelocityLaw_unique
          source current candidate
            (currentCanonicalFullActionLorentzSpatialBFMomentumVelocity source
              current)
          candidateLaw
          (currentCanonicalFullActionLorentzSpatialBFMomentumVelocity_satisfies_actionLaw
            source current)
      connectionActionLaw :=
        currentCanonicalFullActionLorentzUnitConnection_satisfies_actionLaw
          source current
      connectionActionUnique := fun candidate candidateLaw =>
        currentCanonicalFullActionLorentzUnitConnectionVelocityLaw_unique
          source current candidate candidateLaw
      zeroTimeIdentity :=
        currentCanonicalFullActionLorentzCanonicalPhaseUpdate_zero source current
      unitFaithfulZeroFiber :=
        currentCanonicalFullActionLorentzCanonicalPhaseUnitUpdate_eq_initial_iff
          source current }

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCanonicalFullActionLorentzDualResponse
