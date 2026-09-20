import H0mework.Physics.Gauge.GravityGaugeActionLocalActualLift

/-!
# S9-C3h94: action-native P286 canonical-pair update

C3h90 generated the spatial-connection velocity from the P286 auxiliary
action.  C3h87 identified the complementary P286 connection equation as the
time evolution law of the BF momentum dual to spatial connection directions.
This module puts those two action outputs on one spatial-slice carrier and
constructs their common local update before consulting any residual.

For every spatial point the construction proceeds in this order:

* C3h93 supplies the source/action-generated primitive local actual lift;
* its BF differential momentum is evaluated on every spatial connection
  direction and assembled into one spatial field;
* the actual connection Euler--Lagrange integrand supplies
  `algebraic current - spatial BF divergence`, where the divergence is the
  genuine spatial Fréchet derivative of that assembled field;
* the connection velocity and BF-momentum velocity are advanced
  simultaneously by the same physical-time increment.

The momentum field is kept as its complete evaluation function on spatial
directions.  No basis, Riesz inverse, response preimage, quotient
representative, endpoint, or equation receipt selects it.  A future module
may bundle the already action-linear evaluation as a `Module.Dual`; that
packaging is not used to generate this update.

This is the canonical first-order local Cauchy update generated at the input
state.  It is not yet an integral curve, semigroup law, auxiliary
reconstruction, or full gravity--gauge--matter development.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286ActionCanonicalPairUpdate

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-! ## Canonical spatial phase carrier -/

/-- A variation of the three spatial P286 connection components at one
spatial point. -/
abbrev P286SpatialGaugeDirection :=
  Fin 3 → P286CoordinateCarrier

/-- Embed a spatial P286 direction into the already fixed `3+1` one-form
split.  Its time component is definitionally zero. -/
def canonicalP286SpatialGaugeOneForm
    (direction : P286SpatialGaugeDirection) : P286GaugeOneForm :=
  fun formDirection =>
    Fin.cases (0 : P286CoordinateCarrier) direction formDirection

@[simp] theorem canonicalP286SpatialGaugeOneForm_time
    (direction : P286SpatialGaugeDirection) :
    canonicalP286SpatialGaugeOneForm direction
        canonicalLorentzianTimeDirection = 0 := by
  rfl

@[simp] theorem canonicalP286SpatialGaugeOneForm_spatial
    (direction : P286SpatialGaugeDirection)
    (index : Fin 3) :
    canonicalP286SpatialGaugeOneForm direction index.succ =
      direction index := by
  rfl

/-- Derived P286 canonical phase data on a whole spatial slice.

`spatialBFMomentumEvaluation` replaces the canonical momentum role of the
corresponding auxiliary components in this derived chart; it is not an
additional primitive source slot. -/
@[ext] structure StageNineP286CanonicalPhaseState where
  spatialConnection :
    StageNineSpatialPoint → Fin 3 → P286CoordinateCarrier
  spatialBFMomentumEvaluation :
    StageNineSpatialPoint → P286SpatialGaugeDirection → ℝ

/-! ## Action-generated initial point and tangent -/

/-- Spatial connection coordinates read from primitive Cauchy data. -/
def sourceActionGeneratedP286SpatialConnectionCoordinate
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → P286CoordinateCarrier :=
  fun space direction =>
    p286CoordinateEquiv
      (state.gaugeConnection space direction.succ)

/-- Action-native BF momentum evaluation for one spacetime derivative
direction.  Varying `space` varies the source/Cauchy-generated local lift, so
this is one coherent field on the whole canonical slice. -/
def sourceActionGeneratedP286BFMomentumEvaluation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (derivativeDirection : LorentzianIndex) :
    StageNineSpatialPoint → P286SpatialGaugeDirection → ℝ :=
  fun space direction =>
    let actual :=
      sourceActionGeneratedGravityGaugeLocalActualLift source state space
    p286GaugeConnectionBFDifferentialMomentum actual
      (p286GaugeExteriorDerivativeDirection
        derivativeDirection
        (canonicalP286SpatialGaugeOneForm direction))
      0

/-- The canonical momentum conjugate to spatial P286 connection components
is the time-direction member of the coherent BF momentum field. -/
def sourceActionGeneratedP286SpatialBFMomentumEvaluation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → P286SpatialGaugeDirection → ℝ :=
  sourceActionGeneratedP286BFMomentumEvaluation source state
    canonicalLorentzianTimeDirection

/-- Initial P286 canonical phase point derived from primitive source/Cauchy
data and the actual action lift. -/
def sourceActionGeneratedP286CanonicalPhaseState
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineP286CanonicalPhaseState where
  spatialConnection :=
    sourceActionGeneratedP286SpatialConnectionCoordinate state
  spatialBFMomentumEvaluation :=
    sourceActionGeneratedP286SpatialBFMomentumEvaluation source state

/-- Coordinate form of the C3h90 action-generated connection velocity. -/
def sourceActionGeneratedP286SpatialConnectionCoordinateVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → P286CoordinateCarrier :=
  fun space direction =>
    p286CoordinateEquiv
      (sourceGeneratedP286SpatialConnectionVelocity source state
        space direction)

/-- The actual P286 connection action generates the BF-momentum velocity:
algebraic current minus the three spatial BF-momentum derivatives.

This is the right-hand side of C3h87, not the Euler--Lagrange residual and not
an inverse image of it. -/
def sourceActionGeneratedP286SpatialBFMomentumDivergence
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) : ℝ :=
  ∑ derivativeDirection : Fin 3,
    fderiv ℝ
      (sourceActionGeneratedP286BFMomentumEvaluation source state
        derivativeDirection.succ · direction)
      space
      (canonicalSpatialCoordinateDirection derivativeDirection)

def sourceActionGeneratedP286SpatialBFMomentumVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → P286SpatialGaugeDirection → ℝ :=
  fun space direction =>
    let actual :=
      sourceActionGeneratedGravityGaugeLocalActualLift source state space
    let fullDirection :=
      canonicalP286SpatialGaugeOneForm direction
    p286GaugeConnectionAlgebraicCurrentCoefficient source actual
        fullDirection 0 -
      sourceActionGeneratedP286SpatialBFMomentumDivergence
        source state space direction

/-- Full simultaneous P286 canonical-pair tangent generated from source,
primitive Cauchy data, and the actual action. -/
def sourceActionGeneratedP286CanonicalPhaseVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineP286CanonicalPhaseState where
  spatialConnection :=
    sourceActionGeneratedP286SpatialConnectionCoordinateVelocity source state
  spatialBFMomentumEvaluation :=
    sourceActionGeneratedP286SpatialBFMomentumVelocity source state

/-! ## Source/action-generated common update -/

/-- Canonical local physical-time update of the P286 connection/BF-momentum
pair.  Both components use one time increment and one action-generated
tangent; no endpoint is supplied. -/
def sourceActionGeneratedP286CanonicalPhaseUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineP286CanonicalPhaseState where
  spatialConnection := fun space direction =>
    (sourceActionGeneratedP286CanonicalPhaseState source
      state).spatialConnection space direction +
      time •
        (sourceActionGeneratedP286CanonicalPhaseVelocity source
          state).spatialConnection space direction
  spatialBFMomentumEvaluation := fun space direction =>
    (sourceActionGeneratedP286CanonicalPhaseState source
      state).spatialBFMomentumEvaluation space direction +
      time *
        (sourceActionGeneratedP286CanonicalPhaseVelocity source
          state).spatialBFMomentumEvaluation space direction

@[simp] theorem sourceActionGeneratedP286CanonicalPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedP286CanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedP286CanonicalPhaseState source state := by
  apply StageNineP286CanonicalPhaseState.ext <;>
    funext space direction <;>
    simp [sourceActionGeneratedP286CanonicalPhaseUpdate]

theorem sourceActionGeneratedP286CanonicalPhaseUpdate_connection
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    (sourceActionGeneratedP286CanonicalPhaseUpdate source time
      state).spatialConnection space direction =
      p286CoordinateEquiv
          (state.gaugeConnection space direction.succ) +
        time •
          p286CoordinateEquiv
            (sourceGeneratedP286SpatialConnectionVelocity source state
              space direction) :=
  rfl

theorem sourceActionGeneratedP286CanonicalPhaseUpdate_momentum
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    (sourceActionGeneratedP286CanonicalPhaseUpdate source time
      state).spatialBFMomentumEvaluation space direction =
      sourceActionGeneratedP286SpatialBFMomentumEvaluation source state
          space direction +
        time *
          sourceActionGeneratedP286SpatialBFMomentumVelocity source state
            space direction :=
  rfl

/-- The unit update recovers exactly the C3h90 connection velocity from its
connection-coordinate increment. -/
def sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → P286LieBlockData :=
  fun space direction =>
    p286CoordinateEquiv.symm
      ((sourceActionGeneratedP286CanonicalPhaseUpdate source 1
          state).spatialConnection space direction -
        (sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialConnection space direction)

theorem sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity_eq
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
        source state =
      sourceGeneratedP286SpatialConnectionVelocity source state := by
  funext space direction
  unfold sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
  rw [sourceActionGeneratedP286CanonicalPhaseUpdate_connection]
  rw [show
    (sourceActionGeneratedP286CanonicalPhaseState source
      state).spatialConnection space direction =
        p286CoordinateEquiv
          (state.gaugeConnection space direction.succ) by rfl]
  simp only [one_smul, add_sub_cancel_left,
    p286CoordinateEquiv.symm_apply_apply]

/-- The source/action-generated connection part of the common update obeys
the actual temporal-spatial curvature law. -/
theorem sourceActionGeneratedP286CanonicalPhaseUnitConnection_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    P286ActionGeneratedSpatialVelocityLaw source state
      (sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
        source state) := by
  rw [
    sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity_eq]
  exact
    sourceGeneratedP286SpatialConnectionVelocity_satisfies_actionLaw
      source state

/-- The momentum part of the same unit update obeys the full spatial
connection-action evolution law on every spatial point and every spatial
P286 direction. -/
theorem sourceActionGeneratedP286CanonicalPhaseUnitMomentum_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : P286SpatialGaugeDirection) :
    (sourceActionGeneratedP286CanonicalPhaseUpdate source 1
      state).spatialBFMomentumEvaluation space direction -
        (sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction =
      let actual :=
        sourceActionGeneratedGravityGaugeLocalActualLift source state space
      let fullDirection :=
        canonicalP286SpatialGaugeOneForm direction
      p286GaugeConnectionAlgebraicCurrentCoefficient source actual
          fullDirection 0 -
        sourceActionGeneratedP286SpatialBFMomentumDivergence
          source state space direction := by
  simp [sourceActionGeneratedP286CanonicalPhaseUpdate_momentum,
    sourceActionGeneratedP286CanonicalPhaseState,
    sourceActionGeneratedP286SpatialBFMomentumVelocity]

/-- One frontier theorem exposes both action laws on the same generated unit
update.  The connection increment and the complete BF-momentum evaluation
are not assembled from residual coordinates. -/
theorem sourceActionGeneratedP286CanonicalPhaseUnitUpdate_satisfies_actionSystem
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    P286ActionGeneratedSpatialVelocityLaw source state
        (sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
          source state) ∧
      ∀ space direction,
        (sourceActionGeneratedP286CanonicalPhaseUpdate source 1
          state).spatialBFMomentumEvaluation space direction -
            (sourceActionGeneratedP286CanonicalPhaseState source
              state).spatialBFMomentumEvaluation space direction =
          let actual :=
            sourceActionGeneratedGravityGaugeLocalActualLift
              source state space
          let fullDirection :=
            canonicalP286SpatialGaugeOneForm direction
          p286GaugeConnectionAlgebraicCurrentCoefficient source actual
              fullDirection 0 -
            sourceActionGeneratedP286SpatialBFMomentumDivergence
              source state space direction := by
  exact
    ⟨sourceActionGeneratedP286CanonicalPhaseUnitConnection_satisfies_actionLaw
        source state,
      sourceActionGeneratedP286CanonicalPhaseUnitMomentum_satisfies_actionLaw
        source state⟩

/-! ## Positive and negative controls -/

/-- Any nonzero generated connection component makes the common unit update
nontrivial.  The witness is an output component of the action producer, not
a caller-supplied endpoint. -/
theorem sourceActionGeneratedP286CanonicalPhaseUnitUpdate_ne_initial_of_connectionComponent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (componentNonzero :
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity source state
          space direction) ≠ 0) :
    sourceActionGeneratedP286CanonicalPhaseUpdate source 1 state ≠
      sourceActionGeneratedP286CanonicalPhaseState source state := by
  intro updateFixed
  have componentFixed := congrArg
    (fun phase : StageNineP286CanonicalPhaseState =>
      phase.spatialConnection space direction)
    updateFixed
  apply componentNonzero
  simpa [sourceActionGeneratedP286CanonicalPhaseUpdate_connection,
    sourceActionGeneratedP286CanonicalPhaseState,
    sourceActionGeneratedP286SpatialConnectionCoordinate] using
      componentFixed

/-- If both action-generated tangent components vanish, every local update
reduces to the derived initial canonical phase point. -/
theorem sourceActionGeneratedP286CanonicalPhaseUpdate_eq_initial_of_velocity_zero
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (connectionVelocityZero :
      sourceActionGeneratedP286SpatialConnectionCoordinateVelocity
        source state = 0)
    (momentumVelocityZero :
      sourceActionGeneratedP286SpatialBFMomentumVelocity source state = 0) :
    sourceActionGeneratedP286CanonicalPhaseUpdate source time state =
      sourceActionGeneratedP286CanonicalPhaseState source state := by
  apply StageNineP286CanonicalPhaseState.ext
  · funext space direction
    have componentZero := congrFun
      (congrFun connectionVelocityZero space) direction
    change
      (sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialConnection space direction +
        time •
          sourceActionGeneratedP286SpatialConnectionCoordinateVelocity
            source state space direction =
      (sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialConnection space direction
    rw [componentZero]
    simp
  · funext space direction
    have componentZero := congrFun
      (congrFun momentumVelocityZero space) direction
    change
      (sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction +
        time *
          sourceActionGeneratedP286SpatialBFMomentumVelocity source state
            space direction =
      (sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction
    rw [componentZero]
    simp

end

end
  SaturationMonoid.PhysicsCore.StageNineP286ActionCanonicalPairUpdate
