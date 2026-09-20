import H0mework.Physics.GaugeAction.P286ActionCanonicalPairUpdate
import H0mework.Physics.Lorentz.LorentzConnectionPointwiseEquation

/-!
# S9-C3h95: Lorentz BF canonical-pair update

C3h93 already lets the gravity multiplier and auxiliary actions generate
`B = II⁺(e)` and `Fω = ⋆ᵢB`, then realizes that curvature by an actual
Lorentz-skew primitive connection germ.  That germ remains a pointwise
curvature-existence witness; its normalized affine half split is not used to
choose a Cauchy velocity.  This module instead combines the action curvature
with the actual spatial jet already present in the Cauchy state.

The construction is action-first:

* the spatial Lorentz-connection velocity is generated from
  `F₀ᵢ = ∂₀ωᵢ - ∂ᵢω₀ + [ω₀,ωᵢ]` using the actual Cauchy spatial derivative;
* the Lorentz BF momentum is evaluated on every spatial bivector one-form;
* its velocity is the action-owned algebraic BF/spin coefficient minus the
  three derivatives of the coherent slice momentum field;
* gravity and P286 canonical pairs are advanced by one common time argument.

No residual coordinate, response inverse, quotient representative, endpoint,
shell witness, or equation receipt participates in the update.  As in C3h94,
this is an input-state first-order Cauchy update, not yet an ODE integral
curve or a full matter/coframe development.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineLorentzActionCanonicalPairUpdate

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineEnrichedProofFreeSource
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineLorentzConnectionMomentumRegularity
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeConnectionPointwiseEquation

noncomputable section

set_option autoImplicit false

/-! ## Lorentz `3+1` action split -/

/-- Six Lorentz-bivector coordinates for each of the three spatial
connection components. -/
abbrev LorentzSpatialBivectorDirection :=
  Fin 3 → Fin 6 → ℝ

/-- Canonical inclusion into a Lorentz bivector one-form with zero temporal
component. -/
def canonicalLorentzSpatialBivectorOneForm
    (direction : LorentzSpatialBivectorDirection) :
    LorentzBivectorOneForm :=
  fun formDirection =>
    Fin.cases (0 : Fin 6 → ℝ) direction formDirection

@[simp] theorem canonicalLorentzSpatialBivectorOneForm_time
    (direction : LorentzSpatialBivectorDirection) :
    canonicalLorentzSpatialBivectorOneForm direction
        canonicalLorentzianTimeDirection = 0 := by
  rfl

@[simp] theorem canonicalLorentzSpatialBivectorOneForm_spatial
    (direction : LorentzSpatialBivectorDirection)
    (index : Fin 3) :
    canonicalLorentzSpatialBivectorOneForm direction index.succ =
      direction index := by
  rfl

/-- Time contribution to the Lorentz BF-momentum divergence. -/
def lorentzConnectionTemporalBFMomentumDerivative
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) : ℝ :=
  fieldDirectionalDerivative
    (lorentzConnectionBFDifferentialMomentum configuration
      (lorentzConnectionExteriorDerivativeDirection
        canonicalLorentzianTimeDirection direction))
    point canonicalLorentzianTimeDirection

def lorentzConnectionSpatialBFMomentumDerivative
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint)
    (derivativeDirection : Fin 3) : ℝ :=
  fieldDirectionalDerivative
    (lorentzConnectionBFDifferentialMomentum configuration
      (lorentzConnectionExteriorDerivativeDirection
        derivativeDirection.succ direction))
    point derivativeDirection.succ

/-- Three spatial contributions to the same action-owned divergence, kept as
the finite sum of its named axis derivatives. -/
def lorentzConnectionSpatialBFMomentumDivergence
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) : ℝ :=
  ∑ derivativeDirection : Fin 3,
    lorentzConnectionSpatialBFMomentumDerivative configuration direction point
      derivativeDirection

theorem lorentzConnectionSpatialBFMomentumDivergence_eq_sum
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionSpatialBFMomentumDivergence configuration direction
        point =
      ∑ derivativeDirection : Fin 3,
        lorentzConnectionSpatialBFMomentumDerivative configuration direction
          point derivativeDirection := by
  rfl

theorem lorentzConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial
    (configuration : StageNineHolonomicConfiguration)
    (direction : LorentzBivectorOneForm)
    (point : BasePoint) :
    lorentzConnectionBFDifferentialMomentumDivergence configuration
        direction point =
      lorentzConnectionTemporalBFMomentumDerivative configuration
          direction point +
        lorentzConnectionSpatialBFMomentumDivergence configuration
          direction point := by
  simp [lorentzConnectionBFDifferentialMomentumDivergence,
    lorentzConnectionTemporalBFMomentumDerivative,
    lorentzConnectionSpatialBFMomentumDerivative,
    lorentzConnectionSpatialBFMomentumDivergence,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three,
    Fin.sum_univ_four]
  ring

/-- Lorentz BF-momentum evolution law generated by the connection action on
spatial connection directions. -/
def CanonicalLorentzSpatialMomentumEvolutionAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  ∀ direction : LorentzBivectorOneForm,
    direction canonicalLorentzianTimeDirection = 0 →
      lorentzConnectionTemporalBFMomentumDerivative configuration
          direction point =
        lorentzConnectionAlgebraicSpinCurrentCoefficient source
            configuration direction point -
          lorentzConnectionSpatialBFMomentumDivergence configuration
            direction point

theorem canonicalLorentzConnectionPointwiseEquation_implies_spatialMomentumEvolution
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalLorentzConnectionPointwiseEquation source
      configuration)
    (point : BasePoint) :
    CanonicalLorentzSpatialMomentumEvolutionAt source configuration
      point := by
  intro direction _
  have pointEquation :
      lorentzConnectionEulerLagrangeCoefficient source configuration
          direction point = 0 := by
    simpa using congrFun (equation direction) point
  rw [lorentzConnectionEulerLagrangeCoefficient,
    lorentzConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial]
      at pointEquation
  linarith

/-! ## Action-generated Lorentz connection velocity -/

/-- Lowered spatial connection coordinates on the primitive Cauchy slice. -/
def sourceActionGeneratedLorentzSpatialConnectionCoordinate
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ :=
  fun space direction internalPair =>
    minkowskiInternalSign (pairFirst internalPair) *
      state.gravityConnection space direction.succ
        (pairFirst internalPair) (pairSecond internalPair)

/-- Spatial derivative of a lowered Lorentz-connection coordinate on the
actual primitive Cauchy slice. -/
def cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → LorentzianIndex → Fin 6 → ℝ :=
  fun space derivativeDirection formDirection internalPair =>
    fderiv ℝ
      (fun candidate =>
        minkowskiInternalSign (pairFirst internalPair) *
          state.gravityConnection candidate formDirection
            (pairFirst internalPair) (pairSecond internalPair))
      space
      (canonicalSpatialCoordinateDirection derivativeDirection)

/-- Lowered commutator coordinate `[ω_first,ω_second]` on the fixed Cauchy
slice. -/
def cauchyLoweredLorentzConnectionBracketCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (first second : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  minkowskiInternalSign (pairFirst internalPair) *
    ∑ middle : LorentzianIndex,
      (state.gravityConnection space first
          (pairFirst internalPair) middle *
        state.gravityConnection space second middle
          (pairSecond internalPair) -
       state.gravityConnection space second
          (pairFirst internalPair) middle *
        state.gravityConnection space first middle
          (pairSecond internalPair))

/-- Actual temporal-spatial curvature coordinate determined by a candidate
Cauchy velocity and the fixed primitive spatial jet. -/
def lorentzTemporalSpatialCurvatureCoordinate
    (state : StageNineCauchyState)
    (velocity : StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) : ℝ :=
  velocity space direction internalPair -
      cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate state
        space direction canonicalLorentzianTimeDirection internalPair +
    cauchyLoweredLorentzConnectionBracketCoordinate state space
      canonicalLorentzianTimeDirection direction.succ internalPair

/-- Lorentz spatial-connection velocity generated by the actual gravity
auxiliary action and the existing Cauchy spatial jet.  No source coefficient,
candidate velocity, residual, or affine half-split is supplied. -/
def actionGeneratedLorentzSpatialConnectionVelocity
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ :=
  fun space direction internalPair =>
    actionGeneratedGravityCurvature state space internalPair
        (temporalSpatialPair direction) +
      cauchyLoweredLorentzSpatialConnectionDerivativeCoordinate state
        space direction canonicalLorentzianTimeDirection internalPair -
      cauchyLoweredLorentzConnectionBracketCoordinate state space
        canonicalLorentzianTimeDirection direction.succ internalPair

/-- Downstream acceptance predicate for the Lorentz connection velocity. -/
def LorentzActionGeneratedSpatialVelocityLaw
    (state : StageNineCauchyState)
    (velocity : StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ) : Prop :=
  ∀ space direction internalPair,
    lorentzTemporalSpatialCurvatureCoordinate state velocity space direction
        internalPair =
      actionGeneratedGravityCurvature state space internalPair
        (temporalSpatialPair direction)

theorem actionGeneratedLorentzSpatialConnectionVelocity_satisfies_actionLaw
    (state : StageNineCauchyState) :
    LorentzActionGeneratedSpatialVelocityLaw state
      (actionGeneratedLorentzSpatialConnectionVelocity state) := by
  intro space direction internalPair
  unfold lorentzTemporalSpatialCurvatureCoordinate
    actionGeneratedLorentzSpatialConnectionVelocity
  abel

/-- The lowered temporal-spatial curvature law uniquely fixes the connection
velocity over a fixed Cauchy state.  Hence the producer makes no hidden
branch choice. -/
theorem lorentzActionGeneratedSpatialVelocityLaw_unique
    (state : StageNineCauchyState)
    (first second : StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ)
    (firstLaw : LorentzActionGeneratedSpatialVelocityLaw state first)
    (secondLaw : LorentzActionGeneratedSpatialVelocityLaw state second) :
    first = second := by
  funext space direction internalPair
  have firstEquation := firstLaw space direction internalPair
  have secondEquation := secondLaw space direction internalPair
  unfold lorentzTemporalSpatialCurvatureCoordinate at firstEquation secondEquation
  linarith

/-! ## Coherent Lorentz BF momentum field -/

/-- Action-native Lorentz BF momentum evaluation for one spacetime
derivative direction.  Varying `space` varies the source/Cauchy-generated
local lift, producing one coherent field on the whole spatial slice. -/
def sourceActionGeneratedLorentzBFMomentumEvaluation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (derivativeDirection : LorentzianIndex) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → ℝ :=
  fun space direction =>
    let actual :=
      sourceActionGeneratedGravityGaugeLocalActualLift source state space
    lorentzConnectionBFDifferentialMomentum actual
      (lorentzConnectionExteriorDerivativeDirection
        derivativeDirection
        (canonicalLorentzSpatialBivectorOneForm direction))
      0

/-- Complete Lorentz BF momentum conjugate to spatial connection directions:
the time-direction member of the coherent momentum field. -/
def sourceActionGeneratedLorentzSpatialBFMomentumEvaluation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → ℝ :=
  sourceActionGeneratedLorentzBFMomentumEvaluation source state
    canonicalLorentzianTimeDirection

/-- Genuine spatial divergence of the coherent slice momentum field.  The
derivative is taken across `StageNineSpatialPoint`, not inside a separate
constant local germ at each point. -/
def sourceActionGeneratedLorentzSpatialBFMomentumDivergence
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) : ℝ :=
  ∑ derivativeDirection : Fin 3,
    fderiv ℝ
      (sourceActionGeneratedLorentzBFMomentumEvaluation source state
        derivativeDirection.succ · direction)
      space
      (canonicalSpatialCoordinateDirection derivativeDirection)

/-- Action-generated Lorentz BF-momentum velocity. -/
def sourceActionGeneratedLorentzSpatialBFMomentumVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → ℝ :=
  fun space direction =>
    let actual :=
      sourceActionGeneratedGravityGaugeLocalActualLift source state space
    let fullDirection :=
      canonicalLorentzSpatialBivectorOneForm direction
    lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
        fullDirection 0 -
      sourceActionGeneratedLorentzSpatialBFMomentumDivergence
        source state space direction

/-! ## Action-generated Lorentz canonical pair -/

@[ext] structure StageNineLorentzCanonicalPhaseState where
  spatialConnection :
    StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ
  spatialBFMomentumEvaluation :
    StageNineSpatialPoint → LorentzSpatialBivectorDirection → ℝ

def sourceActionGeneratedLorentzCanonicalPhaseState
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection :=
    sourceActionGeneratedLorentzSpatialConnectionCoordinate state
  spatialBFMomentumEvaluation :=
    sourceActionGeneratedLorentzSpatialBFMomentumEvaluation source state

def sourceActionGeneratedLorentzCanonicalPhaseVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection :=
    actionGeneratedLorentzSpatialConnectionVelocity state
  spatialBFMomentumEvaluation :=
    sourceActionGeneratedLorentzSpatialBFMomentumVelocity source state

/-- Common local Lorentz connection/BF-momentum update. -/
def sourceActionGeneratedLorentzCanonicalPhaseUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineLorentzCanonicalPhaseState where
  spatialConnection := fun space direction internalPair =>
    (sourceActionGeneratedLorentzCanonicalPhaseState source
      state).spatialConnection space direction internalPair +
      time *
        (sourceActionGeneratedLorentzCanonicalPhaseVelocity source
          state).spatialConnection space direction internalPair
  spatialBFMomentumEvaluation := fun space direction =>
    (sourceActionGeneratedLorentzCanonicalPhaseState source
      state).spatialBFMomentumEvaluation space direction +
      time *
        (sourceActionGeneratedLorentzCanonicalPhaseVelocity source
          state).spatialBFMomentumEvaluation space direction

@[simp] theorem sourceActionGeneratedLorentzCanonicalPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedLorentzCanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedLorentzCanonicalPhaseState source state := by
  apply StageNineLorentzCanonicalPhaseState.ext
  · funext space direction internalPair
    simp [sourceActionGeneratedLorentzCanonicalPhaseUpdate]
  · funext space direction
    simp [sourceActionGeneratedLorentzCanonicalPhaseUpdate]

theorem sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionIncrement
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6) :
    (sourceActionGeneratedLorentzCanonicalPhaseUpdate source 1
          state).spatialConnection space direction internalPair -
        (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialConnection space direction internalPair =
      actionGeneratedLorentzSpatialConnectionVelocity state
        space direction internalPair := by
  simp [sourceActionGeneratedLorentzCanonicalPhaseUpdate,
    sourceActionGeneratedLorentzCanonicalPhaseVelocity]

/-- Connection velocity read from the unit update.  It is a readout of the
already generated update, not a separately supplied candidate. -/
def sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → Fin 6 → ℝ :=
  fun space direction internalPair =>
    (sourceActionGeneratedLorentzCanonicalPhaseUpdate source 1
          state).spatialConnection space direction internalPair -
      (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialConnection space direction internalPair

theorem sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity_eq
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
        source state =
      actionGeneratedLorentzSpatialConnectionVelocity state := by
  funext space direction internalPair
  exact sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionIncrement
    source state space direction internalPair

/-- The connection component of the unit update satisfies the actual
temporal-spatial Lorentz curvature law. -/
theorem sourceActionGeneratedLorentzCanonicalPhaseUnitConnection_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    LorentzActionGeneratedSpatialVelocityLaw state
      (sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
        source state) := by
  rw [sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity_eq]
  exact
    actionGeneratedLorentzSpatialConnectionVelocity_satisfies_actionLaw state

theorem sourceActionGeneratedLorentzCanonicalPhaseUnitMomentum_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzSpatialBivectorDirection) :
    (sourceActionGeneratedLorentzCanonicalPhaseUpdate source 1
          state).spatialBFMomentumEvaluation space direction -
        (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction =
      let actual :=
        sourceActionGeneratedGravityGaugeLocalActualLift source state space
      let fullDirection :=
        canonicalLorentzSpatialBivectorOneForm direction
      lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
          fullDirection 0 -
        sourceActionGeneratedLorentzSpatialBFMomentumDivergence
          source state space direction := by
  simp [sourceActionGeneratedLorentzCanonicalPhaseUpdate,
    sourceActionGeneratedLorentzCanonicalPhaseState,
    sourceActionGeneratedLorentzCanonicalPhaseVelocity,
    sourceActionGeneratedLorentzSpatialBFMomentumVelocity]

/-- The same generated actual lift supplies pointwise curvature existence,
while the common phase update satisfies both spatial connection and
BF-momentum action laws.  The temporal Lorentz test/Gauss constraint remains
a downstream acceptance condition and is intentionally not claimed here. -/
theorem sourceActionGeneratedLorentzCanonicalPhaseUnitUpdate_satisfies_spatialActionLaws
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    (∀ space,
      holonomicGravityCurvature
          (sourceActionGeneratedGravityGaugeLocalActualLift source state space)
          0 =
        actionGeneratedGravityCurvature state space) ∧
      LorentzActionGeneratedSpatialVelocityLaw state
        (sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
          source state) ∧
      ∀ space direction,
        (sourceActionGeneratedLorentzCanonicalPhaseUpdate source 1
              state).spatialBFMomentumEvaluation space direction -
            (sourceActionGeneratedLorentzCanonicalPhaseState source
              state).spatialBFMomentumEvaluation space direction =
          let actual :=
            sourceActionGeneratedGravityGaugeLocalActualLift
              source state space
          let fullDirection :=
            canonicalLorentzSpatialBivectorOneForm direction
          lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
              fullDirection 0 -
            sourceActionGeneratedLorentzSpatialBFMomentumDivergence
              source state space direction := by
  exact
    ⟨fun space =>
        sourceActionGeneratedGravityGaugeLocalActualLift_gravityCurvature_origin
          source state space,
      sourceActionGeneratedLorentzCanonicalPhaseUnitConnection_satisfies_actionLaw
        source state,
      sourceActionGeneratedLorentzCanonicalPhaseUnitMomentum_satisfies_actionLaw
        source state⟩

/-! ## Positive and negative producer regressions -/

/-- Any nonzero action-generated Lorentz connection component makes the
common unit update nontrivial.  The witness is an output component of the
producer, not a supplied endpoint. -/
theorem sourceActionGeneratedLorentzCanonicalPhaseUnitUpdate_ne_initial_of_connectionComponent
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6)
    (componentNonzero :
      actionGeneratedLorentzSpatialConnectionVelocity state
        space direction internalPair ≠ 0) :
    sourceActionGeneratedLorentzCanonicalPhaseUpdate source 1 state ≠
      sourceActionGeneratedLorentzCanonicalPhaseState source state := by
  intro updateFixed
  have componentFixed := congrArg
    (fun phase : StageNineLorentzCanonicalPhaseState =>
      phase.spatialConnection space direction internalPair)
    updateFixed
  apply componentNonzero
  simpa [sourceActionGeneratedLorentzCanonicalPhaseUpdate,
    sourceActionGeneratedLorentzCanonicalPhaseVelocity] using componentFixed

/-- If both action-generated tangent components vanish, every local update
reduces to the derived initial Lorentz canonical phase point. -/
theorem sourceActionGeneratedLorentzCanonicalPhaseUpdate_eq_initial_of_velocity_zero
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (connectionVelocityZero :
      actionGeneratedLorentzSpatialConnectionVelocity state = 0)
    (momentumVelocityZero :
      sourceActionGeneratedLorentzSpatialBFMomentumVelocity source state =
        0) :
    sourceActionGeneratedLorentzCanonicalPhaseUpdate source time state =
      sourceActionGeneratedLorentzCanonicalPhaseState source state := by
  apply StageNineLorentzCanonicalPhaseState.ext
  · funext space direction internalPair
    have componentZero := congrFun
      (congrFun
        (congrFun connectionVelocityZero space) direction)
      internalPair
    change
      (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialConnection space direction internalPair +
        time *
          actionGeneratedLorentzSpatialConnectionVelocity state
            space direction internalPair =
      (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialConnection space direction internalPair
    rw [componentZero]
    simp
  · funext space direction
    have componentZero := congrFun
      (congrFun momentumVelocityZero space) direction
    change
      (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction +
        time *
          sourceActionGeneratedLorentzSpatialBFMomentumVelocity source state
            space direction =
      (sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction
    rw [componentZero]
    simp

/-! ## Common gravity--P286 canonical phase update -/

@[ext] structure StageNineGravityGaugeCanonicalPhaseState where
  p286 : StageNineP286CanonicalPhaseState
  lorentz : StageNineLorentzCanonicalPhaseState

def sourceActionGeneratedGravityGaugeCanonicalPhaseState
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineGravityGaugeCanonicalPhaseState where
  p286 := sourceActionGeneratedP286CanonicalPhaseState source state
  lorentz := sourceActionGeneratedLorentzCanonicalPhaseState source state

/-- One common physical-time argument advances both action-generated
canonical pairs. -/
def sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineGravityGaugeCanonicalPhaseState where
  p286 := sourceActionGeneratedP286CanonicalPhaseUpdate source time state
  lorentz :=
    sourceActionGeneratedLorentzCanonicalPhaseUpdate source time state

@[simp] theorem sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedGravityGaugeCanonicalPhaseState source state := by
  apply StageNineGravityGaugeCanonicalPhaseState.ext
  · exact sourceActionGeneratedP286CanonicalPhaseUpdate_zero source state
  · exact sourceActionGeneratedLorentzCanonicalPhaseUpdate_zero source state

/-- Gravity and P286 spatial action laws are satisfied by the two components
of one source/action-generated unit update.  This theorem does not claim the
temporal gauge/Lorentz constraints. -/
theorem sourceActionGeneratedGravityGaugeCanonicalPhaseUnitUpdate_satisfies_spatialActionLaws
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    (P286ActionGeneratedSpatialVelocityLaw source state
        (sourceActionGeneratedP286CanonicalPhaseUnitConnectionVelocity
          source state) ∧
      ∀ space direction,
        (sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate source 1
              state).p286.spatialBFMomentumEvaluation space direction -
            (sourceActionGeneratedGravityGaugeCanonicalPhaseState source
              state).p286.spatialBFMomentumEvaluation space direction =
          sourceActionGeneratedP286SpatialBFMomentumVelocity
            source state space direction) ∧
      (∀ space,
        holonomicGravityCurvature
            (sourceActionGeneratedGravityGaugeLocalActualLift
              source state space)
            0 =
          actionGeneratedGravityCurvature state space) ∧
      LorentzActionGeneratedSpatialVelocityLaw state
        (sourceActionGeneratedLorentzCanonicalPhaseUnitConnectionVelocity
          source state) ∧
      ∀ space direction,
        (sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate source 1
              state).lorentz.spatialBFMomentumEvaluation space direction -
            (sourceActionGeneratedGravityGaugeCanonicalPhaseState source
              state).lorentz.spatialBFMomentumEvaluation space direction =
          let actual :=
            sourceActionGeneratedGravityGaugeLocalActualLift
              source state space
          let fullDirection :=
            canonicalLorentzSpatialBivectorOneForm direction
          lorentzConnectionAlgebraicSpinCurrentCoefficient source actual
              fullDirection 0 -
            sourceActionGeneratedLorentzSpatialBFMomentumDivergence
              source state space direction := by
  exact
    ⟨by
        simpa [sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate,
          sourceActionGeneratedGravityGaugeCanonicalPhaseState,
          sourceActionGeneratedP286SpatialBFMomentumVelocity] using
          (sourceActionGeneratedP286CanonicalPhaseUnitUpdate_satisfies_actionSystem
            source state),
      sourceActionGeneratedLorentzCanonicalPhaseUnitUpdate_satisfies_spatialActionLaws
        source state⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineLorentzActionCanonicalPairUpdate
