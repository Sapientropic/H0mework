import H0mework.Physics.Exterior.JointActionCanonicalPhaseUpdate

/-!
# S9-C3h100: source/action-generated joint canonical path law

C3h99 constructs one reduced canonical phase value for every physical-time
parameter.  This module proves the componentwise derivative law of that
fixed-initial-state affine Euler ray.  Its gravity, P286, and scalar
coordinates use the actual action tangents obtained in C3h94--C3h98; its
matter and dual coordinates remain the formal identity-coframe candidates
already isolated in C3h99.  The Lorentz and P286 BF momenta remain primary
canonical variables; they are not inverted into a coframe or auxiliary
endpoint.

The construction order is

```text
source + primitive Cauchy state + actual action
→ one joint canonical path U(t)
→ the componentwise derivative dU/dt
→ gravity/P286/scalar/matter/dual action-law acceptance
→ later residual/simplicity/coframe-stress acceptance.
```

No downstream equation/shell residual, target endpoint, preimage, range
certificate, Riesz inverse, quotient representative, or branch selector is
used to generate the path.  The coframe snapshot and temporal
multiplier/control data have zero path derivative because the present
canonical split has not yet generated their physical velocities.  In
particular, this theorem does not pretend that C3h95's three spatial
connection velocities determine a coframe path.  Nor does it claim
`dU/dt = V(U(t))`, an integral flow, a joint local actual lift, or a complete
synchronized response.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineJointActionCanonicalPhasePathLaw

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineJointActionCanonicalPhaseUpdate
open StageNineLorentzActionCanonicalPairUpdate
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineScalarActionCanonicalMomentumUpdate
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Elementary affine-path derivatives -/

theorem hasDerivAt_const_add_time_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (initial velocity : F) (time : ℝ) :
    HasDerivAt (fun candidate : ℝ => initial + candidate • velocity)
      velocity time := by
  have derivative :=
    (hasDerivAt_const time initial).add
      ((hasDerivAt_id time).smul_const velocity)
  convert derivative using 1
  · funext candidate
    rfl
  · simp

theorem hasDerivAt_matterCoordinate_const_add_time_smul
    (initial velocity : DiracExteriorMatterCarrier)
    (time : ℝ) :
    HasDerivAt
      (fun candidate : ℝ =>
        matterCoordinateEquiv (initial + candidate • velocity))
      (matterCoordinateEquiv velocity)
      time := by
  rw [show
    (fun candidate : ℝ =>
      matterCoordinateEquiv (initial + candidate • velocity)) =
        fun candidate =>
          matterCoordinateEquiv initial +
            candidate • matterCoordinateEquiv velocity by
    funext candidate
    rw [map_add]
    congr 1
    exact matterCoordinateEquiv.toLinearMap.map_smul_of_tower
      candidate velocity]
  exact hasDerivAt_const_add_time_smul
    (matterCoordinateEquiv initial)
    (matterCoordinateEquiv velocity)
    time

/-! ## Complete componentwise update law -/

/-- Exact derivative law of every coordinate carried by the reduced joint
canonical path.

The four leading fields record the currently unevolved snapshot/control
coordinates.  The gravity/P286/scalar fields differentiate to their
action-owned tangents.  The matter/dual fields characterize the formal
identity-coframe candidate derivatives packaged by C3h99; their actual
interpretation still requires the existing identity-coframe consumer gate. -/
structure StageNineJointCanonicalPathDerivativeLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ) : Prop where
  frozenCoframe :
    ∀ space internal coordinate,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).frozenCoframeSnapshot
              space internal coordinate)
        0 time
  simplicityMultiplier :
    ∀ space internalPair spacetimePair,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).gravitySimplicityMultiplier
              space internalPair spacetimePair)
        0 time
  temporalGravityConnection :
    ∀ space internalPair,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).temporalGravityConnection
              space internalPair)
        0 time
  temporalGaugeConnection :
    ∀ space,
      HasDerivAt
        (fun candidate =>
          p286CoordinateEquiv
            ((sourceActionGeneratedJointCanonicalPhaseUpdate
              source candidate state).temporalGaugeConnection space))
        0 time
  p286SpatialConnection :
    ∀ space direction,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).gravityGauge.p286.spatialConnection
              space direction)
        (sourceActionGeneratedP286SpatialConnectionCoordinateVelocity
          source state space direction)
        time
  p286SpatialBFMomentum :
    ∀ space direction,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).gravityGauge.p286
              |>.spatialBFMomentumEvaluation space direction)
        (sourceActionGeneratedP286SpatialBFMomentumVelocity
          source state space direction)
        time
  lorentzSpatialConnection :
    ∀ space direction internalPair,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).gravityGauge.lorentz.spatialConnection
              space direction internalPair)
        (actionGeneratedLorentzSpatialConnectionVelocity
          state space direction internalPair)
        time
  lorentzSpatialBFMomentum :
    ∀ space direction,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).gravityGauge.lorentz
              |>.spatialBFMomentumEvaluation space direction)
        (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source state space direction)
        time
  scalarCoordinate :
    ∀ space,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).scalar.scalarCoordinate space)
        (state.scalarVelocity space)
        time
  scalarTemporalMomentum :
    ∀ space direction,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).scalar.temporalMomentumEvaluation
              space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source state space direction)
        time
  matter :
    ∀ space,
      HasDerivAt
        (fun candidate =>
          matterCoordinateEquiv
            ((sourceActionGeneratedJointCanonicalPhaseUpdate
              source candidate state).matter space))
        (matterCoordinateEquiv
          (actionGeneratedMatterRawTimeVelocity state space))
        time
  conjugateMatterEvaluation :
    ∀ space matter,
      HasDerivAt
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).conjugateMatter space matter)
        (actionGeneratedConjugateMatterTimeDerivative state space matter)
        time

/-- Frontier theorem: the complete reduced canonical path is differentiated
before any residual is read.  Every gravity/P286/scalar derivative is
literally its source/action-generated tangent, while matter/dual expose the
formal identity-coframe candidate derivatives without upgrading them to
arbitrary-coframe actual dynamics. -/
theorem sourceActionGeneratedJointCanonicalPhasePath_hasGeneratedDerivative
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ) :
    StageNineJointCanonicalPathDerivativeLaw source state time := by
  refine
    { frozenCoframe := ?_,
      simplicityMultiplier := ?_,
      temporalGravityConnection := ?_,
      temporalGaugeConnection := ?_,
      p286SpatialConnection := ?_,
      p286SpatialBFMomentum := ?_,
      lorentzSpatialConnection := ?_,
      lorentzSpatialBFMomentum := ?_,
      scalarCoordinate := ?_,
      scalarTemporalMomentum := ?_,
      matter := ?_,
      conjugateMatterEvaluation := ?_ }
  · intro space internal coordinate
    exact hasDerivAt_const time
      (state.coframe space internal coordinate)
  · intro space internalPair spacetimePair
    exact hasDerivAt_const time
      (state.gravitySimplicityMultiplier
        space internalPair spacetimePair)
  · intro space internalPair
    exact hasDerivAt_const time
      (loweredLorentzConnectionCoefficient
        (state.gravityConnection space)
        canonicalLorentzianTimeDirection internalPair)
  · intro space
    exact hasDerivAt_const time
      (p286CoordinateEquiv
        (state.gaugeConnection space canonicalLorentzianTimeDirection))
  · intro space direction
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate,
      sourceActionGeneratedP286CanonicalPhaseUpdate,
      sourceActionGeneratedP286CanonicalPhaseVelocity] using
      hasDerivAt_const_add_time_smul
        ((sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialConnection space direction)
        (sourceActionGeneratedP286SpatialConnectionCoordinateVelocity
          source state space direction)
        time
  · intro space direction
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate,
      sourceActionGeneratedP286CanonicalPhaseUpdate,
      sourceActionGeneratedP286CanonicalPhaseVelocity,
      smul_eq_mul] using
      hasDerivAt_const_add_time_smul
        ((sourceActionGeneratedP286CanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction)
        (sourceActionGeneratedP286SpatialBFMomentumVelocity
          source state space direction)
        time
  · intro space direction internalPair
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate,
      sourceActionGeneratedLorentzCanonicalPhaseUpdate,
      sourceActionGeneratedLorentzCanonicalPhaseVelocity,
      smul_eq_mul] using
      hasDerivAt_const_add_time_smul
        ((sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialConnection space direction internalPair)
        (actionGeneratedLorentzSpatialConnectionVelocity
          state space direction internalPair)
        time
  · intro space direction
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      sourceActionGeneratedGravityGaugeCanonicalPhaseUpdate,
      sourceActionGeneratedLorentzCanonicalPhaseUpdate,
      sourceActionGeneratedLorentzCanonicalPhaseVelocity,
      smul_eq_mul] using
      hasDerivAt_const_add_time_smul
        ((sourceActionGeneratedLorentzCanonicalPhaseState source
          state).spatialBFMomentumEvaluation space direction)
        (sourceActionGeneratedLorentzSpatialBFMomentumVelocity
          source state space direction)
        time
  · intro space
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      sourceActionGeneratedScalarCanonicalPhaseUpdate,
      sourceActionGeneratedScalarCanonicalPhaseVelocity] using
      hasDerivAt_const_add_time_smul
        ((sourceActionGeneratedScalarCanonicalPhaseState source
          state).scalarCoordinate space)
        (state.scalarVelocity space)
        time
  · intro space direction
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      sourceActionGeneratedScalarCanonicalPhaseUpdate,
      sourceActionGeneratedScalarCanonicalPhaseVelocity,
      smul_eq_mul] using
      hasDerivAt_const_add_time_smul
        ((sourceActionGeneratedScalarCanonicalPhaseState source
          state).temporalMomentumEvaluation space direction)
        (sourceActionGeneratedScalarTemporalMomentumVelocity
          source state space direction)
        time
  · intro space
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      actionGeneratedMatterPhaseUpdate] using
      hasDerivAt_matterCoordinate_const_add_time_smul
        (state.matter space)
        (actionGeneratedMatterRawTimeVelocity state space)
        time
  · intro space matter
    simpa [sourceActionGeneratedJointCanonicalPhaseUpdate,
      actionGeneratedConjugateMatterPhaseUpdate,
      LinearMap.add_apply] using
      hasDerivAt_const_add_time_smul
        (state.conjugateMatter space matter)
        (actionGeneratedConjugateMatterTimeDerivative state space matter)
        time

/-! ## Path-level positive and negative controls -/

/-- The frozen coframe really stays outside the generated tangent: its
derivative is zero at every time and every matrix coordinate. -/
theorem sourceActionGeneratedJointCanonicalPhasePath_frozenCoframeDerivative_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (internal coordinate : LorentzianIndex) :
    deriv
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).frozenCoframeSnapshot
              space internal coordinate)
        time =
      0 :=
  (sourceActionGeneratedJointCanonicalPhasePath_hasGeneratedDerivative
    source state time).frozenCoframe space internal coordinate |>.deriv

/-- A nonzero generated Lorentz connection tangent forces the corresponding
joint path coordinate to have nonzero derivative. -/
theorem
    sourceActionGeneratedJointCanonicalPhasePath_lorentzDerivative_ne_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (internalPair : Fin 6)
    (nonzero :
      actionGeneratedLorentzSpatialConnectionVelocity
        state space direction internalPair ≠ 0) :
    deriv
        (fun candidate =>
          (sourceActionGeneratedJointCanonicalPhaseUpdate
            source candidate state).gravityGauge.lorentz.spatialConnection
              space direction internalPair)
        time ≠
      0 := by
  rw [(sourceActionGeneratedJointCanonicalPhasePath_hasGeneratedDerivative
    source state time).lorentzSpatialConnection
      space direction internalPair |>.deriv]
  exact nonzero

/-- Coordinate exposure of the formal matter candidate is faithful: a
nonzero action-generated raw velocity cannot disappear after passing through
the complete finite-dimensional coordinate equivalence.  This does not
remove the identity-coframe domain condition on its actual interpretation. -/
theorem
    sourceActionGeneratedJointCanonicalPhasePath_matterCandidateCoordinateDerivative_ne_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (nonzero :
      actionGeneratedMatterRawTimeVelocity state space ≠ 0) :
    deriv
        (fun candidate =>
          matterCoordinateEquiv
            ((sourceActionGeneratedJointCanonicalPhaseUpdate
              source candidate state).matter space))
        time ≠
      0 := by
  rw [(sourceActionGeneratedJointCanonicalPhasePath_hasGeneratedDerivative
    source state time).matter space |>.deriv]
  intro coordinateVelocityZero
  apply nonzero
  apply matterCoordinateEquiv.injective
  simpa using coordinateVelocityZero

/-- Zero path length still returns the initial reduced phase state.  This
guards the physical-time normalization independently of every residual
acceptance law. -/
theorem sourceActionGeneratedJointCanonicalPhasePath_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedJointCanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedJointCanonicalPhaseState source state :=
  sourceActionGeneratedJointCanonicalPhaseUpdate_zero source state

end

end
  SaturationMonoid.PhysicsCore.StageNineJointActionCanonicalPhasePathLaw
