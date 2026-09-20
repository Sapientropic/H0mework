import H0mework.Physics.Matter.ConjugateMatterActionTimeVelocity
import H0mework.Physics.Geometry.ScalarPointwiseEquation

/-!
# S9-C3h98: action-generated scalar canonical-momentum update

The scalar field is second order, but its action-native `3+1` split does not
require an immediate inversion for scalar acceleration.  The actual scalar
Euler--Lagrange equation first generates the temporal-momentum derivative

`∂₀ P₀ = Aφ - divΣ P`.

Before forming that momentum, this module repairs a producer-side omission
in the earlier local lift: C3h93 carried the primitive scalar value and time
velocity but froze its three spatial derivatives.  Here the full scalar first
jet is read directly from the primitive Cauchy state and realized by an
affine scalar germ.  The resulting actual germ therefore supplies the genuine
`Dᵢ φ` terms to the action momentum.

The construction order is

```text
primitive scalar Cauchy value/velocity/spatial jet
→ Cauchy-faithful affine scalar germ
→ actual scalar differential momentum on the coherent spatial slice
→ action-generated temporal-momentum velocity
→ common scalar coordinate/momentum update.
```

No scalar residual, acceleration, inverse Hessian, endpoint, preimage,
equation witness, or branch selector is supplied.  This is a canonical
first-order phase update at the input state, not yet a scalar acceleration,
integral curve, or full coupled development.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineScalarActionCanonicalMomentumUpdate

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Cauchy-faithful primitive scalar germ -/

/-- Actual spatial derivative of the primitive scalar-coordinate field on
the selected Cauchy slice. -/
def cauchyScalarSpatialDerivativeCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) : ScalarCoordinateCarrier :=
  fderiv ℝ state.scalar space
    (canonicalSpatialCoordinateDirection direction)

/-- Full primitive scalar first jet: stored physical-time velocity followed
by the three actual spatial Cauchy derivatives. -/
def actionGeneratedScalarLocalJetCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  ![
    state.scalarVelocity space,
    cauchyScalarSpatialDerivativeCoordinate state space 0,
    cauchyScalarSpatialDerivativeCoordinate state space 1,
    cauchyScalarSpatialDerivativeCoordinate state space 2
  ] direction

def actionGeneratedScalarLocalIncrement
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    BasePoint →L[ℝ] ScalarCoordinateCarrier :=
  ∑ direction : LorentzianIndex,
    (localBaseCoordinate direction).smulRight
      (actionGeneratedScalarLocalJetCoordinate state space direction)

/-- Cauchy-faithful affine primitive scalar germ. -/
def actionGeneratedScalarLocalField
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  state.scalar space +
    actionGeneratedScalarLocalIncrement state space point

@[simp] theorem actionGeneratedScalarLocalField_origin
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    actionGeneratedScalarLocalField state space 0 =
      state.scalar space := by
  simp [actionGeneratedScalarLocalField,
    actionGeneratedScalarLocalIncrement]

theorem actionGeneratedScalarLocalField_smooth
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞ (actionGeneratedScalarLocalField state space) := by
  change ContDiff ℝ ∞ fun point =>
    state.scalar space +
      actionGeneratedScalarLocalIncrement state space point
  exact contDiff_const.add
    (actionGeneratedScalarLocalIncrement state space).contDiff

theorem actionGeneratedScalarLocalField_derivative
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (actionGeneratedScalarLocalField state space) 0 direction =
      actionGeneratedScalarLocalJetCoordinate state space direction := by
  unfold fieldDirectionalDerivative actionGeneratedScalarLocalField
  rw [fderiv_const_add]
  rw [(actionGeneratedScalarLocalIncrement state space).hasFDerivAt.fderiv]
  fin_cases direction <;>
    simp [actionGeneratedScalarLocalIncrement,
      actionGeneratedScalarLocalJetCoordinate, localBaseCoordinate,
      coordinateDirection, Fin.sum_univ_four]

/-! ## Synchronized local actual lift -/

/-- C3h97 gravity--gauge--matter--dual actual output with the full primitive
scalar Cauchy first jet installed before scalar momentum is read. -/
def sourceActionGeneratedMatterDualScalarLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration :=
  { sourceActionGeneratedMatterDualLocalActualLift source state space with
    scalar := actionGeneratedScalarLocalField state space }

theorem sourceActionGeneratedMatterDualScalarLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedMatterDualScalarLocalActualLift source state
      space).Smooth := by
  have baseSmooth :=
    sourceActionGeneratedMatterDualLocalActualLift_smooth source state space
  rcases baseSmooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      _scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      actionGeneratedScalarLocalField_smooth state space,
      matterSmooth, conjugateMatterSmooth⟩

theorem sourceActionGeneratedMatterDualScalarLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedMatterDualScalarLocalActualLift source state
      space).Nondegenerate := by
  exact sourceActionGeneratedMatterDualLocalActualLift_nondegenerate
    source state space nondegenerate

@[simp] theorem
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedMatterDualScalarLocalActualLift source state
      space).scalar 0 =
      state.scalar space := by
  exact actionGeneratedScalarLocalField_origin state space

theorem sourceActionGeneratedMatterDualScalarLocalActualLift_scalarDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (sourceActionGeneratedMatterDualScalarLocalActualLift source state
          space).scalar
        0 direction =
      actionGeneratedScalarLocalJetCoordinate state space direction := by
  exact actionGeneratedScalarLocalField_derivative state space direction

theorem sourceActionGeneratedMatterDualScalarLocalActualLift_scalarTimeVelocity_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (sourceActionGeneratedMatterDualScalarLocalActualLift source state
          space).scalar
        0 canonicalLorentzianTimeDirection =
      state.scalarVelocity space := by
  simpa [actionGeneratedScalarLocalJetCoordinate,
    canonicalLorentzianTimeDirection] using
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalarDerivative_origin
      source state space canonicalLorentzianTimeDirection

theorem sourceActionGeneratedMatterDualScalarLocalActualLift_scalarSpatialDerivative_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (sourceActionGeneratedMatterDualScalarLocalActualLift source state
          space).scalar
        0 direction.succ =
      cauchyScalarSpatialDerivativeCoordinate state space direction := by
  have derivative :=
    sourceActionGeneratedMatterDualScalarLocalActualLift_scalarDerivative_origin
      source state space direction.succ
  fin_cases direction <;>
    simpa [actionGeneratedScalarLocalJetCoordinate] using
      derivative

/-! ## Action-native scalar canonical phase carrier -/

/-- Derived scalar phase data.  The temporal momentum is retained as its
complete evaluation on all scalar-coordinate directions, not converted back
to an acceleration by a supplied inverse. -/
@[ext] structure StageNineScalarCanonicalPhaseState where
  scalarCoordinate :
    StageNineSpatialPoint → ScalarCoordinateCarrier
  temporalMomentumEvaluation :
    StageNineSpatialPoint → ScalarCoordinateCarrier → ℝ

/-- Coherent scalar differential-momentum field on the whole Cauchy slice.
For each varying spatial point the local actual germ contains that point's
complete primitive scalar first jet. -/
def sourceActionGeneratedScalarDifferentialMomentumEvaluation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (derivativeDirection : LorentzianIndex) :
    StageNineSpatialPoint → ScalarCoordinateCarrier → ℝ :=
  fun space direction =>
    scalarDifferentialMomentum source
      (sourceActionGeneratedMatterDualScalarLocalActualLift
        source state space)
      direction derivativeDirection 0

/-- Initial scalar canonical momentum conjugate to the scalar coordinate. -/
def sourceActionGeneratedScalarTemporalMomentumEvaluation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → ScalarCoordinateCarrier → ℝ :=
  sourceActionGeneratedScalarDifferentialMomentumEvaluation source state
    canonicalLorentzianTimeDirection

def sourceActionGeneratedScalarCanonicalPhaseState
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineScalarCanonicalPhaseState where
  scalarCoordinate := state.scalar
  temporalMomentumEvaluation :=
    sourceActionGeneratedScalarTemporalMomentumEvaluation source state

/-- Three-dimensional divergence of the coherent scalar momentum field. -/
def sourceActionGeneratedScalarSpatialMomentumDivergence
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  ∑ derivativeDirection : Fin 3,
    fderiv ℝ
      (sourceActionGeneratedScalarDifferentialMomentumEvaluation
        source state derivativeDirection.succ · direction)
      space
      (canonicalSpatialCoordinateDirection derivativeDirection)

/-- Temporal scalar-momentum velocity generated by the actual scalar action:
algebraic coefficient minus spatial momentum divergence. -/
def sourceActionGeneratedScalarTemporalMomentumVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → ScalarCoordinateCarrier → ℝ :=
  fun space direction =>
    scalarAlgebraicDirectionalCoefficient source
        (sourceActionGeneratedMatterDualScalarLocalActualLift
          source state space)
        direction 0 -
      sourceActionGeneratedScalarSpatialMomentumDivergence
        source state space direction

/-- Full scalar canonical tangent generated from primitive Cauchy data and
the actual action. -/
def sourceActionGeneratedScalarCanonicalPhaseVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineScalarCanonicalPhaseState where
  scalarCoordinate := state.scalarVelocity
  temporalMomentumEvaluation :=
    sourceActionGeneratedScalarTemporalMomentumVelocity source state

/-! ## Common scalar coordinate/momentum update -/

/-- One physical-time increment advances the primitive scalar coordinate and
its action-derived temporal momentum together. -/
def sourceActionGeneratedScalarCanonicalPhaseUpdate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineScalarCanonicalPhaseState where
  scalarCoordinate := fun space =>
    (sourceActionGeneratedScalarCanonicalPhaseState source
      state).scalarCoordinate space +
      time •
        (sourceActionGeneratedScalarCanonicalPhaseVelocity source
          state).scalarCoordinate space
  temporalMomentumEvaluation := fun space direction =>
    (sourceActionGeneratedScalarCanonicalPhaseState source
      state).temporalMomentumEvaluation space direction +
      time *
        (sourceActionGeneratedScalarCanonicalPhaseVelocity source
          state).temporalMomentumEvaluation space direction

@[simp] theorem sourceActionGeneratedScalarCanonicalPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceActionGeneratedScalarCanonicalPhaseUpdate source 0 state =
      sourceActionGeneratedScalarCanonicalPhaseState source state := by
  apply StageNineScalarCanonicalPhaseState.ext
  · funext space
    simp [sourceActionGeneratedScalarCanonicalPhaseUpdate]
  · funext space direction
    simp [sourceActionGeneratedScalarCanonicalPhaseUpdate]

theorem sourceActionGeneratedScalarCanonicalPhaseUpdate_coordinate
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedScalarCanonicalPhaseUpdate source time
      state).scalarCoordinate space =
      state.scalar space + time • state.scalarVelocity space :=
  rfl

theorem sourceActionGeneratedScalarCanonicalPhaseUpdate_momentum
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    (sourceActionGeneratedScalarCanonicalPhaseUpdate source time
      state).temporalMomentumEvaluation space direction =
      sourceActionGeneratedScalarTemporalMomentumEvaluation source state
          space direction +
        time *
          sourceActionGeneratedScalarTemporalMomentumVelocity source state
            space direction :=
  rfl

/-- The coordinate component of the unit update recovers the stored physical
scalar velocity exactly. -/
theorem sourceActionGeneratedScalarCanonicalPhaseUnitCoordinateVelocity_eq
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedScalarCanonicalPhaseUpdate source 1
          state).scalarCoordinate space -
        (sourceActionGeneratedScalarCanonicalPhaseState source
          state).scalarCoordinate space =
      state.scalarVelocity space := by
  simp [sourceActionGeneratedScalarCanonicalPhaseUpdate_coordinate,
    sourceActionGeneratedScalarCanonicalPhaseState]

/-- The momentum component of the same unit update obeys the actual scalar
action evolution law in every scalar-coordinate direction. -/
theorem sourceActionGeneratedScalarCanonicalPhaseUnitMomentum_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    (sourceActionGeneratedScalarCanonicalPhaseUpdate source 1
          state).temporalMomentumEvaluation space direction -
        (sourceActionGeneratedScalarCanonicalPhaseState source
          state).temporalMomentumEvaluation space direction =
      scalarAlgebraicDirectionalCoefficient source
          (sourceActionGeneratedMatterDualScalarLocalActualLift
            source state space)
          direction 0 -
        sourceActionGeneratedScalarSpatialMomentumDivergence
          source state space direction := by
  simp [sourceActionGeneratedScalarCanonicalPhaseUpdate_momentum,
    sourceActionGeneratedScalarCanonicalPhaseState,
    sourceActionGeneratedScalarTemporalMomentumVelocity]

/-- Frontier theorem: the same producer realizes the complete primitive
scalar first jet and advances the scalar coordinate/temporal-momentum pair by
the actual `3+1` action split. -/
theorem sourceActionGeneratedScalarCanonicalPhaseUnitUpdate_satisfies_actionSystem
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    (∀ space,
      (sourceActionGeneratedMatterDualScalarLocalActualLift source state
          space).scalar 0 =
        state.scalar space ∧
      ∀ direction : LorentzianIndex,
        fieldDirectionalDerivative
            (sourceActionGeneratedMatterDualScalarLocalActualLift source state
              space).scalar
            0 direction =
          actionGeneratedScalarLocalJetCoordinate state space direction) ∧
      (∀ space,
        (sourceActionGeneratedScalarCanonicalPhaseUpdate source 1
              state).scalarCoordinate space -
            (sourceActionGeneratedScalarCanonicalPhaseState source
              state).scalarCoordinate space =
          state.scalarVelocity space) ∧
      ∀ space direction,
        (sourceActionGeneratedScalarCanonicalPhaseUpdate source 1
              state).temporalMomentumEvaluation space direction -
            (sourceActionGeneratedScalarCanonicalPhaseState source
              state).temporalMomentumEvaluation space direction =
          scalarAlgebraicDirectionalCoefficient source
              (sourceActionGeneratedMatterDualScalarLocalActualLift
                source state space)
              direction 0 -
            sourceActionGeneratedScalarSpatialMomentumDivergence
              source state space direction := by
  exact
    ⟨fun space =>
        ⟨sourceActionGeneratedMatterDualScalarLocalActualLift_scalar_origin
            source state space,
          sourceActionGeneratedMatterDualScalarLocalActualLift_scalarDerivative_origin
            source state space⟩,
      sourceActionGeneratedScalarCanonicalPhaseUnitCoordinateVelocity_eq
        source state,
      sourceActionGeneratedScalarCanonicalPhaseUnitMomentum_satisfies_actionLaw
        source state⟩

/-! ## Positive and negative controls -/

/-- Any nonzero primitive scalar-velocity component makes the common unit
update nontrivial. -/
theorem sourceActionGeneratedScalarCanonicalPhaseUnitUpdate_ne_initial_of_velocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (velocityNonzero : state.scalarVelocity space ≠ 0) :
    sourceActionGeneratedScalarCanonicalPhaseUpdate source 1 state ≠
      sourceActionGeneratedScalarCanonicalPhaseState source state := by
  intro updateFixed
  have coordinateFixed := congrArg
    (fun phase : StageNineScalarCanonicalPhaseState =>
      phase.scalarCoordinate space)
    updateFixed
  apply velocityNonzero
  simpa [sourceActionGeneratedScalarCanonicalPhaseUpdate_coordinate,
    sourceActionGeneratedScalarCanonicalPhaseState] using coordinateFixed

/-- If both action-generated scalar tangent components vanish, every local
time update reduces to the derived initial scalar phase point. -/
theorem sourceActionGeneratedScalarCanonicalPhaseUpdate_eq_initial_of_velocity_zero
    (source : SmoothUnifiedSource)
    (time : ℝ)
    (state : StageNineCauchyState)
    (coordinateVelocityZero : state.scalarVelocity = 0)
    (momentumVelocityZero :
      sourceActionGeneratedScalarTemporalMomentumVelocity source state = 0) :
    sourceActionGeneratedScalarCanonicalPhaseUpdate source time state =
      sourceActionGeneratedScalarCanonicalPhaseState source state := by
  apply StageNineScalarCanonicalPhaseState.ext
  · funext space
    have componentZero := congrFun coordinateVelocityZero space
    change
      state.scalar space + time • state.scalarVelocity space =
        state.scalar space
    rw [componentZero]
    simp
  · funext space direction
    have componentZero := congrFun
      (congrFun momentumVelocityZero space) direction
    change
      sourceActionGeneratedScalarTemporalMomentumEvaluation source state
          space direction +
        time *
          sourceActionGeneratedScalarTemporalMomentumVelocity source state
            space direction =
      sourceActionGeneratedScalarTemporalMomentumEvaluation source state
        space direction
    rw [componentZero]
    simp

end

end
  SaturationMonoid.PhysicsCore.StageNineScalarActionCanonicalMomentumUpdate
