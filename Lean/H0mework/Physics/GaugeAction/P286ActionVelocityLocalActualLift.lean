import H0mework.Physics.GaugeAction.P286ActionConnectionVelocity

/-!
# S9-C3h92: local actual lift of the action-generated P286 velocity

C3h90 generated the canonical P286 spatial-connection velocity from source
and pure Cauchy data.  This module realizes that output as an actual smooth
four-dimensional primitive germ.

At a selected spatial point, the germ uses:

* the derived spatial jet of `A₀`;
* the action-generated `∂₀ Aᵢ`;
* the stored scalar velocity;
* constant local lifts of the remaining primitive values.

The resulting actual `dA + [A,A]` curvature satisfies

`Fμν(0) = (gₛ² *ₑ B)μν`

for all six two-form components.  This is a canonical first-jet lift at one
local origin, not a finite-time integral curve and not a neighborhood or full
joint-shell theorem.  No residual, endpoint, inverse image, shell witness, or
supplied update is used in its constructor.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286ActionVelocityLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineCanonicalCauchyState
open StageNineP286ActionConnectionVelocity
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open scoped ContDiff

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

/-! ## Canonical affine first jet -/

/-- Continuous projection onto one coordinate of the fixed spacetime chart. -/
def localBaseCoordinate
    (direction : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj direction).comp
    (EuclideanSpace.equiv LorentzianIndex ℝ).toContinuousLinearMap

@[simp] theorem localBaseCoordinate_apply
    (direction : LorentzianIndex) (point : BasePoint) :
    localBaseCoordinate direction point = point direction :=
  rfl

/-- Exterior-derivative coordinate required by the action-generated
curvature after removing the non-Abelian bracket at the selected Cauchy
point. -/
def actionGeneratedP286ExteriorDerivativeCoordinate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    P286CoordinateCarrier :=
  p286CoordinateEquiv
      (actionGeneratedP286Curvature source state space pair) -
    p286CoordinateLieBracket
      (p286CoordinateEquiv
        (state.gaugeConnection space (pairFirst pair)))
      (p286CoordinateEquiv
        (state.gaugeConnection space (pairSecond pair)))

/-- Canonical connection first jet.  Temporal-spatial entries retain the
already generated velocity and the actual spatial jet of `A₀`.  Pure spatial
entries use the fixed antisymmetric half split of the action-owned exterior
derivative `(12, 23, 31)`. -/
def sourceGeneratedP286ActionLocalConnectionJet
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    P286CoordinateCarrier :=
  ![
    ![
      (0 : P286CoordinateCarrier),
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity source state space 0),
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity source state space 1),
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity source state space 2)
    ],
    ![
      cauchyP286SpatialConnectionDerivativeCoordinate state space 0
        canonicalLorentzianTimeDirection,
      0,
      (1 / 2 : ℝ) •
        actionGeneratedP286ExteriorDerivativeCoordinate source state space 5,
      -((1 / 2 : ℝ) •
        actionGeneratedP286ExteriorDerivativeCoordinate source state space 4)
    ],
    ![
      cauchyP286SpatialConnectionDerivativeCoordinate state space 1
        canonicalLorentzianTimeDirection,
      -((1 / 2 : ℝ) •
        actionGeneratedP286ExteriorDerivativeCoordinate source state space 5),
      0,
      (1 / 2 : ℝ) •
        actionGeneratedP286ExteriorDerivativeCoordinate source state space 3
    ],
    ![
      cauchyP286SpatialConnectionDerivativeCoordinate state space 2
        canonicalLorentzianTimeDirection,
      (1 / 2 : ℝ) •
        actionGeneratedP286ExteriorDerivativeCoordinate source state space 4,
      -((1 / 2 : ℝ) •
        actionGeneratedP286ExteriorDerivativeCoordinate source state space 3),
      0
    ]
  ] derivativeDirection formDirection

/-- The affine P286 connection increment.  Its temporal connection component
carries the derived spatial jet of `A₀`; each spatial connection component
carries the action-generated time velocity, and the remaining spatial jet is
the canonical antisymmetric lift of the action curvature. -/
def sourceGeneratedP286ActionLocalIncrement
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    BasePoint →L[ℝ] P286CoordinateCarrier :=
  ∑ derivativeDirection : LorentzianIndex,
    (localBaseCoordinate derivativeDirection).smulRight
      (sourceGeneratedP286ActionLocalConnectionJet source state space
        derivativeDirection formDirection)

/-- Actual finite P286 coordinates of the local affine connection germ. -/
def sourceGeneratedP286ActionLocalConnectionCoordinate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (formDirection : LorentzianIndex) :
    P286CoordinateCarrier :=
  p286CoordinateEquiv (state.gaugeConnection space formDirection) +
    sourceGeneratedP286ActionLocalIncrement source state space formDirection
      point

/-- Actual typed P286 connection germ obtained by returning from the existing
finite coordinate chart. -/
def sourceGeneratedP286ActionLocalConnection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    BasePoint → LorentzianIndex → P286LieBlockData :=
  fun point formDirection =>
    p286CoordinateEquiv.symm
      (sourceGeneratedP286ActionLocalConnectionCoordinate source state space
        point formDirection)

@[simp] theorem sourceGeneratedP286ActionLocalConnection_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    sourceGeneratedP286ActionLocalConnection source state space 0
        formDirection =
      state.gaugeConnection space formDirection := by
  apply p286CoordinateEquiv.injective
  simp [sourceGeneratedP286ActionLocalConnection,
    sourceGeneratedP286ActionLocalConnectionCoordinate,
    sourceGeneratedP286ActionLocalIncrement]

theorem sourceGeneratedP286ActionLocalConnectionCoordinate_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (sourceGeneratedP286ActionLocalConnection source state space point
          formDirection) := by
  simpa [sourceGeneratedP286ActionLocalConnection,
    sourceGeneratedP286ActionLocalConnectionCoordinate] using
      (contDiff_const.add
        (sourceGeneratedP286ActionLocalIncrement source state space
          formDirection).contDiff)

/-! ## Full primitive local configuration -/

/-- Canonical actual four-dimensional first-jet lift.  Every field value is
taken from the selected Cauchy point; only the action-generated P286 velocity
and stored scalar velocity create time dependence. -/
def sourceGeneratedP286ActionLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    StageNineHolonomicConfiguration where
  coframe := fun _ => state.coframe space
  gravityConnection := fun _ => state.gravityConnection space
  gravityAuxiliary := fun _ => state.gravityAuxiliary space
  gravitySimplicityMultiplier :=
    fun _ => state.gravitySimplicityMultiplier space
  gaugeConnection :=
    sourceGeneratedP286ActionLocalConnection source state space
  gaugeAuxiliary := fun _ => state.gaugeAuxiliary space
  scalar := fun point =>
    state.scalar space +
      point canonicalLorentzianTimeDirection • state.scalarVelocity space
  matter := fun _ => state.matter space
  conjugateMatter := fun _ => state.conjugateMatter space

/-- Directional differentiation of the actual affine connection reads its
generated linear increment exactly. -/
theorem sourceGeneratedP286ActionLocalConnectionCoordinate_derivative
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          sourceGeneratedP286ActionLocalConnectionCoordinate source state
            space point formDirection)
        0 derivativeDirection =
      sourceGeneratedP286ActionLocalIncrement source state space formDirection
        (coordinateDirection derivativeDirection) := by
  unfold fieldDirectionalDerivative
    sourceGeneratedP286ActionLocalConnectionCoordinate
  rw [fderiv_const_add]
  rw [(sourceGeneratedP286ActionLocalIncrement source state space
    formDirection).hasFDerivAt.fderiv]

/-- The three actual spatial-connection time derivatives are precisely the
action-generated velocity. -/
theorem sourceGeneratedP286ActionLocalConnection_timeDerivative_spatial
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286GaugeConnectionCoordinateDerivative
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 canonicalLorentzianTimeDirection direction.succ =
      p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity source state space
          direction) := by
  unfold p286GaugeConnectionCoordinateDerivative
    holonomicP286GaugeConnectionCoordinate
    sourceGeneratedP286ActionLocalActualLift
    sourceGeneratedP286ActionLocalConnection
  simp only [p286CoordinateEquiv.apply_symm_apply]
  change
    fieldDirectionalDerivative
        (fun point =>
          sourceGeneratedP286ActionLocalConnectionCoordinate source state
            space point direction.succ)
        0 canonicalLorentzianTimeDirection =
      _
  rw [sourceGeneratedP286ActionLocalConnectionCoordinate_derivative]
  fin_cases direction <;>
    simp [sourceGeneratedP286ActionLocalIncrement,
      sourceGeneratedP286ActionLocalConnectionJet, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_four]

/-- The actual spatial derivatives of the local temporal connection reproduce
the derived spatial jet consumed by the producer. -/
theorem sourceGeneratedP286ActionLocalConnection_spatialDerivative_time
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point =>
          sourceGeneratedP286ActionLocalConnectionCoordinate source state
            space point canonicalLorentzianTimeDirection)
        0 direction.succ =
      cauchyP286SpatialConnectionDerivativeCoordinate state space direction
        canonicalLorentzianTimeDirection := by
  rw [sourceGeneratedP286ActionLocalConnectionCoordinate_derivative]
  fin_cases direction <;>
    simp [sourceGeneratedP286ActionLocalIncrement,
      sourceGeneratedP286ActionLocalConnectionJet, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_four]

/-- Every directional derivative of the actual affine connection is exactly
the corresponding generated first-jet coordinate. -/
theorem sourceGeneratedP286ActionLocalConnection_derivative_eq_jet
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          sourceGeneratedP286ActionLocalConnectionCoordinate source state
            space point formDirection)
        0 derivativeDirection =
      sourceGeneratedP286ActionLocalConnectionJet source state space
        derivativeDirection formDirection := by
  rw [sourceGeneratedP286ActionLocalConnectionCoordinate_derivative]
  fin_cases derivativeDirection <;>
    simp [sourceGeneratedP286ActionLocalIncrement, coordinateDirection,
      Fin.sum_univ_four]

/-- Antisymmetrizing the generated connection jet recovers the full
action-owned exterior derivative for all six oriented pairs. -/
theorem sourceGeneratedP286ActionLocalConnectionJet_antisymmetrized
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    sourceGeneratedP286ActionLocalConnectionJet source state space
          (pairFirst pair) (pairSecond pair) -
        sourceGeneratedP286ActionLocalConnectionJet source state space
          (pairSecond pair) (pairFirst pair) =
      actionGeneratedP286ExteriorDerivativeCoordinate source state space
        pair := by
  fin_cases pair <;>
    simp [sourceGeneratedP286ActionLocalConnectionJet,
      actionGeneratedP286ExteriorDerivativeCoordinate,
      pairFirst, pairSecond,
      temporalSpatialPair, canonicalLorentzianTimeDirection,
      sourceGeneratedP286SpatialConnectionVelocity_coordinate] <;>
    module

theorem sourceGeneratedP286ActionLocalActualLift_spatialDerivative_time
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286GaugeConnectionCoordinateDerivative
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 direction.succ canonicalLorentzianTimeDirection =
      cauchyP286SpatialConnectionDerivativeCoordinate state space direction
        canonicalLorentzianTimeDirection := by
  unfold p286GaugeConnectionCoordinateDerivative
    holonomicP286GaugeConnectionCoordinate
    sourceGeneratedP286ActionLocalActualLift
    sourceGeneratedP286ActionLocalConnection
  simp only [p286CoordinateEquiv.apply_symm_apply]
  exact sourceGeneratedP286ActionLocalConnection_spatialDerivative_time
    source state space direction

@[simp] theorem sourceGeneratedP286ActionLocalActualLift_connectionCoordinate_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (formDirection : LorentzianIndex) :
    holonomicP286GaugeConnectionCoordinate
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 formDirection =
      p286CoordinateEquiv (state.gaugeConnection space formDirection) := by
  unfold holonomicP286GaugeConnectionCoordinate
    sourceGeneratedP286ActionLocalActualLift
  change
    p286CoordinateEquiv
        (sourceGeneratedP286ActionLocalConnection source state space 0
          formDirection) =
      p286CoordinateEquiv (state.gaugeConnection space formDirection)
  rw [sourceGeneratedP286ActionLocalConnection_origin]

theorem sourceGeneratedP286ActionLocalActualLift_connectionDerivative
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 derivativeDirection formDirection =
      sourceGeneratedP286ActionLocalConnectionJet source state space
        derivativeDirection formDirection := by
  unfold p286GaugeConnectionCoordinateDerivative
    holonomicP286GaugeConnectionCoordinate
    sourceGeneratedP286ActionLocalActualLift
    sourceGeneratedP286ActionLocalConnection
  simp only [p286CoordinateEquiv.apply_symm_apply]
  exact sourceGeneratedP286ActionLocalConnection_derivative_eq_jet
    source state space derivativeDirection formDirection

theorem sourceGeneratedP286ActionLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceGeneratedP286ActionLocalActualLift source state space).Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact contDiff_const
  · intro direction internalOut internalIn
    exact contDiff_const
  · intro internalPair spacetimePair
    exact contDiff_const
  · intro internalPair spacetimePair
    exact contDiff_const
  · exact sourceGeneratedP286ActionLocalConnectionCoordinate_smooth
      source state space
  · intro pair
    exact (contDiff_const :
      ContDiff ℝ ∞ fun _ : BasePoint =>
        p286CoordinateEquiv (state.gaugeAuxiliary space pair))
  · simpa [sourceGeneratedP286ActionLocalActualLift] using
      (contDiff_const.add
        ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff
          |>.smul_const (state.scalarVelocity space)))
  · exact (contDiff_const :
      ContDiff ℝ ∞ fun _ : BasePoint =>
        matterCoordinateEquiv (state.matter space))
  · intro index
    exact (contDiff_const :
      ContDiff ℝ ∞ fun _ : BasePoint =>
        state.conjugateMatter space
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index 1)))

theorem sourceGeneratedP286ActionLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceGeneratedP286ActionLocalActualLift source state space).Nondegenerate :=
  fun _ => nondegenerate

@[simp] theorem sourceGeneratedP286ActionLocalActualLift_scalar_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceGeneratedP286ActionLocalActualLift source state space).scalar 0 =
      state.scalar space := by
  simp [sourceGeneratedP286ActionLocalActualLift]

theorem sourceGeneratedP286ActionLocalActualLift_scalarVelocity_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (sourceGeneratedP286ActionLocalActualLift source state space).scalar
        0 canonicalLorentzianTimeDirection =
      state.scalarVelocity space := by
  unfold sourceGeneratedP286ActionLocalActualLift
    fieldDirectionalDerivative
  let timeLinear :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).smulRight
      (state.scalarVelocity space)
  change
    fderiv ℝ (fun point => state.scalar space + timeLinear point) 0
        (coordinateDirection canonicalLorentzianTimeDirection) =
      state.scalarVelocity space
  rw [fderiv_const_add, timeLinear.hasFDerivAt.fderiv]
  simp [timeLinear, coordinateDirection, canonicalLorentzianTimeDirection]

/-! ## Actual curvature realization -/

theorem sourceGeneratedP286ActionLocalActualLift_curvatureCoordinate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    holonomicP286GaugeCurvatureCoordinate
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 pair =
      p286CoordinateEquiv
        (actionGeneratedP286Curvature source state space pair) := by
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  rw [sourceGeneratedP286ActionLocalActualLift_connectionDerivative,
    sourceGeneratedP286ActionLocalActualLift_connectionDerivative]
  rw [sourceGeneratedP286ActionLocalActualLift_connectionCoordinate_origin,
    sourceGeneratedP286ActionLocalActualLift_connectionCoordinate_origin]
  rw [sourceGeneratedP286ActionLocalConnectionJet_antisymmetrized]
  unfold actionGeneratedP286ExteriorDerivativeCoordinate
  abel

/-- The local actual lift realizes all six components of the action-generated
P286 curvature at the origin. -/
theorem sourceGeneratedP286ActionLocalActualLift_curvature
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (pair : Fin 6) :
    holonomicGaugeCurvature
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 pair =
      actionGeneratedP286Curvature source state space pair := by
  apply p286CoordinateEquiv.injective
  exact sourceGeneratedP286ActionLocalActualLift_curvatureCoordinate
    source state space pair

theorem sourceGeneratedP286ActionLocalActualLift_temporalCurvatureCoordinate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    holonomicP286GaugeCurvatureCoordinate
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 (temporalSpatialPair direction) =
      p286CoordinateEquiv
        (actionGeneratedP286Curvature source state space
          (temporalSpatialPair direction)) := by
  exact sourceGeneratedP286ActionLocalActualLift_curvatureCoordinate
    source state space (temporalSpatialPair direction)

/-- Typed actual-curvature form of the local realization theorem. -/
theorem sourceGeneratedP286ActionLocalActualLift_temporalCurvature
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    holonomicGaugeCurvature
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 (temporalSpatialPair direction) =
      actionGeneratedP286Curvature source state space
        (temporalSpatialPair direction) := by
  exact sourceGeneratedP286ActionLocalActualLift_curvature
    source state space (temporalSpatialPair direction)

/-- Full six-component P286 auxiliary action equation at the origin of the
generated actual germ.  The theorem intentionally makes no finite-neighborhood
shell claim. -/
theorem sourceGeneratedP286ActionLocalActualLift_auxiliaryEquation_origin
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    holonomicGaugeCurvature
        (sourceGeneratedP286ActionLocalActualLift source state space) 0 =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared :
            ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            ((sourceGeneratedP286ActionLocalActualLift source state space).coframe
              0))
        ((sourceGeneratedP286ActionLocalActualLift source state space).gaugeAuxiliary
          0) := by
  funext pair
  simpa [actionGeneratedP286Curvature,
    sourceGeneratedP286ActionLocalActualLift] using
      sourceGeneratedP286ActionLocalActualLift_curvature
        source state space pair

/-- The actual local germ satisfies the temporal-spatial part of the P286
auxiliary action equation at the origin. -/
theorem sourceGeneratedP286ActionLocalActualLift_temporalAuxiliaryEquation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    holonomicGaugeCurvature
        (sourceGeneratedP286ActionLocalActualLift source state space)
        0 (temporalSpatialPair direction) =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared :
            ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (sourceGeneratedP286ActionLocalActualLift source state space
              |>.coframe 0))
        (sourceGeneratedP286ActionLocalActualLift source state space
          |>.gaugeAuxiliary 0)
        (temporalSpatialPair direction) := by
  simpa [actionGeneratedP286Curvature,
    sourceGeneratedP286ActionLocalActualLift] using
      sourceGeneratedP286ActionLocalActualLift_temporalCurvature
        source state space direction

end

end SaturationMonoid.PhysicsCore.StageNineP286ActionVelocityLocalActualLift
