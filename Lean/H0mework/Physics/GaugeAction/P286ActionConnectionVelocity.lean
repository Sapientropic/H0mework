import H0mework.Physics.Cauchy.GeneratedMotherTimeCauchyFlow
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariation

/-!
# S9-C3h90: action-generated P286 connection velocity

The previous checkpoint constructed the actual typed mother-time transport
`U` before inspecting any equation residual.  This module now takes the next
action-first step.  The P286 auxiliary variation of the existing Stage-9
action generates the curvature

`Fᵃᶜᵗ = gₛ² *ₑ B`.

For the canonical `3+1` split, the actual non-Abelian curvature identity is

`F₀ᵢ = ∂₀ Aᵢ - ∂ᵢ A₀ + [A₀, Aᵢ]`.

Consequently the action itself canonically generates

`∂₀ Aᵢ = Fᵃᶜᵗ₀ᵢ + ∂ᵢ A₀ - [A₀, Aᵢ]`.

The definition below consumes only the source-generated coupling and pure
Cauchy data.  It does not consume a residual, endpoint, shell witness,
preimage, stationarity receipt, supplied velocity, or branch selector.
Residual vanishing is deliberately postponed to a downstream acceptance
theorem.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286ActionConnectionVelocity

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineCanonicalCauchyState
open StageNineSourceGeneratedMotherTimeCauchyFlow

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

/-! ## Canonical temporal-spatial coordinates -/

/-- The first three two-form slots are canonically `(01, 02, 03)`. -/
def temporalSpatialPair (direction : Fin 3) : Fin 6 :=
  ⟨direction.val, by omega⟩

@[simp] theorem pairFirst_temporalSpatialPair
    (direction : Fin 3) :
    pairFirst (temporalSpatialPair direction) =
      canonicalLorentzianTimeDirection := by
  fin_cases direction <;>
    rfl

@[simp] theorem pairSecond_temporalSpatialPair
    (direction : Fin 3) :
    pairSecond (temporalSpatialPair direction) = direction.succ := by
  fin_cases direction <;>
    rfl

/-- Unit coordinate vector in the canonical spatial slice. -/
def canonicalSpatialCoordinateDirection
    (direction : Fin 3) : StageNineSpatialPoint :=
  EuclideanSpace.single direction 1

/-- Continuous projection onto a coordinate of the canonical spatial
Euclidean chart. -/
def canonicalSpatialCoordinate
    (direction : Fin 3) : StageNineSpatialPoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj direction).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

/-- The fixed linear inclusion of spatial tangent vectors into spacetime
tangent vectors. -/
def canonicalSpatialInclusion :
    StageNineSpatialPoint →L[ℝ] BasePoint :=
  (EuclideanSpace.equiv LorentzianIndex ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      ![(0 : StageNineSpatialPoint →L[ℝ] ℝ),
        canonicalSpatialCoordinate 0,
        canonicalSpatialCoordinate 1,
        canonicalSpatialCoordinate 2])

@[simp] theorem canonicalSpatialInclusion_time
    (space : StageNineSpatialPoint) :
    canonicalSpatialInclusion space canonicalLorentzianTimeDirection = 0 := by
  rfl

@[simp] theorem canonicalSpatialInclusion_spatial
    (space : StageNineSpatialPoint) (direction : Fin 3) :
    canonicalSpatialInclusion space direction.succ = space direction := by
  fin_cases direction <;>
    rfl

theorem canonicalSpatialInclusion_coordinateDirection
    (direction : Fin 3) :
    canonicalSpatialInclusion
        (canonicalSpatialCoordinateDirection direction) =
      coordinateDirection direction.succ := by
  ext output
  fin_cases direction <;> fin_cases output <;>
    simp [canonicalSpatialInclusion, canonicalSpatialCoordinate,
      canonicalSpatialCoordinateDirection, coordinateDirection]

theorem canonicalCauchySlicePoint_eq_const_add_inclusion
    (time : ℝ) (space : StageNineSpatialPoint) :
    canonicalCauchySlicePoint time space =
      EuclideanSpace.single canonicalLorentzianTimeDirection time +
        canonicalSpatialInclusion space := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalSpatialInclusion,
      canonicalSpatialCoordinate, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- The canonical slice embedding has the fixed spatial inclusion as its
Fréchet derivative. -/
theorem canonicalCauchySlicePoint_hasFDerivAt
    (time : ℝ) (space : StageNineSpatialPoint) :
    HasFDerivAt (canonicalCauchySlicePoint time)
      canonicalSpatialInclusion space := by
  have derivative :=
    (canonicalSpatialInclusion.hasFDerivAt
      (x := space)).const_add
        (EuclideanSpace.single canonicalLorentzianTimeDirection time)
  apply derivative.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun candidate =>
    canonicalCauchySlicePoint_eq_const_add_inclusion time candidate

/-! ## Action-generated curvature and spatial jet -/

/-- The P286 curvature produced by the auxiliary part of the actual action.
This is the right-hand side of `P286GaugeAuxiliaryEquation`, defined directly
from source coupling, coframe, and auxiliary data rather than by inverting a
residual. -/
def actionGeneratedP286Curvature
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    Fin 6 → P286LieBlockData :=
  liftGaugeTwoFormOperator
    (((sourceGeneratedUnifiedCouplings source).strongCouplingSquared : ℝ) •
      coframeGaugeSpacetimeHodgeLinear (state.coframe space))
    (state.gaugeAuxiliary space)

/-- Spatial derivative of one P286 connection component, in the existing
finite coordinate chart on the typed Lie algebra. -/
def cauchyP286SpatialConnectionDerivativeCoordinate
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (formDirection : LorentzianIndex) :
    P286CoordinateCarrier :=
  fderiv ℝ
      (fun candidate =>
        p286CoordinateEquiv
          (state.gaugeConnection candidate formDirection))
      space
      (canonicalSpatialCoordinateDirection derivativeDirection)

/-- Restriction to a canonical Cauchy slice preserves every spatial
connection derivative. -/
theorem cauchyP286SpatialConnectionDerivativeCoordinate_restriction
    (time : ℝ)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (space : StageNineSpatialPoint)
    (derivativeDirection : Fin 3)
    (formDirection : LorentzianIndex) :
    cauchyP286SpatialConnectionDerivativeCoordinate
        (canonicalCauchyRestriction time configuration)
        space derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative configuration
        (canonicalCauchySlicePoint time space)
        derivativeDirection.succ formDirection := by
  have fieldDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          p286CoordinateEquiv
            (configuration.gaugeConnection point formDirection))
        (canonicalCauchySlicePoint time space) :=
    ((smooth.2.2.2.2.1 formDirection).differentiable (by simp)).differentiableAt
  have derivative :=
    fieldDifferentiable.hasFDerivAt.comp space
      (canonicalCauchySlicePoint_hasFDerivAt time space)
  unfold cauchyP286SpatialConnectionDerivativeCoordinate
    p286GaugeConnectionCoordinateDerivative fieldDirectionalDerivative
  change
    fderiv ℝ
        ((fun point =>
          p286CoordinateEquiv
            (configuration.gaugeConnection point formDirection)) ∘
          canonicalCauchySlicePoint time)
        space
        (canonicalSpatialCoordinateDirection derivativeDirection) =
      fderiv ℝ
        (fun point =>
          p286CoordinateEquiv
            (configuration.gaugeConnection point formDirection))
        (canonicalCauchySlicePoint time space)
        (coordinateDirection derivativeDirection.succ)
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.coe_comp,
    Function.comp_apply,
    canonicalSpatialInclusion_coordinateDirection]

/-- Reconstruct only the temporal-spatial curvature component determined by
a candidate connection velocity.  This is the actual `dA + [A,A]` formula,
not a residual carrier. -/
def p286TemporalSpatialCurvatureCoordinate
    (state : StageNineCauchyState)
    (velocity :
      StageNineSpatialPoint → Fin 3 → P286LieBlockData)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    P286CoordinateCarrier :=
  p286CoordinateEquiv (velocity space direction) -
      cauchyP286SpatialConnectionDerivativeCoordinate state space direction
        canonicalLorentzianTimeDirection +
    p286CoordinateLieBracket
      (p286CoordinateEquiv
        (state.gaugeConnection space canonicalLorentzianTimeDirection))
      (p286CoordinateEquiv
        (state.gaugeConnection space direction.succ))

/-! ## Producer -/

/-- The P286 spatial-connection velocity generated by the source and actual
auxiliary action.  No candidate velocity is supplied to this definition. -/
def sourceGeneratedP286SpatialConnectionVelocity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    StageNineSpatialPoint → Fin 3 → P286LieBlockData :=
  fun space direction =>
    p286CoordinateEquiv.symm
      (p286CoordinateEquiv
          (actionGeneratedP286Curvature source state space
            (temporalSpatialPair direction)) +
        cauchyP286SpatialConnectionDerivativeCoordinate state space direction
          canonicalLorentzianTimeDirection -
        p286CoordinateLieBracket
          (p286CoordinateEquiv
            (state.gaugeConnection space
              canonicalLorentzianTimeDirection))
          (p286CoordinateEquiv
            (state.gaugeConnection space direction.succ)))

@[simp] theorem sourceGeneratedP286SpatialConnectionVelocity_coordinate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286CoordinateEquiv
        (sourceGeneratedP286SpatialConnectionVelocity source state
          space direction) =
      p286CoordinateEquiv
          (actionGeneratedP286Curvature source state space
            (temporalSpatialPair direction)) +
        cauchyP286SpatialConnectionDerivativeCoordinate state space direction
          canonicalLorentzianTimeDirection -
        p286CoordinateLieBracket
          (p286CoordinateEquiv
            (state.gaugeConnection space
              canonicalLorentzianTimeDirection))
          (p286CoordinateEquiv
            (state.gaugeConnection space direction.succ)) := by
  exact p286CoordinateEquiv.apply_symm_apply _

/-- Downstream action-law acceptance predicate for a candidate velocity.
It is not stored in the source or in the generated velocity. -/
def P286ActionGeneratedSpatialVelocityLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (velocity :
      StageNineSpatialPoint → Fin 3 → P286LieBlockData) : Prop :=
  ∀ space direction,
    p286TemporalSpatialCurvatureCoordinate state velocity space direction =
      p286CoordinateEquiv
        (actionGeneratedP286Curvature source state space
          (temporalSpatialPair direction))

/-- The source/action-generated velocity satisfies the actual temporal-spatial
curvature law. -/
theorem sourceGeneratedP286SpatialConnectionVelocity_satisfies_actionLaw
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    P286ActionGeneratedSpatialVelocityLaw source state
      (sourceGeneratedP286SpatialConnectionVelocity source state) := by
  intro space direction
  unfold p286TemporalSpatialCurvatureCoordinate
    sourceGeneratedP286SpatialConnectionVelocity
  rw [p286CoordinateEquiv.apply_symm_apply]
  abel

/-- The action law has exactly one velocity over fixed Cauchy data.  Thus the
producer above makes no hidden branch choice. -/
theorem p286ActionGeneratedSpatialVelocityLaw_unique
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (first second :
      StageNineSpatialPoint → Fin 3 → P286LieBlockData)
    (firstLaw :
      P286ActionGeneratedSpatialVelocityLaw source state first)
    (secondLaw :
      P286ActionGeneratedSpatialVelocityLaw source state second) :
    first = second := by
  funext space direction
  apply p286CoordinateEquiv.injective
  have firstEquation := firstLaw space direction
  have secondEquation := secondLaw space direction
  unfold p286TemporalSpatialCurvatureCoordinate at firstEquation secondEquation
  have equation := firstEquation.trans secondEquation.symm
  have canceled := congrArg
    (fun value =>
      value +
        cauchyP286SpatialConnectionDerivativeCoordinate state space direction
          canonicalLorentzianTimeDirection -
        p286CoordinateLieBracket
          (p286CoordinateEquiv
            (state.gaugeConnection space
              canonicalLorentzianTimeDirection))
          (p286CoordinateEquiv
            (state.gaugeConnection space direction.succ)))
    equation
  abel_nf at canceled
  exact canceled

theorem p286ActionGeneratedSpatialVelocityLaw_iff_eq_generated
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (velocity :
      StageNineSpatialPoint → Fin 3 → P286LieBlockData) :
    P286ActionGeneratedSpatialVelocityLaw source state velocity ↔
      velocity =
        sourceGeneratedP286SpatialConnectionVelocity source state := by
  constructor
  · intro law
    exact p286ActionGeneratedSpatialVelocityLaw_unique source state velocity
      (sourceGeneratedP286SpatialConnectionVelocity source state) law
      (sourceGeneratedP286SpatialConnectionVelocity_satisfies_actionLaw
        source state)
  · intro equality
    subst velocity
    exact sourceGeneratedP286SpatialConnectionVelocity_satisfies_actionLaw
      source state

/-! ## Positive and negative producer regressions -/

/-- A nonzero action-generated component forces a nonzero produced velocity.
This is a positive construction check: the conclusion concerns the output of
the producer rather than existence of a supplied witness. -/
theorem sourceGeneratedP286SpatialConnectionVelocity_ne_zero_of_component
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : Fin 3)
    (componentNonzero :
      p286CoordinateEquiv
          (actionGeneratedP286Curvature source state space
            (temporalSpatialPair direction)) +
          cauchyP286SpatialConnectionDerivativeCoordinate state space
            direction canonicalLorentzianTimeDirection -
          p286CoordinateLieBracket
            (p286CoordinateEquiv
              (state.gaugeConnection space
                canonicalLorentzianTimeDirection))
            (p286CoordinateEquiv
              (state.gaugeConnection space direction.succ)) ≠ 0) :
    sourceGeneratedP286SpatialConnectionVelocity source state ≠ 0 := by
  intro velocityZero
  have componentZero := congrArg p286CoordinateEquiv
    (congrFun (congrFun velocityZero space) direction)
  rw [sourceGeneratedP286SpatialConnectionVelocity_coordinate] at componentZero
  exact componentNonzero (by simpa using componentZero)

/-- Zero primitive P286 data is the negative control: the action-generated
connection velocity vanishes without inspecting any residual. -/
theorem sourceGeneratedP286SpatialConnectionVelocity_eq_zero_of_gaugeData_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (connectionZero : state.gaugeConnection = 0)
    (auxiliaryZero : state.gaugeAuxiliary = 0) :
    sourceGeneratedP286SpatialConnectionVelocity source state = 0 := by
  funext space direction
  apply p286CoordinateEquiv.injective
  rw [sourceGeneratedP286SpatialConnectionVelocity_coordinate]
  simp [actionGeneratedP286Curvature,
    cauchyP286SpatialConnectionDerivativeCoordinate,
    p286CoordinateLieBracket, p286LieBracket, suLieBracket,
    connectionZero, auxiliaryZero]

/-! ## Actual holonomic-history bridge -/

/-- The genuine time derivative of the three spatial P286 connection
components, restricted from a four-dimensional holonomic history. -/
def canonicalRestrictedP286SpatialConnectionVelocity
    (time : ℝ)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineSpatialPoint → Fin 3 → P286LieBlockData :=
  fun space direction =>
    p286ConnectionDerivative configuration
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection direction.succ

theorem canonicalRestrictedP286SpatialConnectionVelocity_coordinate
    (time : ℝ)
    (configuration : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    p286CoordinateEquiv
        (canonicalRestrictedP286SpatialConnectionVelocity time configuration
          space direction) =
      p286GaugeConnectionCoordinateDerivative configuration
        (canonicalCauchySlicePoint time space)
        canonicalLorentzianTimeDirection direction.succ := by
  exact (p286GaugeConnectionCoordinateDerivative_eq configuration
    (canonicalCauchySlicePoint time space)
    canonicalLorentzianTimeDirection direction.succ).symm

/-- The field equation derived from the actual auxiliary action implies that
the true holonomic time derivative obeys the Cauchy action law. -/
theorem p286GaugeAuxiliaryEquation_implies_restrictedVelocity_actionLaw
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (equation : P286GaugeAuxiliaryEquation source configuration)
    (time : ℝ) :
    P286ActionGeneratedSpatialVelocityLaw source
      (canonicalCauchyRestriction time configuration)
      (canonicalRestrictedP286SpatialConnectionVelocity time
        configuration) := by
  intro space direction
  let point := canonicalCauchySlicePoint time space
  let pair := temporalSpatialPair direction
  unfold p286TemporalSpatialCurvatureCoordinate
  rw [canonicalRestrictedP286SpatialConnectionVelocity_coordinate]
  rw [cauchyP286SpatialConnectionDerivativeCoordinate_restriction
    time configuration smooth]
  change
    p286GaugeConnectionCoordinateDerivative configuration point
          canonicalLorentzianTimeDirection direction.succ -
        p286GaugeConnectionCoordinateDerivative configuration point
          direction.succ canonicalLorentzianTimeDirection +
      p286CoordinateLieBracket
        (holonomicP286GaugeConnectionCoordinate configuration point
          canonicalLorentzianTimeDirection)
        (holonomicP286GaugeConnectionCoordinate configuration point
          direction.succ) =
      p286CoordinateEquiv
        (actionGeneratedP286Curvature source
          (canonicalCauchyRestriction time configuration) space pair)
  rw [← pairFirst_temporalSpatialPair direction,
    ← pairSecond_temporalSpatialPair direction]
  rw [← holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket
    configuration point pair]
  have typedEquation := congrFun (equation point) pair
  have coordinateEquation := congrArg p286CoordinateEquiv typedEquation
  simpa [point, pair, holonomicP286GaugeCurvatureCoordinate,
    actionGeneratedP286Curvature, canonicalCauchyRestriction] using
    coordinateEquation

/-- Producer theorem: on every smooth history solving the actual auxiliary
action equation, the genuine `∂₀ Aᵢ` is exactly the velocity generated from
the source and its Cauchy data. -/
theorem p286GaugeAuxiliaryEquation_restrictedVelocity_eq_generated
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (equation : P286GaugeAuxiliaryEquation source configuration)
    (time : ℝ) :
    canonicalRestrictedP286SpatialConnectionVelocity time configuration =
      sourceGeneratedP286SpatialConnectionVelocity source
        (canonicalCauchyRestriction time configuration) :=
  (p286ActionGeneratedSpatialVelocityLaw_iff_eq_generated source
    (canonicalCauchyRestriction time configuration)
    (canonicalRestrictedP286SpatialConnectionVelocity time configuration)).mp
      (p286GaugeAuxiliaryEquation_implies_restrictedVelocity_actionLaw
        source configuration smooth equation time)

end

end SaturationMonoid.PhysicsCore.StageNineP286ActionConnectionVelocity
