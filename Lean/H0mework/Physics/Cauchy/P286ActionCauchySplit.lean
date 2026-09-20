import H0mework.Physics.GaugeAction.P286GaugeConnectionPointwiseEquation

/-!
# S9-C3h87: action-native P286 Cauchy split

The P286 connection Euler--Lagrange equation is derived from the actual
Stage-9 action before this module is imported.  Here its BF momentum
divergence is split along the already fixed Lorentzian coordinate convention:
direction `0` is time and directions `1,2,3` are spatial.

This split distinguishes the two roles of the connection equation:

* a temporal one-form test direction has no temporal BF-momentum derivative
  and therefore gives the spatial Gauss responsibility;
* a spatial one-form test direction contains the temporal derivative of the
  action-native BF momentum and therefore gives its evolution equation.

No residual, keep operator, endpoint, target field, inverse, or equation
receipt is used to construct this split.  It is not yet a Cauchy solution
operator: the theorem identifies the action-owned evolution variable and its
constraint before a source-generated development is constructed.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286ActionCauchySplit

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionMomentumRegularity
open StageNineP286GaugeConnectionPointwiseEquation

noncomputable section

/-- The existing Lorentzian coordinate convention fixes time; it is not a
caller-supplied foliation parameter. -/
def canonicalLorentzianTimeDirection : LorentzianIndex := 0

/-- A constant P286 one-form with only a temporal component. -/
def p286TemporalGaugeOneForm
    (component : P286CoordinateCarrier) : P286GaugeOneForm :=
  fun direction =>
    if direction = canonicalLorentzianTimeDirection then component else 0

/-- The temporal projection of a constant P286 one-form. -/
def p286TemporalGaugeOneFormProjection
    (direction : P286GaugeOneForm) : P286GaugeOneForm :=
  p286TemporalGaugeOneForm
    (direction canonicalLorentzianTimeDirection)

/-- The complementary spatial projection of a constant P286 one-form. -/
def p286SpatialGaugeOneFormProjection
    (direction : P286GaugeOneForm) : P286GaugeOneForm :=
  fun formDirection =>
    if formDirection = canonicalLorentzianTimeDirection then
      0
    else
      direction formDirection

@[simp] theorem p286TemporalGaugeOneForm_time
    (component : P286CoordinateCarrier) :
    p286TemporalGaugeOneForm component canonicalLorentzianTimeDirection =
      component := by
  simp [p286TemporalGaugeOneForm]

@[simp] theorem p286SpatialGaugeOneFormProjection_time
    (direction : P286GaugeOneForm) :
    p286SpatialGaugeOneFormProjection direction
        canonicalLorentzianTimeDirection = 0 := by
  simp [p286SpatialGaugeOneFormProjection]

theorem p286GaugeOneForm_eq_temporal_add_spatial
    (direction : P286GaugeOneForm) :
    direction =
      p286TemporalGaugeOneFormProjection direction +
        p286SpatialGaugeOneFormProjection direction := by
  funext formDirection
  by_cases isTime :
      formDirection = canonicalLorentzianTimeDirection
  · subst formDirection
    simp [p286TemporalGaugeOneFormProjection]
  · simp [p286TemporalGaugeOneFormProjection,
      p286TemporalGaugeOneForm, p286SpatialGaugeOneFormProjection, isTime]

/-- The time-direction contribution to the action-generated BF momentum
divergence. -/
def p286GaugeConnectionTemporalBFMomentumDerivative
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  fieldDirectionalDerivative
    (p286GaugeConnectionBFDifferentialMomentum configuration
      (p286GaugeExteriorDerivativeDirection
        canonicalLorentzianTimeDirection direction))
    point canonicalLorentzianTimeDirection

/-- The three spatial contributions to the same action-generated BF momentum
divergence.  The indices are fixed by `LorentzianIndex = Fin 4`; there is no
caller-selected axis or coefficient. -/
def p286GaugeConnectionSpatialBFMomentumDivergence
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) : ℝ :=
  fieldDirectionalDerivative
      (p286GaugeConnectionBFDifferentialMomentum configuration
        (p286GaugeExteriorDerivativeDirection 1 direction))
      point 1 +
    fieldDirectionalDerivative
      (p286GaugeConnectionBFDifferentialMomentum configuration
        (p286GaugeExteriorDerivativeDirection 2 direction))
      point 2 +
    fieldDirectionalDerivative
      (p286GaugeConnectionBFDifferentialMomentum configuration
        (p286GaugeExteriorDerivativeDirection 3 direction))
      point 3

/-- Exact `3+1` decomposition of the BF momentum divergence appearing in the
actual P286 Euler--Lagrange equation. -/
theorem p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial
    (configuration : StageNineHolonomicConfiguration)
    (direction : P286GaugeOneForm) (point : BasePoint) :
    p286GaugeConnectionBFDifferentialMomentumDivergence configuration
        direction point =
      p286GaugeConnectionTemporalBFMomentumDerivative configuration
          direction point +
        p286GaugeConnectionSpatialBFMomentumDivergence configuration
          direction point := by
  simp [p286GaugeConnectionBFDifferentialMomentumDivergence,
    p286GaugeConnectionTemporalBFMomentumDerivative,
    p286GaugeConnectionSpatialBFMomentumDivergence,
    canonicalLorentzianTimeDirection, Fin.sum_univ_four]
  ring

/-- A temporal test one-form has no `dt ∧ dt` exterior-derivative channel. -/
theorem p286GaugeExteriorDerivativeDirection_time_temporal_eq_zero
    (component : P286CoordinateCarrier) :
    p286GaugeExteriorDerivativeDirection canonicalLorentzianTimeDirection
        (p286TemporalGaugeOneForm component) = 0 := by
  funext pair
  fin_cases pair <;>
    simp [p286GaugeExteriorDerivativeDirection,
      p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection,
      pairFirst, pairSecond]

private theorem p286GaugeConnectionBFDifferentialMomentum_zero
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    p286GaugeConnectionBFDifferentialMomentum configuration
        (0 : P286GaugeTwoForm) = 0 := by
  funext point
  rw [p286GaugeConnectionBFDifferentialMomentum_eq_density configuration
    nondegenerate]
  have zeroDensity :
      p286GaugeBFCurvatureIncrementDensity
          (configuration.coframe point)
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryCoordinate configuration point)
          (0 : P286GaugeTwoForm) = 0 := by
    change
      p286GaugeBFCurvatureIncrementLinear
          (configuration.coframe point)
          (coframeGaugeSpacetimeHodgeLinear (configuration.coframe point))
          (holonomicP286GaugeAuxiliaryCoordinate configuration point) 0 = 0
    exact map_zero _
  rw [zeroDensity]
  simp

/-- Consequently the temporal BF-momentum derivative vanishes on every purely
temporal test direction. -/
theorem p286GaugeConnectionTemporalBFMomentumDerivative_temporal_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (component : P286CoordinateCarrier) (point : BasePoint) :
    p286GaugeConnectionTemporalBFMomentumDerivative configuration
        (p286TemporalGaugeOneForm component) point = 0 := by
  rw [p286GaugeConnectionTemporalBFMomentumDerivative,
    p286GaugeExteriorDerivativeDirection_time_temporal_eq_zero,
    p286GaugeConnectionBFDifferentialMomentum_zero configuration
      nondegenerate]
  simp [fieldDirectionalDerivative]

/-- Spatial Gauss responsibility obtained by testing the action equation
against the temporal component of the connection one-form. -/
def CanonicalP286GaugeGaussConstraintAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  ∀ component : P286CoordinateCarrier,
    p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
        (p286TemporalGaugeOneForm component) point =
      p286GaugeConnectionSpatialBFMomentumDivergence configuration
        (p286TemporalGaugeOneForm component) point

/-- Temporal evolution law for the BF momentum dual to spatial connection
directions.  This is an equality generated by the action equation, not a
stored update or stationarity certificate. -/
def CanonicalP286GaugeSpatialMomentumEvolutionAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : Prop :=
  ∀ direction : P286GaugeOneForm,
    direction canonicalLorentzianTimeDirection = 0 →
      p286GaugeConnectionTemporalBFMomentumDerivative configuration
          direction point =
        p286GaugeConnectionAlgebraicCurrentCoefficient source configuration
            direction point -
          p286GaugeConnectionSpatialBFMomentumDivergence configuration
            direction point

theorem canonicalP286GaugeConnectionPointwiseEquation_implies_gauss
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (equation : CanonicalP286GaugeConnectionPointwiseEquation source
      configuration)
    (point : BasePoint) :
    CanonicalP286GaugeGaussConstraintAt source configuration point := by
  intro component
  have pointEquation :
      p286GaugeConnectionEulerLagrangeCoefficient source configuration
          (p286TemporalGaugeOneForm component) point = 0 := by
    simpa using
      congrFun (equation (p286TemporalGaugeOneForm component)) point
  rw [p286GaugeConnectionEulerLagrangeCoefficient,
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial,
    p286GaugeConnectionTemporalBFMomentumDerivative_temporal_eq_zero
      configuration nondegenerate] at pointEquation
  linarith

theorem canonicalP286GaugeConnectionPointwiseEquation_implies_spatialMomentumEvolution
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : CanonicalP286GaugeConnectionPointwiseEquation source
      configuration)
    (point : BasePoint) :
    CanonicalP286GaugeSpatialMomentumEvolutionAt source configuration
      point := by
  intro direction _
  have pointEquation :
      p286GaugeConnectionEulerLagrangeCoefficient source configuration
          direction point = 0 := by
    simpa using congrFun (equation direction) point
  rw [p286GaugeConnectionEulerLagrangeCoefficient,
    p286GaugeConnectionBFDifferentialMomentumDivergence_eq_temporal_add_spatial]
      at pointEquation
  linarith

/-- First action-native Cauchy gate: one already-derived P286 pointwise
equation simultaneously yields its spatial Gauss responsibility and its
temporal BF-momentum evolution law. -/
theorem canonicalP286GaugeConnectionPointwiseEquation_implies_cauchySplit
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (equation : CanonicalP286GaugeConnectionPointwiseEquation source
      configuration)
    (point : BasePoint) :
    CanonicalP286GaugeGaussConstraintAt source configuration point ∧
      CanonicalP286GaugeSpatialMomentumEvolutionAt source configuration
        point :=
  ⟨canonicalP286GaugeConnectionPointwiseEquation_implies_gauss source
      configuration nondegenerate equation point,
    canonicalP286GaugeConnectionPointwiseEquation_implies_spatialMomentumEvolution
      source configuration equation point⟩

end

end SaturationMonoid.PhysicsCore.StageNineP286ActionCauchySplit
