import H0mework.Physics.GaugeAction.P286GaugeConnectionChartTransport
import H0mework.Physics.ConnectionJets.P286ColorCartanQuadraticConnectionJet

/-!
# Source-generated holonomic chart action

This module lifts the already generated Stage-9 hypercharge transition to the
primitive holonomic configuration carrier.  The source supplies only its
actual transition and logarithmic derivative.  In particular, this
construction reads no joint residual, keep predicate, trace, shell receipt, or
stationarity certificate.

The P286 connection transforms by the inhomogeneous logarithmic derivative.
The generated transition centralizes the whole P286 block, so there is no
additional adjoint term in these restricted coordinates.  Scalar and matter
fields transform in their actual finite SU(7) representations, and the
conjugate matter field transforms by the inverse dual action.

This is a configuration-level chart/gauge transporter.  It does not claim to
generate a new dynamical response or a simultaneous stationary solution.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedHolonomicChartAction

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineFullMotherDescentAndTransport
open StageNineGlobalIntegratedAction
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeConnectionChartTransport
open DiracExteriorMatterAction
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open scoped ContDiff

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- The actual P286 preimage of the generated transition logarithmic
derivative.  It is fixed by the source and the ordered chart pair. -/
def generatedTransitionP286LogDerivative
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (direction : LorentzianIndex) : P286LieBlockData :=
  generatedTransitionDerivativeCoefficient source initial terminal direction •
    (0, 0, hyperchargeGenerator)

theorem p286LieBlockEmbed_generatedTransitionP286LogDerivative
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (direction : LorentzianIndex) :
    p286LieBlockEmbed
        (generatedTransitionP286LogDerivative source initial terminal direction) =
      generatedTransitionLogDerivative source initial terminal direction := by
  rw [generatedTransitionP286LogDerivative, p286LieBlockEmbed_real_smul]
  rfl

/-- The source-generated transition acting on every primitive holonomic
field.  The connection shift is independent of the base point because the
generated transition has an affine phase. -/
def sourceGeneratedHolonomicChartAction
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := configuration.coframe
  gravityConnection := configuration.gravityConnection
  gravityAuxiliary := configuration.gravityAuxiliary
  gravitySimplicityMultiplier := configuration.gravitySimplicityMultiplier
  gaugeConnection := fun point direction =>
    configuration.gaugeConnection point direction -
      generatedTransitionP286LogDerivative source initial terminal direction
  gaugeAuxiliary := configuration.gaugeAuxiliary
  scalar := fun point =>
    scalarCoordinateAction
      (generatedTransition source initial terminal point)
      (configuration.scalar point)
  matter := fun point =>
    diracExteriorMatterGaugeRepresentation
      (generatedTransition source initial terminal point)
      (configuration.matter point)
  conjugateMatter := fun point =>
    (configuration.conjugateMatter point).comp
      (diracExteriorMatterGaugeRepresentation
        (generatedTransition source initial terminal point)⁻¹)

@[simp] theorem sourceGeneratedHolonomicChartAction_coframe
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    (sourceGeneratedHolonomicChartAction source initial terminal configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_gravityConnection
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    (sourceGeneratedHolonomicChartAction source initial terminal
      configuration).gravityConnection = configuration.gravityConnection :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_gravityAuxiliary
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    (sourceGeneratedHolonomicChartAction source initial terminal
      configuration).gravityAuxiliary = configuration.gravityAuxiliary :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_gravitySimplicityMultiplier
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    (sourceGeneratedHolonomicChartAction source initial terminal
      configuration).gravitySimplicityMultiplier =
        configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_gaugeConnection
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    (sourceGeneratedHolonomicChartAction source initial terminal
        configuration).gaugeConnection point direction =
      configuration.gaugeConnection point direction -
        generatedTransitionP286LogDerivative source initial terminal direction :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_gaugeAuxiliary
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    (sourceGeneratedHolonomicChartAction source initial terminal
      configuration).gaugeAuxiliary = configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_scalar
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    (sourceGeneratedHolonomicChartAction source initial terminal
        configuration).scalar point =
      scalarCoordinateAction
        (generatedTransition source initial terminal point)
        (configuration.scalar point) :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_matter
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    (sourceGeneratedHolonomicChartAction source initial terminal
        configuration).matter point =
      diracExteriorMatterGaugeRepresentation
        (generatedTransition source initial terminal point)
        (configuration.matter point) :=
  rfl

@[simp] theorem sourceGeneratedHolonomicChartAction_conjugateMatter
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    (sourceGeneratedHolonomicChartAction source initial terminal
        configuration).conjugateMatter point =
      (configuration.conjugateMatter point).comp
        (diracExteriorMatterGaugeRepresentation
          (generatedTransition source initial terminal point)⁻¹) :=
  rfl

theorem sourceGeneratedHolonomicChartAction_nondegenerate
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (sourceGeneratedHolonomicChartAction source initial terminal
      configuration).Nondegenerate :=
  nondegenerate

theorem generatedTransitionDerivativeCoefficient_cocycle
    (source : SmoothUnifiedSource)
    (first second third : StageNineChart)
    (direction : LorentzianIndex) :
    generatedTransitionDerivativeCoefficient source first third direction =
      generatedTransitionDerivativeCoefficient source first second direction +
        generatedTransitionDerivativeCoefficient source second third direction := by
  by_cases directionZero : direction = 0
  · subst direction
    simp [generatedTransitionDerivativeCoefficient]
    ring
  · simp [generatedTransitionDerivativeCoefficient, directionZero]

theorem generatedTransitionP286LogDerivative_cocycle
    (source : SmoothUnifiedSource)
    (first second third : StageNineChart)
    (direction : LorentzianIndex) :
    generatedTransitionP286LogDerivative source first third direction =
      generatedTransitionP286LogDerivative source first second direction +
        generatedTransitionP286LogDerivative source second third direction := by
  unfold generatedTransitionP286LogDerivative
  rw [generatedTransitionDerivativeCoefficient_cocycle, add_smul]

@[simp] theorem p286LieBracket_pureHypercharge_left
    (hypercharge : HyperchargeLieScalar) (data : P286LieBlockData) :
    p286LieBracket (0, 0, hypercharge) data = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

@[simp] theorem p286LieBracket_pureHypercharge_right
    (data : P286LieBlockData) (hypercharge : HyperchargeLieScalar) :
    p286LieBracket data (0, 0, hypercharge) = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    simp [p286LieBracket, suLieBracket]
  · apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, suLieBracket]
    · simp [p286LieBracket]

/-- Coordinate variation whose unit-time shift is exactly the
inhomogeneous connection term in the chart action. -/
def generatedTransitionP286ConnectionVariation
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart) :
    BasePoint → P286GaugeOneForm :=
  fun _ direction =>
    - p286CoordinateEquiv
      (generatedTransitionP286LogDerivative source initial terminal direction)

theorem generatedTransitionP286ConnectionVariation_contDiff
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart) :
    ContDiff ℝ ∞
      (generatedTransitionP286ConnectionVariation source initial terminal) := by
  exact contDiff_const

@[simp] theorem generatedTransitionP286ConnectionVariation_derivative
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        (generatedTransitionP286ConnectionVariation source initial terminal)
        point derivativeDirection formDirection = 0 := by
  simp [p286GaugeVariationCoordinateDerivative,
    generatedTransitionP286ConnectionVariation,
    fieldDirectionalDerivative]

@[simp] theorem generatedTransitionP286ConnectionVariation_bracket_left
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex)
    (coordinate : P286CoordinateCarrier) :
    p286CoordinateLieBracket
        (generatedTransitionP286ConnectionVariation source initial terminal
          point direction)
        coordinate = 0 := by
  simp [generatedTransitionP286ConnectionVariation,
    p286CoordinateLieBracket, generatedTransitionP286LogDerivative]

@[simp] theorem generatedTransitionP286ConnectionVariation_bracket_right
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (direction : LorentzianIndex)
    (coordinate : P286CoordinateCarrier) :
    p286CoordinateLieBracket coordinate
        (generatedTransitionP286ConnectionVariation source initial terminal
          point direction) = 0 := by
  simp [generatedTransitionP286ConnectionVariation,
    p286CoordinateLieBracket, generatedTransitionP286LogDerivative]

@[simp] theorem
    generatedTransitionP286ConnectionVariation_linearCurvature_zero
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    p286GaugeConnectionLinearCurvatureVariation configuration
        (generatedTransitionP286ConnectionVariation source initial terminal)
        point = 0 := by
  funext pair
  simp [p286GaugeConnectionLinearCurvatureVariation]

@[simp] theorem
    generatedTransitionP286ConnectionVariation_quadraticCurvature_zero
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) :
    p286GaugeConnectionQuadraticCurvatureVariation
        (generatedTransitionP286ConnectionVariation source initial terminal)
        point = 0 := by
  funext pair
  simp [p286GaugeConnectionQuadraticCurvatureVariation]

theorem sourceGeneratedHolonomicChartAction_gaugeConnection_eq_vary
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    (sourceGeneratedHolonomicChartAction source initial terminal
        configuration).gaugeConnection =
      (varyP286GaugeConnectionCoordinate configuration
        (generatedTransitionP286ConnectionVariation source initial terminal)
        1).gaugeConnection := by
  funext point direction
  apply p286CoordinateEquiv.injective
  simp [sourceGeneratedHolonomicChartAction,
    varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate,
    generatedTransitionP286ConnectionVariation]
  exact sub_eq_add_neg _ _

theorem sourceGeneratedHolonomicChartAction_gaugeCurvature
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (point : BasePoint) :
    holonomicGaugeCurvature
        (sourceGeneratedHolonomicChartAction source initial terminal
          configuration)
        point =
      holonomicGaugeCurvature configuration point := by
  let variation :=
    generatedTransitionP286ConnectionVariation source initial terminal
  have connectionEquality :
      (sourceGeneratedHolonomicChartAction source initial terminal
          configuration).gaugeConnection =
        (varyP286GaugeConnectionCoordinate configuration variation
          1).gaugeConnection := by
    exact sourceGeneratedHolonomicChartAction_gaugeConnection_eq_vary
      source initial terminal configuration
  have curvatureEquality :
      holonomicGaugeCurvature
          (sourceGeneratedHolonomicChartAction source initial terminal
            configuration)
          point =
        holonomicGaugeCurvature
          (varyP286GaugeConnectionCoordinate configuration variation 1)
          point := by
    unfold holonomicGaugeCurvature p286ConnectionDerivative
    rw [connectionEquality]
  rw [curvatureEquality]
  have coordinateEquality :=
    holonomicP286GaugeCurvatureCoordinate_expansion_of_contDiff
      configuration smooth variation
      (generatedTransitionP286ConnectionVariation_contDiff
        source initial terminal)
      1 point
  have reducedCoordinateEquality :
      holonomicP286GaugeCurvatureCoordinate
          (varyP286GaugeConnectionCoordinate configuration variation 1)
          point =
        holonomicP286GaugeCurvatureCoordinate configuration point := by
    simpa [variation] using coordinateEquality
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun reducedCoordinateEquality pair

theorem toContinuumPointField_sourceGeneratedHolonomicChartAction_gaugeCurvature
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (point : BasePoint) :
    (toContinuumPointField
        (sourceGeneratedHolonomicChartAction source initial terminal
          configuration)
        point).gaugeCurvature =
      (transportContinuumPointField source initial terminal point
        (toContinuumPointField configuration point)).gaugeCurvature := by
  simpa only [toContinuumPointField, transportContinuumPointField] using
    sourceGeneratedHolonomicChartAction_gaugeCurvature
      source initial terminal configuration smooth point

@[simp] theorem sourceGeneratedHolonomicChartAction_self
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicChartAction source chart chart configuration =
      configuration := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point direction
    simp [sourceGeneratedHolonomicChartAction,
      generatedTransitionP286LogDerivative,
      generatedTransitionDerivativeCoefficient]
  · rfl
  · funext point
    simp [sourceGeneratedHolonomicChartAction,
      generatedTransition_normalized]
  · funext point
    change
      diracExteriorMatterGaugeRepresentation
          (generatedTransition source chart chart point)
          (configuration.matter point) =
        configuration.matter point
    rw [generatedTransition_normalized]
    simp only [map_one, Module.End.one_apply]
  · funext point
    apply LinearMap.ext
    intro matter
    simp only [sourceGeneratedHolonomicChartAction, LinearMap.comp_apply]
    rw [generatedTransition_normalized]
    simp only [inv_one, map_one, Module.End.one_apply]

theorem sourceGeneratedHolonomicChartAction_comp
    (source : SmoothUnifiedSource)
    (first second third : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    sourceGeneratedHolonomicChartAction source second third
        (sourceGeneratedHolonomicChartAction source first second configuration) =
      sourceGeneratedHolonomicChartAction source first third configuration := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point direction
    simp only [sourceGeneratedHolonomicChartAction_gaugeConnection]
    calc
      configuration.gaugeConnection point direction -
            generatedTransitionP286LogDerivative source first second direction -
          generatedTransitionP286LogDerivative source second third direction =
        configuration.gaugeConnection point direction -
          (generatedTransitionP286LogDerivative source first second direction +
            generatedTransitionP286LogDerivative source second third direction) := by
              module
      _ = configuration.gaugeConnection point direction -
          generatedTransitionP286LogDerivative source first third direction := by
            exact congrArg
              (fun shift : P286LieBlockData =>
                configuration.gaugeConnection point direction - shift)
              (generatedTransitionP286LogDerivative_cocycle
                source first second third direction).symm
  · rfl
  · funext point
    simp only [sourceGeneratedHolonomicChartAction_scalar]
    rw [← scalarCoordinateAction_mul,
      generatedTransition_cocycle]
  · funext point
    simp only [sourceGeneratedHolonomicChartAction_matter]
    rw [← Module.End.mul_apply, ← map_mul,
      generatedTransition_cocycle]
  · funext point
    apply LinearMap.ext
    intro matter
    simp only [sourceGeneratedHolonomicChartAction_conjugateMatter,
      LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← mul_inv_rev,
      generatedTransition_cocycle]

end

end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedHolonomicChartAction
