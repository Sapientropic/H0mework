import H0mework.Physics.GaugeAction.P286GaugeConnectionLocalVariation
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity

/-!
# Integrated form-native P286 gauge-connection variation

This module promotes the active local P286 connection polynomial to the
authoritative four-dimensional form-native action.  Continuity, compact
support, and integrability of both coefficients are regenerated from the
primitive smooth path.  The BF coefficient is analyzed through a faithful
finite-dimensional coordinate presentation of the same metric-free wedge;
the physical action field remains the actual P286 Lie-valued two-form.

The resulting derivative and stationarity/weak equivalence belong to the
current action hash.  No historical volume-times-metric BF derivative,
momentum, Euler residual, weak equation, stationarity receipt, supplied
current, or fixed actual enters a proof term.  Geometric W13 integration by
parts and the pointwise current balance remain the next checkpoint.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeConnectionIntegratedVariation

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction
open StageNineFormNativeP286GaugeConnectionLocalVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineTopologicalFourFormPairing
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Continuity of the active coefficients -/

private theorem p286TopologicalCoordinateWedge_apply_continuous
    (first second : BasePoint → P286GaugeTwoForm)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (first point) (second point) := by
  unfold generatedTwoFormWedgeCoefficient
  apply continuous_finsetSum
  intro pair _
  exact p286CoordinateLiePairing_apply_continuous
    (fun point => first point pair)
    (fun point => second point (twoFormComplement pair))
    ((continuous_apply pair).comp firstContinuous)
    ((continuous_apply (twoFormComplement pair)).comp secondContinuous)

theorem holonomicFormNativeP286GaugeConnectionBFFirstDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      formNativeP286GaugeConnectionBFFirstVariationDensity
        (toContinuumPointField configuration point)
        (p286GaugeConnectionLinearCurvatureVariation configuration variation
          point) := by
  have auxiliaryContinuous : Continuous fun point =>
      holonomicP286GaugeAuxiliaryCoordinate configuration point :=
    holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth
  have curvatureContinuous : Continuous fun point =>
      p286GaugeConnectionLinearCurvatureVariation configuration variation
        point :=
    p286GaugeConnectionLinearCurvatureVariation_continuous configuration smooth
      variation
  have coordinateContinuous :=
    p286TopologicalCoordinateWedge_apply_continuous
      (holonomicP286GaugeAuxiliaryCoordinate configuration)
      (p286GaugeConnectionLinearCurvatureVariation configuration variation)
      auxiliaryContinuous curvatureContinuous
  exact coordinateContinuous.congr fun point =>
    (formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate
      (toContinuumPointField configuration point)
      (p286GaugeConnectionLinearCurvatureVariation configuration variation
        point)).symm

theorem holonomicFormNativeP286GaugeConnectionBFSecondDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      formNativeP286GaugeConnectionBFFirstVariationDensity
        (toContinuumPointField configuration point)
        (p286GaugeConnectionQuadraticCurvatureVariation variation point) := by
  have auxiliaryContinuous : Continuous fun point =>
      holonomicP286GaugeAuxiliaryCoordinate configuration point :=
    holonomicP286GaugeAuxiliaryCoordinate_continuous configuration smooth
  have curvatureContinuous : Continuous fun point =>
      p286GaugeConnectionQuadraticCurvatureVariation variation point :=
    p286GaugeConnectionQuadraticCurvatureVariation_continuous variation
  have coordinateContinuous :=
    p286TopologicalCoordinateWedge_apply_continuous
      (holonomicP286GaugeAuxiliaryCoordinate configuration)
      (p286GaugeConnectionQuadraticCurvatureVariation variation)
      auxiliaryContinuous curvatureContinuous
  exact coordinateContinuous.congr fun point =>
    (formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate
      (toContinuumPointField configuration point)
      (p286GaugeConnectionQuadraticCurvatureVariation variation point)).symm

private theorem holonomicGeneratedVolumeDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) := by
  unfold generatedVolumeDensity toContinuumPointField
  have coframeContinuous : Continuous configuration.coframe := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    exact (smooth.1 row column).continuous
  exact coframeContinuous.matrix_det.abs

theorem holonomicFormNativeP286GaugeConnectionFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous
      (holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
        configuration variation) := by
  have bfContinuous :=
    holonomicFormNativeP286GaugeConnectionBFFirstDensity_continuous
      configuration smooth variation
  have volumeContinuous :=
    holonomicGeneratedVolumeDensity_continuous configuration smooth
  have scalarContinuous :=
    holonomicScalarGaugeConnectionKineticFirstDensity_continuous source
      configuration smooth nondegenerate variation
  have matterContinuous :=
    holonomicMatterGaugeConnectionFirstDensity_continuous source configuration
      smooth nondegenerate variation
  unfold holonomicFormNativeP286GaugeConnectionFirstVariationDensity
    formNativeP286GaugeConnectionFirstVariationDensity
  exact bfContinuous.add
    (volumeContinuous.mul (scalarContinuous.add matterContinuous))

theorem holonomicFormNativeP286GaugeConnectionSecondVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous
      (holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
        configuration variation) := by
  have bfContinuous :=
    holonomicFormNativeP286GaugeConnectionBFSecondDensity_continuous
      configuration smooth variation
  have volumeContinuous :=
    holonomicGeneratedVolumeDensity_continuous configuration smooth
  have scalarContinuous :=
    holonomicScalarGaugeConnectionKineticSecondDensity_continuous source
      configuration smooth nondegenerate variation
  unfold holonomicFormNativeP286GaugeConnectionSecondVariationDensity
    formNativeP286GaugeConnectionSecondVariationDensity
  exact bfContinuous.add (volumeContinuous.mul scalarContinuous)

/-! ## Compact support and integrability -/

theorem
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ derivativeDirection formDirection : LorentzianIndex,
      p286GaugeVariationCoordinateDerivative variation point
        derivativeDirection formDirection = 0) :
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart
      configuration variation point = 0 := by
  unfold holonomicFormNativeP286GaugeConnectionFirstVariationDensity
  rw [show p286GaugeConnectionLinearCurvatureVariation configuration variation
      point = 0 from
    p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero]
  rw [show holonomicScalarGaugeConnectionVariation configuration variation
      point = 0 from
    holonomicScalarGaugeConnectionVariation_eq_zero configuration variation
      point variationZero]
  rw [show holonomicMatterGaugeConnectionVariation configuration variation
      point = 0 from
    holonomicMatterGaugeConnectionVariation_eq_zero configuration variation
      point variationZero]
  simp [formNativeP286GaugeConnectionFirstVariationDensity,
    formNativeP286GaugeConnectionBFFirstVariationDensity]

theorem
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity_eq_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity source chart
      configuration variation point = 0 := by
  unfold holonomicFormNativeP286GaugeConnectionSecondVariationDensity
  rw [show p286GaugeConnectionQuadraticCurvatureVariation variation point = 0
    from p286GaugeConnectionQuadraticCurvatureVariation_eq_zero variation point
      variationZero]
  rw [show holonomicScalarGaugeConnectionVariation configuration variation
      point = 0 from
    holonomicScalarGaugeConnectionVariation_eq_zero configuration variation
      point variationZero]
  simp [formNativeP286GaugeConnectionSecondVariationDensity,
    formNativeP286GaugeConnectionBFFirstVariationDensity]

theorem holonomicFormNativeP286GaugeConnectionFirstVariationDensity_compact
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart
        configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  exact
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity_eq_zero_of_jet_zero
      source chart configuration variation point jetZero.1 jetZero.2

theorem holonomicFormNativeP286GaugeConnectionSecondVariationDensity_compact
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (holonomicFormNativeP286GaugeConnectionSecondVariationDensity source chart
        configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  exact
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity_eq_zero
      source chart configuration variation point variationZero

theorem holonomicFormNativeP286GaugeConnectionFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
        configuration variation) :=
  (holonomicFormNativeP286GaugeConnectionFirstVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicFormNativeP286GaugeConnectionFirstVariationDensity_compact
        source 0 configuration variation)

theorem holonomicFormNativeP286GaugeConnectionSecondVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
        configuration variation) :=
  (holonomicFormNativeP286GaugeConnectionSecondVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicFormNativeP286GaugeConnectionSecondVariationDensity_compact
        source 0 configuration variation)

/-! ## Integrated polynomial and derivative -/

theorem holonomicFormNativeIntegratedUnifiedAction_p286Connection_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) :
    holonomicFormNativeIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter) =
      holonomicFormNativeIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicFormNativeP286GaugeConnectionFirstVariationDensity source
              0 configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicFormNativeP286GaugeConnectionSecondVariationDensity source
              0 configuration variation point) := by
  unfold holonomicFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedFormNativeUnifiedAction
    integratedFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  change Integrable (fun point : BasePoint =>
    generatedFormNativeUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point
      (toContinuumPointField configuration point)) at densityIntegrable
  have pointwise : (fun point : BasePoint =>
      generatedFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyP286GaugeConnectionCoordinate configuration variation parameter)
          point)) =
      fun point =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
            configuration variation point := by
    funext point
    exact
      holonomicFormNativeUnifiedLocalDensity_p286Connection_quadratic source 0
        configuration smooth variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity_integrable
      source configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity_integrable
      source configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeP286GaugeConnectionFirstVariationDensity
                source 0 configuration variation point +
          parameter ^ 2 *
            holonomicFormNativeP286GaugeConnectionSecondVariationDensity
              source 0 configuration variation point) =
      (∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) 0 point
                (toContinuumPointField configuration point) +
              parameter *
                holonomicFormNativeP286GaugeConnectionFirstVariationDensity
                  source 0 configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeP286GaugeConnectionSecondVariationDensity source
              0 configuration variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter *
            holonomicFormNativeP286GaugeConnectionFirstVariationDensity source
              0 configuration variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeP286GaugeConnectionSecondVariationDensity source
              0 configuration variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicFormNativeIntegratedUnifiedAction_p286Connection_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasDerivAt
      (fun parameter => holonomicFormNativeIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter))
      (∫ point : BasePoint,
        holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
          configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
      configuration variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
      configuration variation point
  have actionEquality :
      (fun parameter => holonomicFormNativeIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter)) =
      fun parameter =>
        holonomicFormNativeIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact
      holonomicFormNativeIntegratedUnifiedAction_p286Connection_quadratic
        source configuration smooth nondegenerate densityIntegrable variation
        parameter
  rw [actionEquality]
  change HasDerivAt
    ((fun parameter =>
      holonomicFormNativeIntegratedUnifiedAction source 0 configuration +
        parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * secondIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstIntegral).const_add
      (holonomicFormNativeIntegratedUnifiedAction source 0 configuration)).add
        (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const secondIntegral))

/-! ## Action stationarity and generated weak coefficient -/

def FormNativeP286GaugeConnectionActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeOneForm,
    HasDerivAt
      (fun parameter => holonomicFormNativeIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter))
      0 0

def FormNativeP286GaugeConnectionWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeOneForm,
    (∫ point : BasePoint,
      holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
        configuration variation point) = 0

theorem formNativeP286GaugeConnectionActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0 configuration) :
    FormNativeP286GaugeConnectionActionStationary source configuration ↔
      FormNativeP286GaugeConnectionWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicFormNativeIntegratedUnifiedAction_p286Connection_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicFormNativeIntegratedUnifiedAction_p286Connection_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    rw [weakEquation variation] at actual
    exact actual

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeP286GaugeConnectionIntegratedVariation
