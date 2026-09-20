import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity

/-!
# S9-C3a3: integrated P286 connection derivative and weak equation

The local C3a2 polynomial and the analytic C3a3 density control are combined
at the actual integrated action.  The result is an honest derivative along
every compactly supported primitive P286 connection variation.  Stationarity
then implies the weak equation by uniqueness of derivatives; neither a
current nor a field-equation Boolean is stored in the source mouth.

This checkpoint works in canonical generated chart `0`, where the generated
SU(7) frame is definitionally normalized.  Gauge-covariant transport to all
generated charts and integration by parts into the pointwise current equation
remain separate downstream obligations.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionWeakEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open MeasureTheory
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory

noncomputable section

set_option maxHeartbeats 600000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286GaugeConnectionActionVariation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem holonomicIntegratedUnifiedAction_p286GaugeConnection_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter) =
      holonomicIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicP286GaugeConnectionFirstVariationDensity source 0
              configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicP286GaugeConnectionSecondVariationDensity source 0
              configuration variation point) := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyP286GaugeConnectionCoordinate configuration variation parameter)
          point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicP286GaugeConnectionFirstVariationDensity source 0
            configuration variation point +
        parameter ^ 2 *
          holonomicP286GaugeConnectionSecondVariationDensity source 0
            configuration variation point := by
    funext point
    exact holonomicLocalDensity_p286GaugeConnection_quadratic source 0
      configuration smooth variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicP286GaugeConnectionFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicP286GaugeConnectionSecondVariationDensity_integrable source
      configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicP286GaugeConnectionFirstVariationDensity source 0
                configuration variation point +
          parameter ^ 2 *
            holonomicP286GaugeConnectionSecondVariationDensity source 0
              configuration variation point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicP286GaugeConnectionFirstVariationDensity source 0
                configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicP286GaugeConnectionSecondVariationDensity source 0
              configuration variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter *
            holonomicP286GaugeConnectionFirstVariationDensity source 0
              configuration variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicP286GaugeConnectionSecondVariationDensity source 0
              configuration variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicIntegratedUnifiedAction_p286GaugeConnection_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter))
      (∫ point : BasePoint,
        holonomicP286GaugeConnectionFirstVariationDensity source 0
          configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicP286GaugeConnectionFirstVariationDensity source 0 configuration
      variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicP286GaugeConnectionSecondVariationDensity source 0 configuration
      variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_p286GaugeConnection_quadratic source
      configuration smooth nondegenerate densityIntegrable variation parameter
  rw [actionEquality]
  change HasDerivAt
    ((fun parameter =>
      holonomicIntegratedUnifiedAction source 0 configuration +
        parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * secondIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicIntegratedUnifiedAction source 0 configuration)).add
        (((hasDerivAt_id (x := 0)).pow 2).mul_const secondIntegral))

/-- Stationarity is a property of a candidate primitive configuration under
all compactly supported P286 connection variations.  It is not a stored
source credential. -/
def CanonicalP286GaugeConnectionActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeOneForm,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyP286GaugeConnectionCoordinate configuration variation parameter))
      0 0

def CanonicalP286GaugeConnectionWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation P286GaugeOneForm,
    (∫ point : BasePoint,
      holonomicP286GaugeConnectionFirstVariationDensity source 0 configuration
        variation point) = 0

theorem canonicalP286GaugeConnectionActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalP286GaugeConnectionActionStationary source
      configuration) :
    CanonicalP286GaugeConnectionWeakEquation source configuration := by
  intro variation
  have actual :=
    holonomicIntegratedUnifiedAction_p286GaugeConnection_hasDerivAt source
      configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

end

end SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionWeakEquation
