import H0mework.Physics.Lorentz.LorentzConnectionLocalVariation
import H0mework.Physics.Lorentz.LorentzConnectionActualVariationRegularity

/-!
# Integrated form-native Lorentz-connection variation

This module promotes the actual local Lorentz polynomial of the corrected
form-native mother action to its four-dimensional integral.  Continuity,
compact support, and integrability of both coefficients are regenerated from
the primitive smooth path.  Nondegeneracy is used only by the Dirac kinetic
readout through the inverse coframe; the topological gravity coefficient does
not depend on it.

No historical action derivative, momentum, weak equation, stationarity
certificate, geometric residual, or fixed actual enters a proof term here.
The geometric W13 integration-by-parts identification remains the next gate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeLorentzConnectionIntegratedVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction
open StageNineFormNativeLorentzConnectionLocalVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActualVariationRegularity
open StageNineMatterCovariantDerivativeAffine
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing
open StageNineHolonomicGravityCurvatureVarianceNormalization
open DiracExteriorMatterAction
open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! ## Continuity of the new coefficients -/

private theorem holonomicGravityAuxiliary_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.gravityAuxiliary := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  exact (smooth.2.2.1 internalPair spacetimePair).continuous

private theorem gravityTopologicalBFCoefficient_apply_continuous
    (first second : BasePoint -> PhysicalBivector)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      gravityTopologicalBFCoefficient (first point) (second point) := by
  have coefficientEquality :
      (fun point =>
        gravityTopologicalBFCoefficient (first point) (second point)) =
      fun point =>
        gravityTopologicalMixedWedgeCoefficient
          (first point) (second point) := by
    funext point
    exact gravityTopologicalBFCoefficient_eq_mixed _ _
  rw [coefficientEquality]
  unfold gravityTopologicalMixedWedgeCoefficient
  apply continuous_finsetSum
  intro internalPair _
  have firstPairContinuous : Continuous fun point =>
      first point internalPair :=
    (continuous_apply internalPair).comp firstContinuous
  have secondPairContinuous : Continuous fun point =>
      second point internalPair :=
    (continuous_apply internalPair).comp secondContinuous
  rw [show (fun point =>
      orientedTwoFormWedgeCoefficient
        (first point internalPair) (second point internalPair)) =
      fun point =>
        first point internalPair 0 * second point internalPair 3 +
        first point internalPair 1 * second point internalPair 4 +
        first point internalPair 2 * second point internalPair 5 +
        first point internalPair 3 * second point internalPair 0 +
        first point internalPair 4 * second point internalPair 1 +
        first point internalPair 5 * second point internalPair 2 by
    funext point
    rw [orientedTwoFormWedgeCoefficient_explicit]]
  fun_prop

theorem holonomicFormNativeLorentzConnectionGravityFirstDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      gravityTopologicalBFCoefficient
        (configuration.gravityAuxiliary point)
        (lorentzConnectionLinearCurvatureVariation configuration variation
          point) :=
  gravityTopologicalBFCoefficient_apply_continuous _ _
    (holonomicGravityAuxiliary_continuous configuration smooth)
    (lorentzConnectionLinearCurvatureVariation_continuous configuration smooth
      variation)

theorem holonomicFormNativeLorentzConnectionGravitySecondDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous fun point =>
      gravityTopologicalBFCoefficient
        (configuration.gravityAuxiliary point)
        (lorentzConnectionQuadraticCurvatureVariation variation point) :=
  gravityTopologicalBFCoefficient_apply_continuous _ _
    (holonomicGravityAuxiliary_continuous configuration smooth)
    (lorentzConnectionQuadraticCurvatureVariation_continuous variation)

private theorem holonomicGeneratedVolumeDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) := by
  unfold generatedVolumeDensity toContinuumPointField
  exact (holonomicCoframe_continuous configuration smooth).matrix_det.abs

theorem holonomicFormNativeLorentzConnectionFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous
      (holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
        configuration variation) := by
  have gravityContinuous :=
    holonomicFormNativeLorentzConnectionGravityFirstDensity_continuous
      configuration smooth variation
  have volumeContinuous :=
    holonomicGeneratedVolumeDensity_continuous configuration smooth
  have matterContinuous :=
    holonomicMatterLorentzFirstDensity_continuous source configuration smooth
      nondegenerate variation
  unfold holonomicFormNativeLorentzConnectionFirstVariationDensity
    formNativeLorentzConnectionFirstVariationDensity
  exact gravityContinuous.add (volumeContinuous.mul matterContinuous)

theorem holonomicFormNativeLorentzConnectionSecondVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Continuous
      (holonomicFormNativeLorentzConnectionSecondVariationDensity configuration
        variation) := by
  change Continuous fun point =>
    gravityTopologicalBFCoefficient
      (configuration.gravityAuxiliary point)
      (lorentzConnectionQuadraticCurvatureVariation variation point)
  exact
    holonomicFormNativeLorentzConnectionGravitySecondDensity_continuous
      configuration smooth variation

/-! ## Compact support generated by the primitive jet -/

@[simp] theorem gravityTopologicalBFCoefficient_zero_right
    (first : PhysicalBivector) :
    gravityTopologicalBFCoefficient first 0 = 0 := by
  unfold gravityTopologicalBFCoefficient
  rw [map_zero]
  exact gravityTopologicalWedgeCoefficient_zero_right first

@[simp] theorem matterCovariantDerivativeFirstVariationDensity_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    matterCovariantDerivativeFirstVariationDensity source chart point field
        0 = 0 := by
  have actual :=
    matterCovariantDerivativeFirstVariationDensity_add source chart point field
      (0 : LorentzianIndex -> DiracExteriorMatterCarrier) 0
  have idempotent :
      matterCovariantDerivativeFirstVariationDensity source chart point field
          0 =
        matterCovariantDerivativeFirstVariationDensity source chart point field
            0 +
          matterCovariantDerivativeFirstVariationDensity source chart point
            field 0 := by
    simpa only [add_zero] using actual
  linarith

theorem holonomicFormNativeLorentzConnectionFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint -> LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ derivativeDirection formDirection internalOut
        internalIn : LorentzianIndex,
      lorentzConnectionVariationDerivative variation point derivativeDirection
        formDirection internalOut internalIn = 0) :
    holonomicFormNativeLorentzConnectionFirstVariationDensity source chart
      configuration variation point = 0 := by
  unfold holonomicFormNativeLorentzConnectionFirstVariationDensity
    formNativeLorentzConnectionFirstVariationDensity
  rw [show lorentzConnectionLinearCurvatureVariation configuration variation
      point = 0 from
    lorentzConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero]
  rw [show holonomicMatterLorentzConnectionVariation configuration variation
      point = 0 from
    holonomicMatterLorentzConnectionVariation_eq_zero configuration variation
      point variationZero]
  simp

theorem holonomicFormNativeLorentzConnectionSecondVariationDensity_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint -> LorentzBivectorOneForm) (point : BasePoint)
    (variationZero : variation point = 0) :
    holonomicFormNativeLorentzConnectionSecondVariationDensity configuration
      variation point = 0 := by
  unfold holonomicFormNativeLorentzConnectionSecondVariationDensity
    formNativeLorentzConnectionSecondVariationDensity
  rw [show lorentzConnectionQuadraticCurvatureVariation variation point = 0
    from lorentzConnectionQuadraticCurvatureVariation_eq_zero variation point
      variationZero]
  simp

theorem holonomicFormNativeLorentzConnectionFirstVariationDensity_compact
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasCompactSupport
      (holonomicFormNativeLorentzConnectionFirstVariationDensity source chart
        configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactLorentzConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  exact
    holonomicFormNativeLorentzConnectionFirstVariationDensity_eq_zero_of_jet_zero
      source chart configuration variation point jetZero.1 jetZero.2

theorem holonomicFormNativeLorentzConnectionSecondVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasCompactSupport
      (holonomicFormNativeLorentzConnectionSecondVariationDensity configuration
        variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  exact
    holonomicFormNativeLorentzConnectionSecondVariationDensity_eq_zero
      configuration variation point variationZero

theorem holonomicFormNativeLorentzConnectionFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Integrable
      (holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
        configuration variation) :=
  (holonomicFormNativeLorentzConnectionFirstVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicFormNativeLorentzConnectionFirstVariationDensity_compact source
        0 configuration variation)

theorem holonomicFormNativeLorentzConnectionSecondVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    Integrable
      (holonomicFormNativeLorentzConnectionSecondVariationDensity configuration
        variation) :=
  (holonomicFormNativeLorentzConnectionSecondVariationDensity_continuous
    configuration smooth variation).integrable_of_hasCompactSupport
      (holonomicFormNativeLorentzConnectionSecondVariationDensity_compact
        configuration variation)

/-! ## Integrated polynomial and derivative -/

theorem holonomicFormNativeIntegratedUnifiedAction_lorentzConnection_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) :
    holonomicFormNativeIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter) =
      holonomicFormNativeIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
              configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicFormNativeLorentzConnectionSecondVariationDensity
              configuration variation point) := by
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
          (varyLorentzConnection configuration variation parameter) point)) =
      fun point =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeLorentzConnectionSecondVariationDensity
            configuration variation point := by
    funext point
    exact
      holonomicFormNativeUnifiedLocalDensity_lorentzConnection_quadratic source
        0 configuration smooth variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeLorentzConnectionFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicFormNativeLorentzConnectionSecondVariationDensity_integrable
      configuration smooth variation
  calc
    (∫ point : BasePoint,
        generatedFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeLorentzConnectionFirstVariationDensity source
                0 configuration variation point +
          parameter ^ 2 *
            holonomicFormNativeLorentzConnectionSecondVariationDensity
              configuration variation point) =
      (∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) 0 point
                (toContinuumPointField configuration point) +
              parameter *
                holonomicFormNativeLorentzConnectionFirstVariationDensity
                  source 0 configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeLorentzConnectionSecondVariationDensity
              configuration variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter *
            holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
              configuration variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeLorentzConnectionSecondVariationDensity
              configuration variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicFormNativeIntegratedUnifiedAction_lorentzConnection_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasDerivAt
      (fun parameter => holonomicFormNativeIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter))
      (∫ point : BasePoint,
        holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
          configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
      configuration variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicFormNativeLorentzConnectionSecondVariationDensity configuration
      variation point
  have actionEquality :
      (fun parameter => holonomicFormNativeIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter)) =
      fun parameter =>
        holonomicFormNativeIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact
      holonomicFormNativeIntegratedUnifiedAction_lorentzConnection_quadratic
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
    ((((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicFormNativeIntegratedUnifiedAction source 0 configuration)).add
        (((hasDerivAt_id (x := 0)).pow 2).mul_const secondIntegral))

/-! ## Action stationarity versus the generated weak coefficient -/

def FormNativeLorentzConnectionActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    HasDerivAt
      (fun parameter => holonomicFormNativeIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter))
      0 0

def FormNativeLorentzConnectionWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    (∫ point : BasePoint,
      holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
        configuration variation point) = 0

theorem formNativeLorentzConnectionActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      FormNativeHolonomicLocalDensityIntegrable source 0 configuration) :
    FormNativeLorentzConnectionActionStationary source configuration ↔
      FormNativeLorentzConnectionWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicFormNativeIntegratedUnifiedAction_lorentzConnection_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicFormNativeIntegratedUnifiedAction_lorentzConnection_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    rw [weakEquation variation] at actual
    exact actual

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeLorentzConnectionIntegratedVariation
