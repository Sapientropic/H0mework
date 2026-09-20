import H0mework.Physics.Lorentz.LorentzConnectionVariationDensity

/-!
# S9-C3b3: integrated Lorentz connection derivative and weak equation

The exact local polynomial from C3b1 and the analytic density control from
C3b2 are combined at the one actual integrated action.  This produces an
honest derivative along every compactly supported primitive Lorentz-skew
connection variation.  Stationarity then implies the weak equation by
uniqueness of derivatives.

The theorem consumes no spin current, curvature increment, integrability,
stationarity Boolean, or field-equation certificate from the source mouth.
Integration by parts and extraction of the pointwise Einstein--Cartan
connection equation remain downstream obligations.
-/

namespace SaturationMonoid.PhysicsCore.StageNineLorentzConnectionWeakEquation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNinePlebanskiMultiplierVariation
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionActionVariation
open StageNineLorentzConnectionVariationDensity
open MeasureTheory

noncomputable section

set_option maxHeartbeats 600000

theorem holonomicIntegratedUnifiedAction_lorentzConnection_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter) =
      holonomicIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicLorentzConnectionFirstVariationDensity source 0
              configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicLorentzConnectionSecondVariationDensity configuration
              variation point) := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyLorentzConnection configuration variation parameter) point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicLorentzConnectionFirstVariationDensity source 0
            configuration variation point +
        parameter ^ 2 *
          holonomicLorentzConnectionSecondVariationDensity configuration
            variation point := by
    funext point
    exact holonomicLocalDensity_lorentzConnection_quadratic source 0
      configuration smooth variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicLorentzConnectionFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicLorentzConnectionSecondVariationDensity_integrable configuration
      smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicLorentzConnectionFirstVariationDensity source 0
                configuration variation point +
          parameter ^ 2 *
            holonomicLorentzConnectionSecondVariationDensity configuration
              variation point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicLorentzConnectionFirstVariationDensity source 0
                configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicLorentzConnectionSecondVariationDensity configuration
              variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter *
            holonomicLorentzConnectionFirstVariationDensity source 0
              configuration variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            holonomicLorentzConnectionSecondVariationDensity configuration
              variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicIntegratedUnifiedAction_lorentzConnection_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter))
      (∫ point : BasePoint,
        holonomicLorentzConnectionFirstVariationDensity source 0 configuration
          variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicLorentzConnectionFirstVariationDensity source 0 configuration
      variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicLorentzConnectionSecondVariationDensity configuration variation
      point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_lorentzConnection_quadratic source
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

/-- Stationarity of a candidate primitive configuration under every compactly
supported Lorentz-skew connection variation.  This is not source data. -/
def CanonicalLorentzConnectionActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter))
      0 0

def CanonicalLorentzConnectionWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    (∫ point : BasePoint,
      holonomicLorentzConnectionFirstVariationDensity source 0 configuration
        variation point) = 0

theorem canonicalLorentzConnectionActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalLorentzConnectionActionStationary source
      configuration) :
    CanonicalLorentzConnectionWeakEquation source configuration := by
  intro variation
  have actual :=
    holonomicIntegratedUnifiedAction_lorentzConnection_hasDerivAt source
      configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

end

end SaturationMonoid.PhysicsCore.StageNineLorentzConnectionWeakEquation
