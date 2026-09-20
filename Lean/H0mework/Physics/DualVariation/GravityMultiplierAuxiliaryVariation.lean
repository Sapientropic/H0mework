import H0mework.Physics.DualVariation.IIPlusReductionLocalVariation
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation

/-!
# Algebraic gravity variations of the Dirac-dual form-native root

The repaired Yukawa epoch leaves the primitive multiplier and gravity-
auxiliary paths numerically unchanged, but an old action receipt cannot stand
for the new hash.  This module therefore derives the affine multiplier law and
quadratic auxiliary law directly from the repaired density, then integrates
those new-root paths using only the formulation-neutral compact-support
regularity of their coefficients.

The resulting zero fibers remain simplicity and the unique BF reaction.  No
old action derivative or stationarity theorem is used to produce them.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeGravityMultiplierAuxiliaryVariation

open EmpiricalReferenceScaleCouplingBoundary
open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineTopologicalWeakEquation
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Direct repaired-root local laws -/

@[simp] theorem generatedDiracDualFormNativeMatterDensity_withMultiplier
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) :
    generatedDiracDualFormNativeMatterDensity source chart point
        (withFormNativeGravityMultiplier field multiplier) =
      generatedDiracDualFormNativeMatterDensity source chart point field :=
  rfl

theorem
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_multiplier_affine
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point
        (withFormNativeGravityMultiplier field
          (field.gravitySimplicityMultiplier + parameter • variation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
          chart point field +
        parameter *
          formNativeGravityMultiplierFirstVariationDensity field variation := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedFormNativeGravityConstraintDensity_multiplier_affine]
  simp only [generatedFormNativeGravityBFDensity_withMultiplier,
    generatedFormNativeGaugeDensityAtBoundary_withMultiplier,
    generatedDiracDualFormNativeMatterDensity_withMultiplier]
  ring

theorem holonomicDiracDualFormNativeLocalDensity_multiplier_affine
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point
        (toContinuumPointField
          (varyFormNativeGravityMultiplier configuration variation parameter)
          point) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
          chart point (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityMultiplierFirstVariationDensity
            configuration variation point := by
  rw [toContinuumPointField_varyFormNativeGravityMultiplier]
  exact
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_multiplier_affine
      source boundary chart point (toContinuumPointField configuration point)
      (variation point) parameter

theorem holonomicDiracDualFormNativeLocalDensity_auxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point
        (toContinuumPointField
          (varyFormNativeGravityAuxiliary configuration variation parameter)
          point) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
          chart point (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityAuxiliaryFirstVariationDensity
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
            variation point := by
  rw [toContinuumPointField_varyFormNativeGravityAuxiliary]
  exact
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_auxiliary_quadratic
      source boundary chart point (toContinuumPointField configuration point)
      (variation point) parameter

/-! ## Integrated multiplier path -/

theorem holonomicDiracDualFormNativeIntegratedAction_multiplier_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (varyFormNativeGravityMultiplier configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          configuration +
        parameter *
          ∫ point : BasePoint,
            holonomicFormNativeGravityMultiplierFirstVariationDensity
              configuration variation point := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    integratedDiracDualFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise :
      (fun point : BasePoint =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField
            (varyFormNativeGravityMultiplier configuration variation parameter)
            point)) =
      fun point =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityMultiplierFirstVariationDensity
            configuration variation point := by
    funext point
    exact holonomicDiracDualFormNativeLocalDensity_multiplier_affine source
      (sourceGeneratedUnifiedCouplings source) chart point configuration
      variation parameter
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeGravityMultiplierFirstVariationDensity_integrable
      configuration smooth variation
  change Integrable (fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField configuration point)) at densityIntegrable
  rw [integral_add densityIntegrable
    (firstIntegrable.const_mul parameter), integral_const_mul]

theorem holonomicDiracDualFormNativeIntegratedAction_multiplier_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityMultiplier configuration variation parameter))
      (∫ point : BasePoint,
        holonomicFormNativeGravityMultiplierFirstVariationDensity
          configuration variation point) 0 := by
  let coefficient := ∫ point : BasePoint,
    holonomicFormNativeGravityMultiplierFirstVariationDensity
      configuration variation point
  have formula :
      (fun parameter : ℝ =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityMultiplier configuration variation parameter)) =
      fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
            configuration +
          parameter * coefficient := by
    funext parameter
    exact holonomicDiracDualFormNativeIntegratedAction_multiplier_affine
      source chart configuration smooth densityIntegrable variation parameter
  rw [formula]
  simpa [coefficient] using
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const coefficient).const_add
      (holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        configuration)

/-! ## Integrated gravity-auxiliary path -/

theorem holonomicDiracDualFormNativeIntegratedAction_auxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (varyFormNativeGravityAuxiliary configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicFormNativeGravityAuxiliaryFirstVariationDensity
              configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
              variation point) := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    integratedDiracDualFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise :
      (fun point : BasePoint =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField
            (varyFormNativeGravityAuxiliary configuration variation parameter)
            point)) =
      fun point =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityAuxiliaryFirstVariationDensity
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
            variation point := by
    funext point
    exact holonomicDiracDualFormNativeLocalDensity_auxiliary_quadratic source
      (sourceGeneratedUnifiedCouplings source) chart point configuration
      variation parameter
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeGravityAuxiliaryFirstVariationDensity_integrable
      configuration smooth variation
  have quadraticIntegrable :=
    holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_integrable
      variation
  change Integrable (fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField configuration point)) at densityIntegrable
  calc
    (∫ point : BasePoint,
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeGravityAuxiliaryFirstVariationDensity
                configuration variation point +
          parameter ^ 2 *
            holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
              variation point) =
      (∫ point : BasePoint,
          generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) chart point
                (toContinuumPointField configuration point) +
              parameter *
                holonomicFormNativeGravityAuxiliaryFirstVariationDensity
                  configuration variation point) +
        ∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
              variation point := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (quadraticIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) chart point
            (toContinuumPointField configuration point)) +
        ∫ point : BasePoint,
          parameter *
            holonomicFormNativeGravityAuxiliaryFirstVariationDensity
              configuration variation point) +
        ∫ point : BasePoint,
          parameter ^ 2 *
            holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
              variation point := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicDiracDualFormNativeIntegratedAction_auxiliary_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityAuxiliary configuration variation parameter))
      (∫ point : BasePoint,
        holonomicFormNativeGravityAuxiliaryFirstVariationDensity
          configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicFormNativeGravityAuxiliaryFirstVariationDensity
      configuration variation point
  let quadraticIntegral := ∫ point : BasePoint,
    holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
      variation point
  have formula :
      (fun parameter : ℝ =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityAuxiliary configuration variation parameter)) =
      fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
            configuration +
          parameter * firstIntegral + parameter ^ 2 * quadraticIntegral := by
    funext parameter
    exact holonomicDiracDualFormNativeIntegratedAction_auxiliary_quadratic
      source chart configuration smooth densityIntegrable variation parameter
  rw [formula]
  change HasDerivAt
    ((fun parameter =>
      holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          configuration + parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * quadraticIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstIntegral).const_add
      (holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        configuration)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const quadraticIntegral))

/-! ## New-hash stationarity and unchanged faithful zero fibers -/

def DiracDualFormNativeGravityMultiplierActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityMultiplier configuration variation parameter))
      0 0

def DiracDualFormNativeGravityAuxiliaryActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityAuxiliary configuration variation parameter))
      0 0

theorem diracDualFormNativeGravityMultiplierActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    DiracDualFormNativeGravityMultiplierActionStationary source chart
        configuration ↔
      FormNativeGravityMultiplierWeakEquation configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedAction_multiplier_hasDerivAt
        source chart configuration smooth densityIntegrable variation
    have coefficientZero :
        (∫ point : BasePoint,
          holonomicFormNativeGravityMultiplierFirstVariationDensity
            configuration variation point) = 0 :=
      ((stationary variation).unique actual).symm
    simpa only [FormNativeGravityMultiplierWeakEquation,
      TopologicalGravityWeakEquation,
      holonomicFormNativeGravityMultiplierFirstVariationDensity_eq_pairing]
      using coefficientZero
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedAction_multiplier_hasDerivAt
        source chart configuration smooth densityIntegrable variation
    have coefficientZero :
        (∫ point : BasePoint,
          holonomicFormNativeGravityMultiplierFirstVariationDensity
            configuration variation point) = 0 := by
      simpa only [FormNativeGravityMultiplierWeakEquation,
        TopologicalGravityWeakEquation,
        holonomicFormNativeGravityMultiplierFirstVariationDensity_eq_pairing]
        using weakEquation variation
    simpa [coefficientZero] using actual

theorem diracDualFormNativeGravityMultiplierActionStationary_iff_simplicity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    DiracDualFormNativeGravityMultiplierActionStationary source chart
        configuration ↔
      FormNativeGravitySimplicityEquation configuration := by
  rw [diracDualFormNativeGravityMultiplierActionStationary_iff_weakEquation
    source chart configuration smooth densityIntegrable]
  rw [formNativeGravityMultiplierWeakEquation_iff_residual_eq_zero
    configuration smooth]
  exact formNativeGravityMultiplierResidual_eq_zero_iff_simplicity
    configuration

theorem diracDualFormNativeGravityAuxiliaryActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    DiracDualFormNativeGravityAuxiliaryActionStationary source chart
        configuration ↔
      FormNativeGravityAuxiliaryWeakEquation configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedAction_auxiliary_hasDerivAt
        source chart configuration smooth densityIntegrable variation
    have coefficientZero :
        (∫ point : BasePoint,
          holonomicFormNativeGravityAuxiliaryFirstVariationDensity
            configuration variation point) = 0 :=
      ((stationary variation).unique actual).symm
    simpa only [FormNativeGravityAuxiliaryWeakEquation,
      TopologicalGravityWeakEquation,
      holonomicFormNativeGravityAuxiliaryFirstVariationDensity_eq_pairing]
      using coefficientZero
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedAction_auxiliary_hasDerivAt
        source chart configuration smooth densityIntegrable variation
    have coefficientZero :
        (∫ point : BasePoint,
          holonomicFormNativeGravityAuxiliaryFirstVariationDensity
            configuration variation point) = 0 := by
      simpa only [FormNativeGravityAuxiliaryWeakEquation,
        TopologicalGravityWeakEquation,
        holonomicFormNativeGravityAuxiliaryFirstVariationDensity_eq_pairing]
        using weakEquation variation
    simpa [coefficientZero] using actual

theorem diracDualFormNativeGravityAuxiliaryActionStationary_iff_reaction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    DiracDualFormNativeGravityAuxiliaryActionStationary source chart
        configuration ↔
      configuration.gravitySimplicityMultiplier =
        formNativeGravityReactionField configuration := by
  rw [diracDualFormNativeGravityAuxiliaryActionStationary_iff_weakEquation
    source chart configuration smooth densityIntegrable]
  rw [formNativeGravityAuxiliaryWeakEquation_iff_equation configuration smooth]
  exact formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
    configuration

/-- Same-new-action checkpoint for the two algebraic gravity legs. -/
theorem diracDualFormNativeGravityMultiplierAndAuxiliaryActionStationary_iff
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : DiracDualFormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    (DiracDualFormNativeGravityMultiplierActionStationary source chart
        configuration ∧
      DiracDualFormNativeGravityAuxiliaryActionStationary source chart
        configuration) ↔
      (FormNativeGravitySimplicityEquation configuration ∧
        configuration.gravitySimplicityMultiplier =
          formNativeGravityReactionField configuration) := by
  rw [diracDualFormNativeGravityMultiplierActionStationary_iff_simplicity
    source chart configuration smooth densityIntegrable]
  rw [diracDualFormNativeGravityAuxiliaryActionStationary_iff_reaction
    source chart configuration smooth densityIntegrable]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeGravityMultiplierAuxiliaryVariation
