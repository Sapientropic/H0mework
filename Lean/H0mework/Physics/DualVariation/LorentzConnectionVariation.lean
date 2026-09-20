import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.Lorentz.LorentzConnectionIntegratedVariation

/-!
# Lorentz-connection variation of the Dirac-dual form-native root

The repaired Yukawa vector is algebraic in the scalar and matter fields, so a
primitive Lorentz-connection path changes only the unchanged BF curvature and
Dirac kinetic derivative channels.  This module proves that fact directly at
the repaired density, then rebuilds the integrated quadratic path and its
stationarity/weak-equation correspondence under the new action hash.

The historical action derivative is not used.  Only its action-neutral jet,
coefficient regularity, compact-support, and weak-coefficient interfaces are
reused.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLorentzConnectionVariation

open DiracExteriorMatterAction
open EmpiricalReferenceScaleCouplingBoundary
open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzConnectionIntegratedVariation
open StageNineFormNativeLorentzConnectionLocalVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionActualVariationCore
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineScalarLocalSpinDensity
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Direct repaired matter polynomial -/

@[simp] theorem generatedDensitizedContinuumScalarDensity_withLorentzConnectionJets
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (gravityCurvature : PhysicalBivector)
    (matterDerivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    generatedDensitizedContinuumScalarDensity source chart point
        (withLorentzConnectionJets field gravityCurvature matterDerivative) =
      generatedDensitizedContinuumScalarDensity source chart point field :=
  rfl

@[simp] theorem
    generatedDensitizedContinuumDiracDualYukawaDensity_withLorentzConnectionJets
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (gravityCurvature : PhysicalBivector)
    (matterDerivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    generatedDensitizedContinuumDiracDualYukawaDensity source chart point
        (withLorentzConnectionJets field gravityCurvature matterDerivative) =
      generatedDensitizedContinuumDiracDualYukawaDensity source chart point
        field :=
  rfl

theorem
    generatedDensitizedContinuumMatterKineticDensity_withLorentzConnectionJets_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (gravityCurvature : PhysicalBivector)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedDensitizedContinuumMatterKineticDensity source chart point
        (withLorentzConnectionJets field gravityCurvature
          (field.matterCovariantDerivative + parameter • variation)) =
      generatedDensitizedContinuumMatterKineticDensity source chart point
          field +
        parameter *
          (generatedVolumeDensity field *
            matterCovariantDerivativeFirstVariationDensity source chart point
              field variation) := by
  change
    generatedVolumeDensity field *
        (matterDualFrameRelative source chart point field.conjugateMatter
          (matterCovariantDerivativeVariationVector source chart point field
            (field.matterCovariantDerivative + parameter • variation))).re =
      generatedVolumeDensity field *
          (matterDualFrameRelative source chart point field.conjugateMatter
            (matterCovariantDerivativeVariationVector source chart point field
              field.matterCovariantDerivative)).re +
        parameter *
          (generatedVolumeDensity field *
            matterCovariantDerivativeFirstVariationDensity source chart point
              field variation)
  rw [matterCovariantDerivativeVariationVector_add, map_add,
    Complex.add_re]
  have scaled :
      (matterDualFrameRelative source chart point field.conjugateMatter
        (matterCovariantDerivativeVariationVector source chart point field
          (parameter • variation))).re =
        parameter *
          matterCovariantDerivativeFirstVariationDensity source chart point
            field variation := by
    rw [← matterCovariantDerivativeFirstVariationDensity_real_smul]
    rfl
  rw [scaled]
  ring

theorem generatedDiracDualFormNativeMatterDensity_withLorentzConnectionJets_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (gravityCurvature : PhysicalBivector)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedDiracDualFormNativeMatterDensity source chart point
        (withLorentzConnectionJets field gravityCurvature
          (field.matterCovariantDerivative + parameter • variation)) =
      generatedDiracDualFormNativeMatterDensity source chart point field +
        parameter *
          (generatedVolumeDensity field *
            matterCovariantDerivativeFirstVariationDensity source chart point
              field variation) := by
  unfold generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumDiracDualMatterDensity
  rw [generatedDensitizedContinuumScalarDensity_withLorentzConnectionJets,
    generatedDensitizedContinuumMatterKineticDensity_withLorentzConnectionJets_affine,
    generatedDensitizedContinuumDiracDualYukawaDensity_withLorentzConnectionJets]
  ring

/-! ## Direct repaired local action polynomial -/

theorem
    generatedDiracDualFormNativeUnifiedLocalDensity_lorentzConnectionJets_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (linearCurvature quadraticCurvature : PhysicalBivector)
    (matterVariation : LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point
        (withLorentzConnectionJets field
          (field.gravityCurvature + parameter • linearCurvature +
            parameter ^ 2 • quadraticCurvature)
          (field.matterCovariantDerivative + parameter • matterVariation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
          chart point field +
        parameter *
          formNativeLorentzConnectionFirstVariationDensity source chart point
            field linearCurvature matterVariation +
        parameter ^ 2 *
          formNativeLorentzConnectionSecondVariationDensity field
            quadraticCurvature := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  have gravityExpansion :=
    generatedFormNativeGravityBFDensity_withLorentzConnectionJets_quadratic
      field linearCurvature quadraticCurvature parameter
      (field.matterCovariantDerivative + parameter • matterVariation)
  have matterExpansion :=
    generatedDiracDualFormNativeMatterDensity_withLorentzConnectionJets_affine
      source chart point field
      (field.gravityCurvature + parameter • linearCurvature +
        parameter ^ 2 • quadraticCurvature)
      matterVariation parameter
  have constraintReadout :
      generatedFormNativeGravityConstraintDensity
          (withLorentzConnectionJets field
            (field.gravityCurvature + parameter • linearCurvature +
              parameter ^ 2 • quadraticCurvature)
            (field.matterCovariantDerivative + parameter • matterVariation)) =
        generatedFormNativeGravityConstraintDensity field :=
    rfl
  have gaugeReadout :
      generatedFormNativeGaugeDensityAtBoundary boundary
          (withLorentzConnectionJets field
            (field.gravityCurvature + parameter • linearCurvature +
              parameter ^ 2 • quadraticCurvature)
            (field.matterCovariantDerivative + parameter • matterVariation)) =
        generatedFormNativeGaugeDensityAtBoundary boundary field :=
    rfl
  rw [gravityExpansion, constraintReadout, gaugeReadout, matterExpansion]
  unfold formNativeLorentzConnectionFirstVariationDensity
    formNativeLorentzConnectionSecondVariationDensity
  ring

theorem
    holonomicDiracDualFormNativeUnifiedLocalDensity_lorentzConnection_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField
          (varyLorentzConnection configuration variation parameter) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeLorentzConnectionFirstVariationDensity source chart
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeLorentzConnectionSecondVariationDensity
            configuration variation point := by
  rw [toContinuumPointField_varyLorentzConnection configuration smooth
    variation parameter point]
  exact
    generatedDiracDualFormNativeUnifiedLocalDensity_lorentzConnectionJets_quadratic
      source (sourceGeneratedUnifiedCouplings source) chart point
      (toContinuumPointField configuration point)
      (lorentzConnectionLinearCurvatureVariation configuration variation point)
      (lorentzConnectionQuadraticCurvatureVariation variation point)
      (holonomicMatterLorentzConnectionVariation configuration variation point)
      parameter

/-! ## Integrated new-root polynomial and derivative -/

theorem
    holonomicDiracDualFormNativeIntegratedUnifiedAction_lorentzConnection_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm)
    (parameter : ℝ) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        (varyLorentzConnection configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicFormNativeLorentzConnectionFirstVariationDensity source 0
              configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicFormNativeLorentzConnectionSecondVariationDensity
              configuration variation point) := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    integratedDiracDualFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  change Integrable (fun point : BasePoint =>
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point
      (toContinuumPointField configuration point)) at densityIntegrable
  have pointwise : (fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyLorentzConnection configuration variation parameter) point)) =
      fun point =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
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
      holonomicDiracDualFormNativeUnifiedLocalDensity_lorentzConnection_quadratic
        source 0 configuration smooth variation parameter point
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeLorentzConnectionFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable :=
    holonomicFormNativeLorentzConnectionSecondVariationDensity_integrable
      configuration smooth variation
  calc
    (∫ point : BasePoint,
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeLorentzConnectionFirstVariationDensity source
                0 configuration variation point +
          parameter ^ 2 *
            holonomicFormNativeLorentzConnectionSecondVariationDensity
              configuration variation point) =
      (∫ point : BasePoint,
          generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
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
          generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
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

theorem
    holonomicDiracDualFormNativeIntegratedUnifiedAction_lorentzConnection_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm) :
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
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
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyLorentzConnection configuration variation parameter)) =
      fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
            configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact
      holonomicDiracDualFormNativeIntegratedUnifiedAction_lorentzConnection_quadratic
        source configuration smooth nondegenerate densityIntegrable variation
        parameter
  rw [actionEquality]
  change HasDerivAt
    ((fun parameter =>
      holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          configuration + parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * secondIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        configuration)).add
      (((hasDerivAt_id (x := 0)).pow 2).mul_const secondIntegral))

/-! ## New-hash stationarity -/

def DiracDualFormNativeLorentzConnectionActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzBivectorOneForm,
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyLorentzConnection configuration variation parameter))
      0 0

theorem diracDualFormNativeLorentzConnectionActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    DiracDualFormNativeLorentzConnectionActionStationary source
        configuration ↔
      FormNativeLorentzConnectionWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_lorentzConnection_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_lorentzConnection_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    rw [weakEquation variation] at actual
    exact actual

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeLorentzConnectionVariation
