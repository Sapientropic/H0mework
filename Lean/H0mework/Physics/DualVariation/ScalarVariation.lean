import H0mework.Physics.DualVariation.ConjugateMatterVariation
import H0mework.Physics.Geometry.ScalarPointwiseEquation

/-!
# Dirac-dual form-native scalar variation

The primitive scalar path, gauge-covariant first jet, kinetic coefficient,
potential coefficient, and second-order scalar coefficient are unchanged.
The scalar derivative of the Yukawa block is not: it is generated again from
the repaired right-chiral Dirac-dual operator, and every action-dependent
derivative and pointwise receipt is reissued for the active root hash.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeScalarVariation

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction
open StageNineFundamentalLemma
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePlebanskiMultiplierVariation
open StageNineScalarLocalSpinDensity
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterFullVariations
open MeasureTheory

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Repaired scalar Yukawa coefficient -/

def diracDualScalarYukawaVariationVector
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier) : DiracExteriorMatterCarrier :=
  diracDualRightChiralYukawaAction
    (scalarCoordinateEquiv.symm variation) field.matter

def diracDualScalarYukawaFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier) : ℝ :=
  (field.conjugateMatter
    (diracDualScalarYukawaVariationVector field variation)).re

def diracDualScalarFirstVariationDensity
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (derivativeVariation : LorentzianIndex → ScalarCoordinateCarrier) : ℝ :=
  generatedVolumeDensity field *
    (scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
        derivativeVariation -
      scalarPotentialFirstVariation source field variation +
      diracDualScalarYukawaFirstVariationDensity field variation)

theorem diracDualScalarYukawaFirstVariationDensity_real_smul
    (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity field
        (parameter • variation) =
      parameter *
        diracDualScalarYukawaFirstVariationDensity field variation := by
  unfold diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  rw [show scalarCoordinateEquiv.symm (parameter • variation) =
      (parameter : ℂ) • scalarCoordinateEquiv.symm variation by
    change scalarCoordinateEquiv.symm ((parameter : ℂ) • variation) = _
    rw [map_smul]]
  rw [diracDualRightChiralYukawaAction_smul, LinearMap.smul_apply, map_smul]
  simp [Complex.mul_re]

theorem generatedContinuumDiracDualYukawaVector_withScalarJets_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedContinuumDiracDualYukawaVector source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation) scalarDerivative) =
      generatedContinuumDiracDualYukawaVector source 0 point field +
        parameter • diracDualScalarYukawaVariationVector field variation := by
  unfold generatedContinuumDiracDualYukawaVector
    diracDualScalarYukawaVariationVector
  simp only [withScalarJets, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart]
  rw [map_add]
  rw [show scalarCoordinateEquiv.symm (parameter • variation) =
      (parameter : ℂ) • scalarCoordinateEquiv.symm variation by
    change scalarCoordinateEquiv.symm ((parameter : ℂ) • variation) = _
    rw [map_smul]]
  rw [diracDualRightChiralYukawaAction_add,
    diracDualRightChiralYukawaAction_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  module

theorem generatedContinuumDiracDualMatterVector_withScalarJets_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation) scalarDerivative) =
      generatedContinuumDiracDualMatterVector source 0 point field +
        parameter • diracDualScalarYukawaVariationVector field variation := by
  have kineticUnchanged :
      generatedContinuumMatterKineticVector source 0 point
          (withScalarJets field
            (field.scalar + parameter • variation) scalarDerivative) =
        generatedContinuumMatterKineticVector source 0 point field := rfl
  unfold generatedContinuumDiracDualMatterVector
  rw [kineticUnchanged,
    generatedContinuumDiracDualYukawaVector_withScalarJets_affine]
  module

theorem
    generatedDensitizedContinuumDiracDualMatterDensity_withScalarJets_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedDensitizedContinuumDiracDualMatterDensity source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation) scalarDerivative) =
      generatedDensitizedContinuumDiracDualMatterDensity source 0 point field +
        parameter *
          (generatedVolumeDensity field *
            diracDualScalarYukawaFirstVariationDensity field variation) := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    generatedContinuumDiracDualMatterVector_withScalarJets_affine, map_add,
    StageNineMatterCovariantDerivativeAffine.matterDualFrameRelative_real_smul]
  simp only [withScalarJets, generatedVolumeDensity,
    StageNineP286GaugeConnectionVariationDensity.matterDualFrameRelative_zeroChart,
    Complex.add_re]
  unfold diracDualScalarYukawaFirstVariationDensity
  simp [Complex.mul_re]
  ring

/-- Direct quadratic expansion of the active root along the primitive scalar
path.  The repaired Yukawa leg contributes only to the linear coefficient. -/
theorem generatedDiracDualFormNativeUnifiedLocalDensity_withScalarJets_quadratic
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (derivativeVariation : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withScalarJets field
          (field.scalar + parameter • variation)
          (field.scalarCovariantDerivative +
            parameter • derivativeVariation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point field +
        parameter * diracDualScalarFirstVariationDensity source point field
          variation derivativeVariation +
        parameter ^ 2 * scalarSecondVariationDensity source point field
          variation derivativeVariation := by
  let variedField := withScalarJets field
    (field.scalar + parameter • variation)
    (field.scalarCovariantDerivative + parameter • derivativeVariation)
  have gravityBFUnchanged :
      generatedFormNativeGravityBFDensity variedField =
        generatedFormNativeGravityBFDensity field := rfl
  have constraintUnchanged :
      generatedFormNativeGravityConstraintDensity variedField =
        generatedFormNativeGravityConstraintDensity field := rfl
  have gaugeUnchanged :
      generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source) variedField =
        generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source) field := rfl
  change
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point variedField = _
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    generatedDiracDualFormNativeMatterDensity
    generatedDensitizedContinuumScalarDensity
  rw [gravityBFUnchanged, constraintUnchanged, gaugeUnchanged,
    generatedScalarKineticDensity_withScalarJets_quadratic,
    generatedScalarPotential_withScalarJets_quadratic,
    generatedDensitizedContinuumDiracDualMatterDensity_withScalarJets_affine]
  dsimp only [variedField, withScalarJets]
  unfold diracDualScalarFirstVariationDensity scalarSecondVariationDensity
  simp only [generatedVolumeDensity]
  ring

def holonomicDiracDualScalarFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  diracDualScalarFirstVariationDensity source point
    (toContinuumPointField configuration point) (variation point)
    (holonomicScalarVariationCovariantDerivative configuration variation point)

theorem holonomicDiracDualFormNativeLocalDensity_scalar_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (varyScalarCoordinates configuration variation parameter) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicDiracDualScalarFirstVariationDensity source configuration
            variation point +
        parameter ^ 2 * holonomicScalarSecondVariationDensity source
          configuration variation point := by
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
  rw [toContinuumPointField_varyScalarCoordinates configuration smooth]
  exact
    generatedDiracDualFormNativeUnifiedLocalDensity_withScalarJets_quadratic
      source point (toContinuumPointField configuration point) (variation point)
      (holonomicScalarVariationCovariantDerivative configuration variation
        point) parameter

/-! ## Analytic control of the repaired first density -/

theorem holonomicDiracDualScalarYukawaVariationVector_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField configuration point) (variation point)) := by
  have actual := diracDualYukawaCoordinate_apply_continuous variation
    (fun point => matterCoordinateEquiv (configuration.matter point))
    variation.smooth.continuous
    smooth.2.2.2.2.2.2.2.1.continuous
  unfold diracDualScalarYukawaVariationVector
  exact actual.congr fun point => by
    simp only [toContinuumPointField]
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (variation point))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicDiracDualScalarYukawaFirstVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField configuration point) (variation point) := by
  let vector := fun point =>
    diracDualScalarYukawaVariationVector
      (toContinuumPointField configuration point) (variation point)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    holonomicDiracDualScalarYukawaVariationVector_coordinate_continuous
      configuration smooth variation
  have pairingSumContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorEntryContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          vectorCoordinateContinuous
    have dualEntryContinuous : Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
      (smooth.2.2.2.2.2.2.2.2 index).continuous
    exact vectorEntryContinuous.mul dualEntryContinuous
  have dualPairingContinuous : Continuous fun point =>
      configuration.conjugateMatter point (vector point) := by
    rw [show (fun point =>
        configuration.conjugateMatter point (vector point)) =
      fun point => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext point
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        matterDual_coordinate_expansion (configuration.conjugateMatter point)
          (matterCoordinateEquiv (vector point))]
    exact pairingSumContinuous
  unfold diracDualScalarYukawaFirstVariationDensity
  exact (Complex.continuous_re.comp dualPairingContinuous).congr fun point => by
    simp only [Function.comp_apply, toContinuumPointField, vector]

theorem holonomicDiracDualScalarFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous
      (holonomicDiracDualScalarFirstVariationDensity source configuration
        variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have kineticContinuous :=
    holonomicScalarKineticFirstVariationDensity_continuous source configuration
      smooth nondegenerate variation
  have potentialContinuous :=
    holonomicScalarPotentialFirstVariation_continuous source configuration smooth
      variation
  have yukawaContinuous :=
    holonomicDiracDualScalarYukawaFirstVariationDensity_continuous configuration
      smooth variation
  unfold holonomicDiracDualScalarFirstVariationDensity
    diracDualScalarFirstVariationDensity
  exact volumeContinuous.mul
    ((kineticContinuous.sub potentialContinuous).add yukawaContinuous)

@[simp] theorem diracDualScalarYukawaVariationVector_zero
    (field : StageNineContinuumPointField) :
    diracDualScalarYukawaVariationVector field 0 = 0 := by
  have actionZero :
      diracDualRightChiralYukawaAction
          (0 : ExteriorBreakingScalarCarrier) = 0 := by
    have actual := diracDualRightChiralYukawaAction_smul (0 : ℂ)
      (0 : ExteriorBreakingScalarCarrier)
    simpa using actual
  unfold diracDualScalarYukawaVariationVector
  rw [map_zero, actionZero]
  simp

@[simp] theorem diracDualScalarYukawaFirstVariationDensity_zero
    (field : StageNineContinuumPointField) :
    diracDualScalarYukawaFirstVariationDensity field 0 = 0 := by
  simp [diracDualScalarYukawaFirstVariationDensity]

theorem holonomicDiracDualScalarFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ direction : LorentzianIndex,
      scalarVariationCoordinateDerivative variation point direction = 0) :
    holonomicDiracDualScalarFirstVariationDensity source configuration variation
        point = 0 := by
  have covariantDerivativeZero :=
    holonomicScalarVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero
  unfold holonomicDiracDualScalarFirstVariationDensity
    diracDualScalarFirstVariationDensity
  rw [variationZero, covariantDerivativeZero]
  simp

theorem holonomicDiracDualScalarFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    HasCompactSupport
      (holonomicDiracDualScalarFirstVariationDensity source configuration
        variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards [compactScalarVariation_eventually_jet_zero variation] with
    point jetZero
  exact holonomicDiracDualScalarFirstVariationDensity_eq_zero_of_jet_zero source
    configuration variation point jetZero.1 jetZero.2

theorem holonomicDiracDualScalarFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Integrable
      (holonomicDiracDualScalarFirstVariationDensity source configuration
        variation) :=
  (holonomicDiracDualScalarFirstVariationDensity_continuous source configuration
    smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicDiracDualScalarFirstVariationDensity_compact source
        configuration variation)

/-! ## Integrated quadratic law and weak equation -/

theorem holonomicDiracDualFormNativeIntegratedUnifiedAction_scalar_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        (varyScalarCoordinates configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicDiracDualScalarFirstVariationDensity source configuration
              variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicScalarSecondVariationDensity source configuration
              variation point) := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    integratedDiracDualFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyScalarCoordinates configuration variation parameter) point)) =
      fun point =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicDiracDualScalarFirstVariationDensity source configuration
            variation point +
        parameter ^ 2 * holonomicScalarSecondVariationDensity source
          configuration variation point := by
    funext point
    exact holonomicDiracDualFormNativeLocalDensity_scalar_quadratic source
      configuration smooth variation parameter point
  rw [pointwise]
  have baseIntegrable : Integrable fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField configuration point) := by
    simpa [DiracDualFormNativeHolonomicLocalDensityIntegrable,
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity] using
      densityIntegrable
  have firstIntegrable :=
    holonomicDiracDualScalarFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  have secondIntegrable := holonomicScalarSecondVariationDensity_integrable
    source configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicDiracDualScalarFirstVariationDensity source
                configuration variation point +
          parameter ^ 2 * holonomicScalarSecondVariationDensity source
            configuration variation point) =
      (∫ point : BasePoint,
          generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) 0 point
                (toContinuumPointField configuration point) +
              parameter *
                holonomicDiracDualScalarFirstVariationDensity source
                  configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicScalarSecondVariationDensity source
            configuration variation point) := by
      exact integral_add
        (baseIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter *
            holonomicDiracDualScalarFirstVariationDensity source configuration
              variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicScalarSecondVariationDensity source
            configuration variation point) := by
      rw [integral_add baseIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicDiracDualFormNativeIntegratedUnifiedAction_scalar_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyScalarCoordinates configuration variation parameter))
      (∫ point : BasePoint,
        holonomicDiracDualScalarFirstVariationDensity source configuration
          variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicDiracDualScalarFirstVariationDensity source configuration variation
      point
  let secondIntegral := ∫ point : BasePoint,
    holonomicScalarSecondVariationDensity source configuration variation point
  have actionEquality :
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyScalarCoordinates configuration variation parameter)) =
      fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
            configuration + parameter * firstIntegral +
          parameter ^ 2 * secondIntegral := by
    funext parameter
    exact
      holonomicDiracDualFormNativeIntegratedUnifiedAction_scalar_quadratic
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

def DiracDualFormNativeScalarActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier,
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyScalarCoordinates configuration variation parameter))
      0 0

def DiracDualFormNativeScalarWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier,
    (∫ point : BasePoint,
      holonomicDiracDualScalarFirstVariationDensity source configuration
        variation point) = 0

theorem diracDualFormNativeScalarActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    DiracDualFormNativeScalarActionStationary source configuration ↔
      DiracDualFormNativeScalarWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_scalar_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_scalar_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    simpa only [weakEquation variation] using actual

/-! ## Repaired algebraic scalar coefficient -/

def diracDualScalarAlgebraicDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarVariationAlgebraicDirection configuration direction
          point) -
      scalarPotentialFirstVariation source
        (toContinuumPointField configuration point) direction +
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField configuration point) direction)

theorem holonomicDiracDualScalarFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicDiracDualScalarFirstVariationDensity source configuration
        (scalarTimesScalarVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          scalarDifferentialMomentum source configuration direction
            derivativeDirection point) +
        variation point *
          diracDualScalarAlgebraicDirectionalCoefficient source configuration
            direction point := by
  unfold holonomicDiracDualScalarFirstVariationDensity
    diracDualScalarFirstVariationDensity scalarDifferentialMomentum
    diracDualScalarAlgebraicDirectionalCoefficient
  rw [holonomicScalarVariationCovariantDerivative_scalarTimes_as_sum]
  change
    generatedVolumeDensity (toContinuumPointField configuration point) *
      (scalarKineticFirstVariationLinear source point
          (toContinuumPointField configuration point)
          ((∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative variation point derivativeDirection •
              scalarVariationDifferentialDirection direction
                derivativeDirection) +
            variation point •
              holonomicScalarVariationAlgebraicDirection configuration
                direction point) -
        scalarPotentialFirstVariation source
          (toContinuumPointField configuration point)
          (scalarTimesScalarVariation direction variation point) +
        diracDualScalarYukawaFirstVariationDensity
          (toContinuumPointField configuration point)
          (scalarTimesScalarVariation direction variation point)) = _
  rw [map_add, map_sum]
  simp_rw [map_smul]
  simp only [scalarKineticFirstVariationLinear_apply, smul_eq_mul,
    scalarTimesScalarVariation_apply,
    scalarPotentialFirstVariation_real_smul,
    diracDualScalarYukawaFirstVariationDensity_real_smul]
  calc
    _ = generatedVolumeDensity (toContinuumPointField configuration point) *
          (∑ derivativeDirection : LorentzianIndex,
            fieldDirectionalDerivative variation point derivativeDirection *
              scalarGaugeConnectionKineticFirstVariationDensity source 0 point
                (toContinuumPointField configuration point)
                (scalarVariationDifferentialDirection direction
                  derivativeDirection)) +
        variation point *
          (generatedVolumeDensity (toContinuumPointField configuration point) *
            (scalarGaugeConnectionKineticFirstVariationDensity source 0 point
                (toContinuumPointField configuration point)
                (holonomicScalarVariationAlgebraicDirection configuration
                  direction point) -
              scalarPotentialFirstVariation source
                (toContinuumPointField configuration point) direction +
              diracDualScalarYukawaFirstVariationDensity
                (toContinuumPointField configuration point) direction)) := by
      ring
    _ = _ := by
      apply congrArg₂ (fun left right : ℝ => left + right)
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro derivativeDirection _
        ring
      · rfl

/-! ## Continuity of the repaired algebraic residual -/

theorem
    diracDualScalarYukawaConstantDirectionVector_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : ScalarCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracDualScalarYukawaVariationVector
          (toContinuumPointField configuration point) direction) := by
  have actual := diracDualYukawaCoordinate_apply_continuous
    (fun _ : BasePoint => direction)
    (fun point => matterCoordinateEquiv (configuration.matter point))
    continuous_const smooth.2.2.2.2.2.2.2.1.continuous
  unfold diracDualScalarYukawaVariationVector
  exact actual.congr fun point => by
    simp only [toContinuumPointField]
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem diracDualScalarYukawaConstantDirectionDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : ScalarCoordinateCarrier) :
    Continuous fun point =>
      diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField configuration point) direction := by
  let vector := fun point =>
    diracDualScalarYukawaVariationVector
      (toContinuumPointField configuration point) direction
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    diracDualScalarYukawaConstantDirectionVector_coordinate_continuous
      configuration smooth direction
  have pairingSumContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorEntryContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          vectorCoordinateContinuous
    have dualEntryContinuous : Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
      (smooth.2.2.2.2.2.2.2.2 index).continuous
    exact vectorEntryContinuous.mul dualEntryContinuous
  have dualPairingContinuous : Continuous fun point =>
      configuration.conjugateMatter point (vector point) := by
    rw [show (fun point =>
        configuration.conjugateMatter point (vector point)) =
      fun point => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext point
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        matterDual_coordinate_expansion (configuration.conjugateMatter point)
          (matterCoordinateEquiv (vector point))]
    exact pairingSumContinuous
  unfold diracDualScalarYukawaFirstVariationDensity
  exact (Complex.continuous_re.comp dualPairingContinuous).congr fun point => by
    simp only [Function.comp_apply, toContinuumPointField, vector]

theorem diracDualScalarAlgebraicDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier) :
    Continuous
      (diracDualScalarAlgebraicDirectionalCoefficient source configuration
        direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have kineticContinuous := scalarAlgebraicKineticDensity_continuous source
    configuration smooth nondegenerate direction
  have potentialContinuous := scalarPotentialConstantDirection_continuous source
    configuration smooth direction
  have yukawaContinuous :=
    diracDualScalarYukawaConstantDirectionDensity_continuous configuration
      smooth direction
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  exact volumeContinuous.mul
    ((kineticContinuous.sub potentialContinuous).add yukawaContinuous)

/-- New scalar Euler coefficient with the unchanged kinetic momentum
divergence and the repaired Yukawa algebraic leg. -/
def diracDualScalarEulerLagrangeDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : ScalarCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  diracDualScalarAlgebraicDirectionalCoefficient source configuration direction
      point -
    scalarDifferentialMomentumDivergence source configuration direction point

theorem diracDualScalarEulerLagrangeDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : ScalarCoordinateCarrier) :
    Continuous
      (diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
        direction) :=
  (diracDualScalarAlgebraicDirectionalCoefficient_continuous source
    configuration smooth nondegenerate direction).sub
      (scalarDifferentialMomentumDivergence_continuous source configuration
        smooth nondegenerate direction)

/-! ## Genuine integration by parts and pointwise equation -/

theorem diracDualFormNativeScalarWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      DiracDualFormNativeScalarWeakEquation source configuration)
    (direction : ScalarCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
          direction point) = 0 := by
  let momentum := fun derivativeDirection : LorentzianIndex =>
    scalarDifferentialMomentum source configuration direction
      derivativeDirection
  let momentumDerivative := fun derivativeDirection : LorentzianIndex =>
    fun point => fieldDirectionalDerivative (momentum derivativeDirection)
      point derivativeDirection
  let algebraic :=
    diracDualScalarAlgebraicDirectionalCoefficient source configuration
      direction
  have momentumContinuous : ∀ derivativeDirection,
      Continuous (momentum derivativeDirection) := fun derivativeDirection =>
    (scalarDifferentialMomentum_contDiff source configuration smooth
      nondegenerate direction derivativeDirection).continuous
  have momentumDerivativeContinuous : ∀ derivativeDirection,
      Continuous (momentumDerivative derivativeDirection) := by
    intro derivativeDirection
    have momentumSmooth := scalarDifferentialMomentum_contDiff source
      configuration smooth nondegenerate direction derivativeDirection
    unfold momentumDerivative momentum fieldDirectionalDerivative
    exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  have derivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point := fun derivativeDirection =>
    scalarCompactDerivative_mul_continuous_integrable variation
      (momentum derivativeDirection) (momentumContinuous derivativeDirection)
      derivativeDirection
  have derivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      derivativeTermIntegrable derivativeDirection
  have algebraicContinuous : Continuous algebraic :=
    diracDualScalarAlgebraicDirectionalCoefficient_continuous source
      configuration smooth nondegenerate direction
  have algebraicTermIntegrable : Integrable fun point =>
      variation point * algebraic point :=
    scalarCompact_mul_continuous_integrable variation algebraic
      algebraicContinuous
  have momentumDerivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        variation point * momentumDerivative derivativeDirection point :=
    fun derivativeDirection =>
      scalarCompact_mul_continuous_integrable variation
        (momentumDerivative derivativeDirection)
        (momentumDerivativeContinuous derivativeDirection)
  have momentumDerivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        variation point * momentumDerivative derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      momentumDerivativeTermIntegrable derivativeDirection
  have weakDirection := weakEquation
    (scalarTimesScalarVariation direction variation)
  rw [show (fun point : BasePoint =>
      holonomicDiracDualScalarFirstVariationDensity source configuration
        (scalarTimesScalarVariation direction variation) point) =
    fun point =>
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point) +
        variation point * algebraic point by
    funext point
    exact holonomicDiracDualScalarFirstVariationDensity_scalarTimes source
      configuration direction variation point] at weakDirection
  have integralDerivativeSum :
      (∫ point : BasePoint,
        ∑ derivativeDirection : LorentzianIndex,
          fieldDirectionalDerivative variation point derivativeDirection *
            momentum derivativeDirection point) =
        ∑ derivativeDirection : LorentzianIndex,
          ∫ point : BasePoint,
            fieldDirectionalDerivative variation point derivativeDirection *
              momentum derivativeDirection point := by
    simpa using integral_finsetSum Finset.univ
      (fun derivativeDirection _ => derivativeTermIntegrable derivativeDirection)
  rw [integral_add derivativeSumIntegrable algebraicTermIntegrable,
    integralDerivativeSum] at weakDirection
  have ibp : ∀ derivativeDirection,
      (∫ point : BasePoint,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point) =
        -(∫ point : BasePoint,
          variation point * momentumDerivative derivativeDirection point) := by
    intro derivativeDirection
    exact scalarDifferentialMomentum_integrationByParts source configuration
      smooth nondegenerate direction variation derivativeDirection
  simp_rw [ibp] at weakDirection
  have integralMomentumDerivativeSum :
      (∫ point : BasePoint,
        ∑ derivativeDirection : LorentzianIndex,
          variation point * momentumDerivative derivativeDirection point) =
        ∑ derivativeDirection : LorentzianIndex,
          ∫ point : BasePoint,
            variation point * momentumDerivative derivativeDirection point := by
    simpa using integral_finsetSum Finset.univ
      (fun derivativeDirection _ =>
        momentumDerivativeTermIntegrable derivativeDirection)
  have residualFunctionEquality :
      (fun point : BasePoint =>
        variation point *
          diracDualScalarEulerLagrangeDirectionalCoefficient source
            configuration direction point) =
      fun point =>
        variation point * algebraic point -
          ∑ derivativeDirection : LorentzianIndex,
            variation point * momentumDerivative derivativeDirection point := by
    funext point
    unfold diracDualScalarEulerLagrangeDirectionalCoefficient
      scalarDifferentialMomentumDivergence algebraic momentumDerivative
      momentum
    rw [mul_sub, Finset.mul_sum]
  rw [residualFunctionEquality,
    integral_sub algebraicTermIntegrable momentumDerivativeSumIntegrable,
    integralMomentumDerivativeSum]
  have rearrangedWeak :
      (∫ point : BasePoint, variation point * algebraic point) -
          ∑ derivativeDirection : LorentzianIndex,
            ∫ point : BasePoint,
              variation point * momentumDerivative derivativeDirection point =
        0 := by
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simpa only [add_comm] using weakDirection
  exact rearrangedWeak

def DiracDualFormNativeScalarPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : ScalarCoordinateCarrier,
    diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
      direction = 0

theorem diracDualFormNativeScalarWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      DiracDualFormNativeScalarWeakEquation source configuration) :
    DiracDualFormNativeScalarPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (diracDualScalarEulerLagrangeDirectionalCoefficient source configuration
      direction)
    (diracDualScalarEulerLagrangeDirectionalCoefficient_continuous source
      configuration smooth nondegenerate direction)
  intro variation
  exact diracDualFormNativeScalarWeakEquation_direction_integral source
    configuration smooth nondegenerate weakEquation direction variation

theorem diracDualFormNativeScalarActionStationary_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (stationary :
      DiracDualFormNativeScalarActionStationary source configuration) :
    DiracDualFormNativeScalarPointwiseEquation source configuration := by
  apply diracDualFormNativeScalarWeakEquation_implies_pointwiseEquation source
    configuration smooth nondegenerate
  exact (diracDualFormNativeScalarActionStationary_iff_weakEquation source
    configuration smooth nondegenerate densityIntegrable).1 stationary

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeScalarVariation
