import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import H0mework.Physics.Matter.SU7ExteriorMatterVariationCore

/-!
# S9-C3d0: scalar variation and weak Euler--Lagrange equation

The primitive breaking scalar is varied through actual compactly supported
smooth coordinate fields.  Its covariant jet is regenerated from the
Fréchet derivative and the actual P286 mother action.  The common local
density has an exact quadratic expansion whose linear term contains the
covariant kinetic, source-generated vacuum potential, and exterior-Yukawa
contributions.  Continuity, compact support, integrability, and the integrated
action derivative are proved internally.

No scalar equation, current, derivative, integrability, potential-gradient,
mass, or stationarity certificate is accepted from the source mouth.
Pointwise extraction by integration by parts remains the next checkpoint.
-/

namespace SaturationMonoid.PhysicsCore.StageNineScalarVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNinePlebanskiMultiplierVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open SU7ExteriorMatterFullVariations
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorBreakingYukawa
open DiracExteriorMatterAction
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

set_option maxHeartbeats 600000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286GaugeConnectionActionVariation.p286CoordinateIndexFintype

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def varyScalarCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    scalar := fun point => configuration.scalar point + parameter • variation point }

@[simp] theorem varyScalarCoordinates_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier) :
    varyScalarCoordinates configuration variation 0 = configuration := by
  cases configuration
  simp [varyScalarCoordinates]

def scalarVariationCoordinateDerivative
    (variation : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  fieldDirectionalDerivative variation point direction

def holonomicScalarVariationCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  scalarVariationCoordinateDerivative variation point direction +
    scalarMotherLieAction
      (p286LieBlockEmbed (configuration.gaugeConnection point direction))
      (variation point)

theorem scalarCoordinateDerivative_varyScalarCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ) (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (varyScalarCoordinates configuration variation parameter).scalar
        point direction =
      fieldDirectionalDerivative configuration.scalar point direction +
        parameter • scalarVariationCoordinateDerivative variation point
          direction := by
  have backgroundDifferentiable : DifferentiableAt ℝ configuration.scalar point :=
    (smooth.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have variationDifferentiable : DifferentiableAt ℝ
      (variation : BasePoint → ScalarCoordinateCarrier) point :=
    (variation.smooth.differentiable (by simp)).differentiableAt
  unfold fieldDirectionalDerivative scalarVariationCoordinateDerivative
  simp only [varyScalarCoordinates]
  have derivativeEquality :
      fderiv ℝ
          (fun candidate => configuration.scalar candidate +
            parameter • variation candidate) point =
        fderiv ℝ configuration.scalar point +
          parameter • fderiv ℝ variation point := by
    exact (backgroundDifferentiable.hasFDerivAt.add
      (variationDifferentiable.hasFDerivAt.const_smul parameter)).fderiv
  rw [derivativeEquality]
  simp [fieldDirectionalDerivative]

theorem holonomicScalarCovariantDerivative_varyScalarCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ) (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (varyScalarCoordinates configuration variation parameter) point
        direction =
      holonomicScalarCovariantDerivative configuration point direction +
        parameter • holonomicScalarVariationCovariantDerivative configuration
          variation point direction := by
  unfold holonomicScalarCovariantDerivative
    holonomicScalarVariationCovariantDerivative
  rw [scalarCoordinateDerivative_varyScalarCoordinates configuration smooth]
  simp only [varyScalarCoordinates, scalarMotherLieAction_add_right,
    scalarMotherLieAction_real_smul_right]
  module

def withScalarJets
    (field : StageNineContinuumPointField)
    (scalar : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier) :
    StageNineContinuumPointField :=
  { field with
    scalar := scalar
    scalarCovariantDerivative := scalarDerivative }

theorem toContinuumPointField_varyScalarCoordinates
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ) (point : BasePoint) :
    toContinuumPointField
        (varyScalarCoordinates configuration variation parameter) point =
      withScalarJets (toContinuumPointField configuration point)
        (configuration.scalar point + parameter • variation point)
        (holonomicScalarCovariantDerivative configuration point +
          parameter • holonomicScalarVariationCovariantDerivative configuration
            variation point) := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  funext direction
  exact holonomicScalarCovariantDerivative_varyScalarCoordinates configuration
    smooth variation parameter point direction

def scalarPotentialFirstVariation
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier) : ℝ :=
  frameRelativeScalarGradient (sourceGeneratedVacuumCoordinates source)
    field.scalar variation

def scalarYukawaVariationVector
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier) : DiracExteriorMatterCarrier :=
  chiralExteriorYukawaAction
    (scalarCoordinateEquiv.symm variation) field.matter

def scalarYukawaFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier) : ℝ :=
  (field.conjugateMatter
    (scalarYukawaVariationVector field variation)).re

def scalarFirstVariationDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (derivativeVariation : LorentzianIndex → ScalarCoordinateCarrier) : ℝ :=
  generatedVolumeDensity field *
    (scalarGaugeConnectionKineticFirstVariationDensity source 0 point field
        derivativeVariation -
      scalarPotentialFirstVariation source field variation +
      scalarYukawaFirstVariationDensity field variation)

def scalarSecondVariationDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (derivativeVariation : LorentzianIndex → ScalarCoordinateCarrier) : ℝ :=
  generatedVolumeDensity field *
    (scalarGaugeConnectionKineticSecondVariationDensity source 0 point field
        derivativeVariation -
      scalarCoordinateSquaredNorm variation)

theorem generatedScalarKineticDensity_withScalarJets_quadratic
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarVariation : ScalarCoordinateCarrier)
    (derivativeVariation : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedScalarKineticDensity source 0 point
        (withScalarJets field
          (field.scalar + parameter • scalarVariation)
          (field.scalarCovariantDerivative +
            parameter • derivativeVariation)) =
      generatedScalarKineticDensity source 0 point field +
        parameter * scalarGaugeConnectionKineticFirstVariationDensity
          source 0 point field derivativeVariation +
        parameter ^ 2 * scalarGaugeConnectionKineticSecondVariationDensity
          source 0 point field derivativeVariation := by
  unfold generatedScalarKineticDensity
    scalarGaugeConnectionKineticFirstVariationDensity
    scalarGaugeConnectionKineticSecondVariationDensity
  simp only [withScalarJets, Pi.add_apply, Pi.smul_apply,
    scalarFrameRelativeCovariantDerivative_add,
    scalarFrameRelativeCovariantDerivative_real_smul,
    scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [weightedDoubleSum_quadratic]
  ring

theorem generatedScalarPotential_withScalarJets_quadratic
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedScalarPotential source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation)
          scalarDerivative).scalar =
      generatedScalarPotential source 0 point field.scalar +
        parameter * scalarPotentialFirstVariation source field variation +
        parameter ^ 2 * scalarCoordinateSquaredNorm variation := by
  unfold generatedScalarPotential scalarPotentialFirstVariation
  simp only [withScalarJets, scalarFrameRelativeCoordinates_zeroChart]
  change frameRelativeScalarPotential (sourceGeneratedVacuumCoordinates source)
      (field.scalar + (parameter : ℂ) • variation) = _
  exact frameRelativeScalarPotential_expansion
    (sourceGeneratedVacuumCoordinates source) field.scalar variation parameter

theorem generatedContinuumMatterVector_withScalarJets_affine
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedContinuumMatterVector source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation)
          scalarDerivative) =
      generatedContinuumMatterVector source 0 point field +
        parameter • scalarYukawaVariationVector field variation := by
  unfold generatedContinuumMatterVector scalarYukawaVariationVector
  simp only [withScalarJets, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart]
  rw [map_add]
  rw [show scalarCoordinateEquiv.symm (parameter • variation) =
      (parameter : ℂ) • scalarCoordinateEquiv.symm variation by
    change scalarCoordinateEquiv.symm ((parameter : ℂ) • variation) = _
    rw [map_smul]]
  rw [chiralExteriorYukawaAction_add,
    chiralExteriorYukawaAction_smul, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

theorem generatedContinuumMatterDensity_withScalarJets_affine
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (scalarDerivative : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedContinuumMatterDensity source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation)
          scalarDerivative) =
      generatedContinuumMatterDensity source 0 point field +
        parameter * scalarYukawaFirstVariationDensity field variation := by
  unfold generatedContinuumMatterDensity scalarYukawaFirstVariationDensity
  change
    (matterDualFrameRelative source 0 point field.conjugateMatter
      (generatedContinuumMatterVector source 0 point
        (withScalarJets field
          (field.scalar + parameter • variation)
          scalarDerivative))).re = _
  rw [generatedContinuumMatterVector_withScalarJets_affine, map_add,
    matterDualFrameRelative_real_smul]
  simp only [matterDualFrameRelative_zeroChart, Complex.add_re]
  simp [Complex.mul_re]

theorem generatedUnifiedLocalDensity_withScalarJets_quadratic
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : ScalarCoordinateCarrier)
    (derivativeVariation : LorentzianIndex → ScalarCoordinateCarrier)
    (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withScalarJets field
          (field.scalar + parameter • variation)
          (field.scalarCovariantDerivative +
            parameter • derivativeVariation)) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point field +
        parameter * scalarFirstVariationDensity source point field variation
          derivativeVariation +
        parameter ^ 2 * scalarSecondVariationDensity source point field variation
          derivativeVariation := by
  rw [generatedUnifiedLocalDensityAtBoundary,
    generatedUnifiedLocalDensityAtBoundary]
  unfold generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
  rw [generatedScalarKineticDensity_withScalarJets_quadratic,
    generatedScalarPotential_withScalarJets_quadratic,
    generatedContinuumMatterDensity_withScalarJets_affine]
  unfold scalarFirstVariationDensity scalarSecondVariationDensity
  simp only [withScalarJets, generatedVolumeDensity,
    generatedGravitySimplicityDensity, generatedGravitySimplicityResidual,
    generatedGravityBFDensity]
  ring

def holonomicScalarFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  scalarFirstVariationDensity source point
    (toContinuumPointField configuration point) (variation point)
    (holonomicScalarVariationCovariantDerivative configuration variation point)

def holonomicScalarSecondVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  scalarSecondVariationDensity source point
    (toContinuumPointField configuration point) (variation point)
    (holonomicScalarVariationCovariantDerivative configuration variation point)

theorem holonomicLocalDensity_scalar_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ) (point : BasePoint) :
    generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyScalarCoordinates configuration variation parameter) point) =
      generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter * holonomicScalarFirstVariationDensity source configuration
          variation point +
        parameter ^ 2 * holonomicScalarSecondVariationDensity source
          configuration variation point := by
  rw [toContinuumPointField_varyScalarCoordinates configuration smooth]
  exact generatedUnifiedLocalDensity_withScalarJets_quadratic source point
    (toContinuumPointField configuration point) (variation point)
    (holonomicScalarVariationCovariantDerivative configuration variation point)
    parameter

/-! ## Analytic control of scalar first and second densities -/

theorem scalarVariationCoordinateDerivative_continuous
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      scalarVariationCoordinateDerivative variation point direction := by
  simpa [scalarVariationCoordinateDerivative, fieldDirectionalDerivative] using
    compactVariation_directionalDerivative_continuous variation direction

theorem holonomicScalarVariationCovariantDerivative_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (direction : LorentzianIndex) :
    Continuous fun point =>
      holonomicScalarVariationCovariantDerivative configuration variation point
        direction := by
  have derivativeContinuous :=
    scalarVariationCoordinateDerivative_continuous variation direction
  have gaugeCoordinateContinuous : Continuous fun point =>
      p286CoordinateEquiv (configuration.gaugeConnection point direction) :=
    (smooth.2.2.2.2.1 direction).continuous
  have variationContinuous : Continuous
      (variation : BasePoint → ScalarCoordinateCarrier) :=
    variation.smooth.continuous
  have gaugeContinuous := scalarP286Action_apply_continuous
    (fun point => p286CoordinateEquiv
      (configuration.gaugeConnection point direction)) variation
    gaugeCoordinateContinuous variationContinuous
  unfold holonomicScalarVariationCovariantDerivative
  exact derivativeContinuous.add (gaugeContinuous.congr fun point => by
    change
      scalarMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (configuration.gaugeConnection point direction))))
          (variation point) = _
    rw [p286CoordinateEquiv.symm_apply_apply])

theorem holonomicScalarKineticFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarVariationCovariantDerivative configuration variation
          point) := by
  have metricInverseContinuous :=
    holonomicLorentzianMetric_inv_continuous configuration smooth nondegenerate
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro first _
  apply continuous_finsetSum
  intro second _
  have metricEntryContinuous : Continuous fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ first second :=
    (continuous_apply second).comp
      ((continuous_apply first).comp metricInverseContinuous)
  apply metricEntryContinuous.mul
  apply Continuous.add
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarVariationCovariantDerivative_continuous configuration
        smooth variation first)
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        second)
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarCovariantDerivative_continuous configuration smooth first)
      (holonomicScalarVariationCovariantDerivative_continuous configuration
        smooth variation second)

theorem holonomicScalarKineticSecondVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarGaugeConnectionKineticSecondVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (holonomicScalarVariationCovariantDerivative configuration variation
          point) := by
  have metricInverseContinuous :=
    holonomicLorentzianMetric_inv_continuous configuration smooth nondegenerate
  unfold scalarGaugeConnectionKineticSecondVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro first _
  apply continuous_finsetSum
  intro second _
  have metricEntryContinuous : Continuous fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ first second :=
    (continuous_apply second).comp
      ((continuous_apply first).comp metricInverseContinuous)
  exact metricEntryContinuous.mul
    (scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarVariationCovariantDerivative_continuous configuration
        smooth variation first)
      (holonomicScalarVariationCovariantDerivative_continuous configuration
        smooth variation second))

theorem holonomicScalarPotentialFirstVariation_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarPotentialFirstVariation source
        (toContinuumPointField configuration point) (variation point) := by
  have scalarContinuous : Continuous configuration.scalar :=
    smooth.2.2.2.2.2.2.1.continuous
  have variationContinuous : Continuous
      (variation : BasePoint → ScalarCoordinateCarrier) :=
    variation.smooth.continuous
  have pairingContinuous := scalarCoordinatePairingRe_apply_continuous _ _
    (scalarContinuous.sub
      (continuous_const : Continuous
        (fun _ : BasePoint => sourceGeneratedVacuumCoordinates source)))
    variationContinuous
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
    scalarCoordinateRealPairing
  simp only [toContinuumPointField]
  exact ((continuous_const : Continuous (fun _ : BasePoint => (2 : ℝ))).mul
    pairingContinuous).congr fun point => by
    simp only [Pi.mul_apply, Pi.sub_apply, scalarCoordinatePairingRe]

def scalarVariationYukawaCoordinateBilinear :
    ScalarCoordinateCarrier →ₗ[ℂ]
      MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier where
  toFun scalar :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        simp only [map_add]
      map_smul' := by
        intro parameter matter
        simp only [map_smul, RingHom.id_apply] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (first + second))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm first)
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm second)
              (matterCoordinateEquiv.symm matter))
    rw [map_add, chiralExteriorYukawaAction_add, LinearMap.add_apply, map_add]
  map_smul' := by
    intro parameter scalar
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (parameter • scalar))
            (matterCoordinateEquiv.symm matter)) =
        parameter • matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
    rw [map_smul, chiralExteriorYukawaAction_smul,
      LinearMap.smul_apply, map_smul]

theorem scalarVariationYukawaCoordinate_apply_continuous
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (matter : BasePoint → MatterCoordinateCarrier)
    (scalarContinuous : Continuous scalar)
    (matterContinuous : Continuous matter) :
    Continuous fun point =>
      scalarVariationYukawaCoordinateBilinear (scalar point) (matter point) := by
  exact
    (scalarVariationYukawaCoordinateBilinear.toContinuousBilinearMap.continuous.comp
      scalarContinuous).clm_apply matterContinuous

theorem holonomicScalarYukawaVariationVector_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (scalarYukawaVariationVector
          (toContinuumPointField configuration point) (variation point)) := by
  have actual := scalarVariationYukawaCoordinate_apply_continuous variation
    (fun point => matterCoordinateEquiv (configuration.matter point))
    variation.smooth.continuous
    smooth.2.2.2.2.2.2.2.1.continuous
  unfold scalarYukawaVariationVector
  exact actual.congr fun point => by
    simp only [toContinuumPointField]
    change
      matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (variation point))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicScalarYukawaFirstVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point =>
      scalarYukawaFirstVariationDensity
        (toContinuumPointField configuration point) (variation point) := by
  let vector := fun point =>
    scalarYukawaVariationVector (toContinuumPointField configuration point)
      (variation point)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    holonomicScalarYukawaVariationVector_coordinate_continuous configuration
      smooth variation
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
  unfold scalarYukawaFirstVariationDensity
  exact (Complex.continuous_re.comp dualPairingContinuous).congr fun point => by
    simp only [Function.comp_apply, toContinuumPointField, vector]

theorem scalarCoordinateSquaredNorm_continuous
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous fun point => scalarCoordinateSquaredNorm (variation point) := by
  unfold scalarCoordinateSquaredNorm
  apply continuous_finsetSum
  intro index _
  have coordinateContinuous : Continuous fun point => variation point index :=
    (PiLp.continuous_apply 2
      (fun _ : ScalarBasisIndex => ℂ) index).comp variation.smooth.continuous
  exact Complex.continuous_normSq.comp coordinateContinuous

theorem holonomicScalarFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous
      (holonomicScalarFirstVariationDensity source configuration variation) := by
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
    holonomicScalarYukawaFirstVariationDensity_continuous configuration smooth
      variation
  unfold holonomicScalarFirstVariationDensity scalarFirstVariationDensity
  exact volumeContinuous.mul
    ((kineticContinuous.sub potentialContinuous).add yukawaContinuous)

theorem holonomicScalarSecondVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Continuous
      (holonomicScalarSecondVariationDensity source configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have kineticContinuous :=
    holonomicScalarKineticSecondVariationDensity_continuous source configuration
      smooth nondegenerate variation
  have normContinuous := scalarCoordinateSquaredNorm_continuous variation
  unfold holonomicScalarSecondVariationDensity scalarSecondVariationDensity
  exact volumeContinuous.mul (kineticContinuous.sub normContinuous)

/-! ## Compact support and integrability -/

theorem compactScalarVariation_eventually_jet_zero
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    ∀ᶠ point in Filter.coclosedCompact BasePoint,
      variation point = 0 ∧
        ∀ direction : LorentzianIndex,
          scalarVariationCoordinateDerivative variation point direction = 0 := by
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  have derivativeEventually : ∀ direction : LorentzianIndex,
      ∀ᶠ point in Filter.coclosedCompact BasePoint,
        fderiv ℝ (variation : BasePoint → ScalarCoordinateCarrier) point
          (coordinateDirection direction) = 0 := by
    intro direction
    have actual := compactVariation_directionalDerivative_compact variation
      direction
    rw [hasCompactSupport_iff_eventuallyEq] at actual
    exact actual
  have everyDerivativeEventually :=
    Filter.eventually_all.2 derivativeEventually
  filter_upwards [variationEventually, everyDerivativeEventually] with
    point variationZero derivativeZero
  refine ⟨variationZero, ?_⟩
  intro direction
  simpa [scalarVariationCoordinateDerivative, fieldDirectionalDerivative] using
    derivativeZero direction

@[simp] theorem scalarMotherLieAction_zero_scalar
    (matrix : SU7MotherLieMatrix) :
    scalarMotherLieAction matrix 0 = 0 := by
  have actual := scalarMotherLieAction_real_smul_right matrix 0
    (0 : ScalarCoordinateCarrier)
  simpa using actual

theorem holonomicScalarVariationCovariantDerivative_eq_zero_of_jet_zero
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ direction : LorentzianIndex,
      scalarVariationCoordinateDerivative variation point direction = 0) :
    holonomicScalarVariationCovariantDerivative configuration variation point =
      0 := by
  funext direction
  unfold holonomicScalarVariationCovariantDerivative
  rw [derivativeZero direction, variationZero]
  simp

@[simp] theorem scalarPotentialFirstVariation_zero
    (source : SmoothUnifiedSource) (field : StageNineContinuumPointField) :
    scalarPotentialFirstVariation source field 0 = 0 := by
  simp [scalarPotentialFirstVariation, frameRelativeScalarGradient,
    scalarCoordinateRealPairing]

@[simp] theorem scalarYukawaVariationVector_zero
    (field : StageNineContinuumPointField) :
    scalarYukawaVariationVector field 0 = 0 := by
  have actionZero :
      chiralExteriorYukawaAction (0 : ExteriorBreakingScalarCarrier) = 0 := by
    have actual := chiralExteriorYukawaAction_smul (0 : ℂ)
      (0 : ExteriorBreakingScalarCarrier)
    simpa using actual
  unfold scalarYukawaVariationVector
  rw [map_zero, actionZero]
  simp

@[simp] theorem scalarYukawaFirstVariationDensity_zero
    (field : StageNineContinuumPointField) :
    scalarYukawaFirstVariationDensity field 0 = 0 := by
  simp [scalarYukawaFirstVariationDensity]

theorem holonomicScalarFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ direction : LorentzianIndex,
      scalarVariationCoordinateDerivative variation point direction = 0) :
    holonomicScalarFirstVariationDensity source configuration variation point =
      0 := by
  have covariantDerivativeZero :=
    holonomicScalarVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero
  unfold holonomicScalarFirstVariationDensity scalarFirstVariationDensity
  rw [variationZero, covariantDerivativeZero]
  simp

theorem holonomicScalarSecondVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → ScalarCoordinateCarrier) (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ direction : LorentzianIndex,
      scalarVariationCoordinateDerivative variation point direction = 0) :
    holonomicScalarSecondVariationDensity source configuration variation point =
      0 := by
  have covariantDerivativeZero :=
    holonomicScalarVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero
  unfold holonomicScalarSecondVariationDensity scalarSecondVariationDensity
  rw [variationZero, covariantDerivativeZero]
  simp [scalarCoordinateSquaredNorm]

theorem holonomicScalarFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    HasCompactSupport
      (holonomicScalarFirstVariationDensity source configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards [compactScalarVariation_eventually_jet_zero variation] with
    point jetZero
  exact holonomicScalarFirstVariationDensity_eq_zero_of_jet_zero source
    configuration variation point jetZero.1 jetZero.2

theorem holonomicScalarSecondVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    HasCompactSupport
      (holonomicScalarSecondVariationDensity source configuration variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards [compactScalarVariation_eventually_jet_zero variation] with
    point jetZero
  exact holonomicScalarSecondVariationDensity_eq_zero_of_jet_zero source
    configuration variation point jetZero.1 jetZero.2

theorem holonomicScalarFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Integrable
      (holonomicScalarFirstVariationDensity source configuration variation) :=
  (holonomicScalarFirstVariationDensity_continuous source configuration smooth
    nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicScalarFirstVariationDensity_compact source configuration
        variation)

theorem holonomicScalarSecondVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    Integrable
      (holonomicScalarSecondVariationDensity source configuration variation) :=
  (holonomicScalarSecondVariationDensity_continuous source configuration smooth
    nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicScalarSecondVariationDensity_compact source configuration
        variation)

/-! ## Integrated quadratic law and weak scalar equation -/

theorem holonomicIntegratedUnifiedAction_scalar_quadratic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source 0
        (varyScalarCoordinates configuration variation parameter) =
      holonomicIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicScalarFirstVariationDensity source configuration variation
              point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicScalarSecondVariationDensity source configuration variation
              point) := by
  unfold holonomicIntegratedUnifiedAction
    sourceGeneratedIntegratedUnifiedAction integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyScalarCoordinates configuration variation parameter) point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter * holonomicScalarFirstVariationDensity source configuration
          variation point +
        parameter ^ 2 * holonomicScalarSecondVariationDensity source
          configuration variation point := by
    funext point
    exact holonomicLocalDensity_scalar_quadratic source configuration smooth
      variation parameter point
  rw [pointwise]
  have firstIntegrable := holonomicScalarFirstVariationDensity_integrable
    source configuration smooth nondegenerate variation
  have secondIntegrable := holonomicScalarSecondVariationDensity_integrable
    source configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter * holonomicScalarFirstVariationDensity source
              configuration variation point +
          parameter ^ 2 * holonomicScalarSecondVariationDensity source
            configuration variation point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter * holonomicScalarFirstVariationDensity source
              configuration variation point) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicScalarSecondVariationDensity source
            configuration variation point) := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter * holonomicScalarFirstVariationDensity source configuration
            variation point)) +
        (∫ point : BasePoint,
          parameter ^ 2 * holonomicScalarSecondVariationDensity source
            configuration variation point) := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicIntegratedUnifiedAction_scalar_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyScalarCoordinates configuration variation parameter))
      (∫ point : BasePoint,
        holonomicScalarFirstVariationDensity source configuration variation
          point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicScalarFirstVariationDensity source configuration variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicScalarSecondVariationDensity source configuration variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyScalarCoordinates configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_scalar_quadratic source configuration
      smooth nondegenerate densityIntegrable variation parameter
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

/-- Stationarity under every compactly supported scalar-coordinate variation.
This is a predicate on a candidate configuration, never source data. -/
def CanonicalScalarActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyScalarCoordinates configuration variation parameter))
      0 0

def CanonicalScalarWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation ScalarCoordinateCarrier,
    (∫ point : BasePoint,
      holonomicScalarFirstVariationDensity source configuration variation
        point) = 0

theorem canonicalScalarActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (stationary : CanonicalScalarActionStationary source configuration) :
    CanonicalScalarWeakEquation source configuration := by
  intro variation
  have actual := holonomicIntegratedUnifiedAction_scalar_hasDerivAt source
    configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

end

end SaturationMonoid.PhysicsCore.StageNineScalarVariation
