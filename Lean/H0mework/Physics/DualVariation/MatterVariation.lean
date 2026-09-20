import H0mework.Physics.DualVariation.ConjugateMatterVariation
import H0mework.Physics.Matter.MatterPointwiseEquation

/-!
# Dirac-dual form-native primal-matter variation

This module rederives the primal-matter Euler--Lagrange chain for the repaired
Dirac-dual action hash.  The primitive matter path and the kinetic principal
momentum are formulation-independent and remain reusable.  The Yukawa
algebraic coefficient, local action derivative, weak equation, and pointwise
residual are generated again from the repaired right-chiral operator.

No historical action derivative or historical pointwise matter equation is
accepted at a theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeMatterVariation

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineConjugateMatterVariation
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
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePlebanskiMultiplierVariation
open StageNineScalarLocalSpinDensity
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

/-! ## Repaired primal coefficient and local affine law -/

theorem diracDualRightChiralYukawaAction_matter_real_smul
    (scalar : ExteriorBreakingScalarCarrier)
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    diracDualRightChiralYukawaAction scalar (parameter • matter) =
      parameter • diracDualRightChiralYukawaAction scalar matter := by
  change
    diracDualRightChiralYukawaAction scalar ((parameter : ℂ) • matter) =
      (parameter : ℂ) • diracDualRightChiralYukawaAction scalar matter
  exact map_smul (diracDualRightChiralYukawaAction scalar)
    (parameter : ℂ) matter

/-- Complete primal variation vector of the repaired epoch. -/
def diracDualMatterFieldVariationVector
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matterVariation : DiracExteriorMatterCarrier)
    (derivativeVariation : LorentzianIndex → DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  matterCovariantDerivativeVariationVector source 0 point field
      derivativeVariation +
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm field.scalar) matterVariation

/-- Densitized coefficient of the primitive matter path. -/
def diracDualMatterFirstVariationDensity
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matterVariation : DiracExteriorMatterCarrier)
    (derivativeVariation : LorentzianIndex → DiracExteriorMatterCarrier) : ℝ :=
  generatedVolumeDensity field *
    (field.conjugateMatter
      (diracDualMatterFieldVariationVector source point field matterVariation
        derivativeVariation)).re

theorem generatedContinuumDiracDualMatterVector_withMatterJets_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matterVariation : DiracExteriorMatterCarrier)
    (derivativeVariation : LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedContinuumDiracDualMatterVector source 0 point
        (withMatterJets field
          (field.matter + parameter • matterVariation)
          (field.matterCovariantDerivative +
            parameter • derivativeVariation)) =
      generatedContinuumDiracDualMatterVector source 0 point field +
        parameter • diracDualMatterFieldVariationVector source point field
          matterVariation derivativeVariation := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [withMatterJets, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    Pi.add_apply, Pi.smul_apply]
  simp only [map_add, diracMatrixMatterAction_real_smul]
  rw [Finset.sum_add_distrib,
    diracDualRightChiralYukawaAction_matter_real_smul]
  have sumRealSmul :
      (∑ direction : LorentzianIndex,
        parameter • diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := field.coframe, derivative := 0 } direction)
          (derivativeVariation direction)) =
        parameter • ∑ direction : LorentzianIndex,
          diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := field.coframe, derivative := 0 } direction)
            (derivativeVariation direction) := by
    change
      (∑ direction : LorentzianIndex,
        (parameter : ℂ) • diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := field.coframe, derivative := 0 } direction)
          (derivativeVariation direction)) =
        (parameter : ℂ) • ∑ direction : LorentzianIndex,
          diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := field.coframe, derivative := 0 } direction)
            (derivativeVariation direction)
    rw [Finset.smul_sum]
  rw [sumRealSmul]
  module

theorem
    generatedDensitizedContinuumDiracDualMatterDensity_withMatterJets_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matterVariation : DiracExteriorMatterCarrier)
    (derivativeVariation : LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedDensitizedContinuumDiracDualMatterDensity source 0 point
        (withMatterJets field
          (field.matter + parameter • matterVariation)
          (field.matterCovariantDerivative +
            parameter • derivativeVariation)) =
      generatedDensitizedContinuumDiracDualMatterDensity source 0 point field +
        parameter *
          diracDualMatterFirstVariationDensity source point field
            matterVariation derivativeVariation := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    generatedContinuumDiracDualMatterVector_withMatterJets_affine, map_add,
    StageNineMatterCovariantDerivativeAffine.matterDualFrameRelative_real_smul]
  simp only [withMatterJets, generatedVolumeDensity,
    StageNineP286GaugeConnectionVariationDensity.matterDualFrameRelative_zeroChart,
    Complex.add_re]
  unfold diracDualMatterFirstVariationDensity generatedVolumeDensity
  simp [Complex.mul_re]
  ring

/-- The repaired root is exactly affine along the primitive matter path. -/
theorem generatedDiracDualFormNativeUnifiedLocalDensity_withMatterJets_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (matterVariation : DiracExteriorMatterCarrier)
    (derivativeVariation : LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withMatterJets field
          (field.matter + parameter • matterVariation)
          (field.matterCovariantDerivative +
            parameter • derivativeVariation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point field +
        parameter * diracDualMatterFirstVariationDensity source point field
          matterVariation derivativeVariation := by
  let variedField := withMatterJets field
    (field.matter + parameter • matterVariation)
    (field.matterCovariantDerivative + parameter • derivativeVariation)
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
  have scalarUnchanged :
      generatedDensitizedContinuumScalarDensity source 0 point variedField =
        generatedDensitizedContinuumScalarDensity source 0 point field := rfl
  change
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point variedField = _
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    generatedDiracDualFormNativeMatterDensity
  rw [gravityBFUnchanged, constraintUnchanged, gaugeUnchanged,
    scalarUnchanged,
    generatedDensitizedContinuumDiracDualMatterDensity_withMatterJets_affine]
  ring

/-- Holonomic first density belonging to the repaired root. -/
def holonomicDiracDualMatterFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  diracDualMatterFirstVariationDensity source point
    (toContinuumPointField configuration point)
    (matterCoordinateEquiv.symm (variation point))
    (holonomicMatterVariationCovariantDerivative configuration variation point)

theorem holonomicDiracDualFormNativeLocalDensity_matter_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (varyMatterCoordinates configuration variation parameter) point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicDiracDualMatterFirstVariationDensity source configuration
            variation point := by
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
  rw [toContinuumPointField_varyMatterCoordinates configuration smooth]
  exact generatedDiracDualFormNativeUnifiedLocalDensity_withMatterJets_affine
    source point (toContinuumPointField configuration point)
    (matterCoordinateEquiv.symm (variation point))
    (holonomicMatterVariationCovariantDerivative configuration variation point)
    parameter

/-! ## Analytic control of the repaired first density -/

theorem holonomicDiracDualMatterVariationYukawaVector_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm (variation point))) := by
  exact diracDualYukawaCoordinate_apply_continuous configuration.scalar variation
    smooth.2.2.2.2.2.2.1.continuous variation.smooth.continuous

theorem holonomicDiracDualMatterFieldVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracDualMatterFieldVariationVector source point
          (toContinuumPointField configuration point)
          (matterCoordinateEquiv.symm (variation point))
          (holonomicMatterVariationCovariantDerivative configuration variation
            point)) := by
  have kineticContinuous :=
    holonomicMatterVariationKineticSum_coordinate_continuous source
      configuration smooth nondegenerate variation
  have kineticWithIContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationCovariantDerivative configuration variation
            point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun _ => rfl
  have kineticVariationContinuous : Continuous fun point =>
      matterCoordinateEquiv
        (matterCovariantDerivativeVariationVector source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationCovariantDerivative configuration variation
            point)) := by
    exact kineticWithIContinuous.congr fun point => by
      unfold matterCovariantDerivativeVariationVector
        matterCovariantDerivativeKineticSum matterGaugeKineticSum
      simp only [toContinuumPointField, matterDerivativeFrameRelative_zeroChart,
        map_smul]
  have yukawaContinuous :=
    holonomicDiracDualMatterVariationYukawaVector_coordinate_continuous
      configuration smooth variation
  have actual := kineticVariationContinuous.add yukawaContinuous
  unfold diracDualMatterFieldVariationVector
  exact actual.congr fun point => by
    simp only [Pi.add_apply, toContinuumPointField]
    rw [map_add]

theorem holonomicDiracDualMatterFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Continuous
      (holonomicDiracDualMatterFirstVariationDensity source configuration
        variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have vectorContinuous :=
    holonomicDiracDualMatterFieldVariationVector_coordinate_continuous source
      configuration smooth nondegenerate variation
  let vector := fun point =>
    diracDualMatterFieldVariationVector source point
      (toContinuumPointField configuration point)
      (matterCoordinateEquiv.symm (variation point))
      (holonomicMatterVariationCovariantDerivative configuration variation
        point)
  have pairingSumContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorCoordinateContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp vectorContinuous
    have dualCoordinateContinuous : Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
      (smooth.2.2.2.2.2.2.2.2 index).continuous
    exact vectorCoordinateContinuous.mul dualCoordinateContinuous
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
  have realPairingContinuous := Complex.continuous_re.comp dualPairingContinuous
  unfold holonomicDiracDualMatterFirstVariationDensity
    diracDualMatterFirstVariationDensity
  exact volumeContinuous.mul realPairingContinuous

@[simp] theorem diracDualMatterFieldVariationVector_zero
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualMatterFieldVariationVector source point field 0 0 = 0 := by
  unfold diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp

theorem holonomicDiracDualMatterFirstVariationDensity_eq_zero_of_jet_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (variationZero : variation point = 0)
    (derivativeZero : ∀ direction : LorentzianIndex,
      matterVariationCoordinateDerivative variation point direction = 0) :
    holonomicDiracDualMatterFirstVariationDensity source configuration
        variation point = 0 := by
  have covariantDerivativeZero :=
    holonomicMatterVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration variation point variationZero derivativeZero
  unfold holonomicDiracDualMatterFirstVariationDensity
    diracDualMatterFirstVariationDensity
  rw [show matterCoordinateEquiv.symm (variation point) = 0 by
    simp [variationZero], covariantDerivativeZero]
  simp

theorem holonomicDiracDualMatterFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    HasCompactSupport
      (holonomicDiracDualMatterFirstVariationDensity source configuration
        variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards [compactMatterVariation_eventually_jet_zero variation] with
    point jetZero
  exact holonomicDiracDualMatterFirstVariationDensity_eq_zero_of_jet_zero source
    configuration variation point jetZero.1 jetZero.2

theorem holonomicDiracDualMatterFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Integrable
      (holonomicDiracDualMatterFirstVariationDensity source configuration
        variation) :=
  (holonomicDiracDualMatterFirstVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (holonomicDiracDualMatterFirstVariationDensity_compact source
        configuration variation)

/-! ## Integrated derivative and weak equation -/

theorem holonomicDiracDualFormNativeIntegratedUnifiedAction_matter_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier)
    (parameter : ℝ) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        (varyMatterCoordinates configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicDiracDualMatterFirstVariationDensity source configuration
              variation point) := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    integratedDiracDualFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyMatterCoordinates configuration variation parameter) point)) =
      fun point =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicDiracDualMatterFirstVariationDensity source configuration
            variation point := by
    funext point
    exact holonomicDiracDualFormNativeLocalDensity_matter_affine source
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
    holonomicDiracDualMatterFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  rw [integral_add baseIntegrable
    (firstIntegrable.const_mul parameter), integral_const_mul]

theorem holonomicDiracDualFormNativeIntegratedUnifiedAction_matter_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyMatterCoordinates configuration variation parameter))
      (∫ point : BasePoint,
        holonomicDiracDualMatterFirstVariationDensity source configuration
          variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicDiracDualMatterFirstVariationDensity source configuration
      variation point
  have actionEquality :
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyMatterCoordinates configuration variation parameter)) =
      fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
            configuration + parameter * firstIntegral := by
    funext parameter
    exact
      holonomicDiracDualFormNativeIntegratedUnifiedAction_matter_affine source
        configuration smooth nondegenerate densityIntegrable variation
        parameter
  rw [actionEquality]
  simpa using
    ((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        configuration)

def DiracDualFormNativeMatterActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier,
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyMatterCoordinates configuration variation parameter))
      0 0

def DiracDualFormNativeMatterWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier,
    (∫ point : BasePoint,
      holonomicDiracDualMatterFirstVariationDensity source configuration
        variation point) = 0

theorem diracDualFormNativeMatterActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    DiracDualFormNativeMatterActionStationary source configuration ↔
      DiracDualFormNativeMatterWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_matter_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_matter_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    simpa only [weakEquation variation] using actual

/-! ## Repaired algebraic coefficient and unchanged kinetic momentum -/

theorem matterCovariantDerivativeVariationVector_real_smul
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector source 0 point field
        (parameter • variation) =
      parameter • matterCovariantDerivativeVariationVector source 0 point field
        variation := by
  unfold matterCovariantDerivativeVariationVector
  rw [matterCovariantDerivativeKineticSum_real_smul]
  module

theorem
    matterCovariantDerivativeVariationVector_coordinateDerivativeDirections
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (direction : MatterCoordinateCarrier)
    (coefficient : LorentzianIndex → ℝ) :
    matterCovariantDerivativeVariationVector source 0 point field
        (fun derivativeDirection =>
          coefficient derivativeDirection •
            matterCoordinateEquiv.symm direction) =
      ∑ derivativeDirection : LorentzianIndex,
        coefficient derivativeDirection •
          matterDifferentialVariationVector source point field direction
            derivativeDirection := by
  unfold matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum matterDifferentialVariationVector
  simp only [matterDerivativeFrameRelative_zeroChart,
    diracMatrixMatterAction_real_smul]
  rw [Finset.smul_sum]
  simp_rw [StageNineMatterPointwiseEquation.complex_smul_real_smul_comm]

/-- Repaired algebraic response to a constant matter-coordinate direction. -/
def diracDualMatterAlgebraicVariationVector
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  diracDualMatterFieldVariationVector source point
    (toContinuumPointField configuration point)
    (matterCoordinateEquiv.symm direction)
    (holonomicMatterVariationAlgebraicDirection configuration direction point)

theorem diracDualMatterFieldVariationVector_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    diracDualMatterFieldVariationVector source point
        (toContinuumPointField configuration point)
        (matterCoordinateEquiv.symm
          (scalarTimesMatterVariation direction variation point))
        (holonomicMatterVariationCovariantDerivative configuration
          (scalarTimesMatterVariation direction variation) point) =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection •
          matterDifferentialVariationVector source point
            (toContinuumPointField configuration point) direction
            derivativeDirection) +
        variation point •
          diracDualMatterAlgebraicVariationVector source configuration direction
            point := by
  simp only [scalarTimesMatterVariation_apply]
  rw [matterCoordinateEquiv_symm_real_smul]
  have covariantDerivativeEquality :
      holonomicMatterVariationCovariantDerivative configuration
          (scalarTimesMatterVariation direction variation) point =
        (fun formDirection =>
          fieldDirectionalDerivative variation point formDirection •
            matterCoordinateEquiv.symm direction) +
          variation point •
            holonomicMatterVariationAlgebraicDirection configuration direction
              point := by
    funext formDirection
    exact holonomicMatterVariationCovariantDerivative_scalarTimes configuration
      direction variation point formDirection
  unfold diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
  rw [covariantDerivativeEquality,
    matterCovariantDerivativeVariationVector_add,
    matterCovariantDerivativeVariationVector_coordinateDerivativeDirections,
    matterCovariantDerivativeVariationVector_real_smul,
    diracDualRightChiralYukawaAction_matter_real_smul]
  module

/-- New algebraic coefficient.  The differential momentum remains the one
generated solely by the unchanged kinetic principal. -/
def diracDualMatterAlgebraicDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (configuration.conjugateMatter point
      (diracDualMatterAlgebraicVariationVector source configuration direction
        point)).re

theorem holonomicDiracDualMatterFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicDiracDualMatterFirstVariationDensity source configuration
        (scalarTimesMatterVariation direction variation) point =
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          matterDifferentialMomentum source configuration direction
            derivativeDirection point) +
        variation point *
          diracDualMatterAlgebraicDirectionalCoefficient source configuration
            direction point := by
  unfold holonomicDiracDualMatterFirstVariationDensity
    diracDualMatterFirstVariationDensity matterDifferentialMomentum
    diracDualMatterAlgebraicDirectionalCoefficient
  rw [diracDualMatterFieldVariationVector_scalarTimes]
  rw [map_add, map_sum]
  simp only [Complex.add_re, Complex.re_sum]
  simp_rw [StageNineMatterPointwiseEquation.matterDual_real_smul]
  simp_rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [mul_add, Finset.mul_sum]
  simp only [toContinuumPointField]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro derivativeDirection _
    ring
  · ring

/-! ## Continuity of the repaired algebraic residual -/

theorem diracDualMatterAlgebraicVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracDualMatterAlgebraicVariationVector source configuration direction
          point) := by
  have kineticSumContinuous : Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationAlgebraicDirection configuration direction
            point)) := by
    have sumContinuous : Continuous fun point =>
        ∑ formDirection : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := configuration.coframe point, derivative := 0 }
                formDirection)
              (holonomicMatterVariationAlgebraicDirection configuration direction
                point formDirection)) := by
      apply continuous_finsetSum
      intro formDirection _
      exact diracMatrixMatterCoordinate_raw_apply_continuous _ _
        (holonomicInverseCoframeDiracGamma_continuous configuration smooth
          nondegenerate formDirection)
        (holonomicMatterVariationAlgebraicDirection_coordinate_continuous
          configuration smooth direction formDirection)
    exact sumContinuous.congr fun point => by
      unfold matterGaugeKineticSum matterDerivativeFrameRelative
      simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]
  have kineticWithIContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationAlgebraicDirection configuration direction
            point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticSumContinuous).congr fun _ => rfl
  have kineticVariationContinuous : Continuous fun point =>
      matterCoordinateEquiv
        (matterCovariantDerivativeVariationVector source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterVariationAlgebraicDirection configuration direction
            point)) := by
    exact kineticWithIContinuous.congr fun point => by
      unfold matterCovariantDerivativeVariationVector
        matterCovariantDerivativeKineticSum matterGaugeKineticSum
      simp only [toContinuumPointField, matterDerivativeFrameRelative_zeroChart,
        map_smul]
  have yukawaContinuous := diracDualYukawaCoordinate_apply_continuous
    configuration.scalar (fun _ : BasePoint => direction)
    smooth.2.2.2.2.2.2.1.continuous continuous_const
  have actual := kineticVariationContinuous.add yukawaContinuous
  unfold diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
  exact actual.congr fun point => by
    simp only [Pi.add_apply, toContinuumPointField]
    rw [map_add]
    rfl

theorem diracDualMatterAlgebraicDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (diracDualMatterAlgebraicDirectionalCoefficient source configuration
        direction) := by
  let vector :=
    diracDualMatterAlgebraicVariationVector source configuration direction
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    diracDualMatterAlgebraicVariationVector_coordinate_continuous source
      configuration smooth nondegenerate direction
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
  have realPairingContinuous := Complex.continuous_re.comp dualPairingContinuous
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold diracDualMatterAlgebraicDirectionalCoefficient
  exact (volumeContinuous.mul realPairingContinuous).congr fun point => by
    simp only [Pi.mul_apply, Function.comp_apply, toContinuumPointField, vector]

/-- Repaired adjoint Euler coefficient: new algebraic Yukawa response minus
the unchanged divergence of the kinetic momentum. -/
def diracDualMatterEulerLagrangeDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  diracDualMatterAlgebraicDirectionalCoefficient source configuration direction
      point -
    matterDifferentialMomentumDivergence source configuration direction point

theorem diracDualMatterEulerLagrangeDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
        direction) :=
  (diracDualMatterAlgebraicDirectionalCoefficient_continuous source
    configuration smooth nondegenerate direction).sub
      (matterDifferentialMomentumDivergence_continuous source configuration
        smooth nondegenerate direction)

/-! ## Genuine integration by parts and pointwise equation -/

theorem diracDualFormNativeMatterWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      DiracDualFormNativeMatterWeakEquation source configuration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
          direction point) = 0 := by
  let momentum := fun derivativeDirection : LorentzianIndex =>
    matterDifferentialMomentum source configuration direction
      derivativeDirection
  let momentumDerivative := fun derivativeDirection : LorentzianIndex =>
    fun point => fieldDirectionalDerivative (momentum derivativeDirection)
      point derivativeDirection
  let algebraic :=
    diracDualMatterAlgebraicDirectionalCoefficient source configuration
      direction
  have momentumContinuous : ∀ derivativeDirection,
      Continuous (momentum derivativeDirection) := fun derivativeDirection =>
    (matterDifferentialMomentum_contDiff source configuration smooth
      nondegenerate direction derivativeDirection).continuous
  have momentumDerivativeContinuous : ∀ derivativeDirection,
      Continuous (momentumDerivative derivativeDirection) := by
    intro derivativeDirection
    have momentumSmooth := matterDifferentialMomentum_contDiff source
      configuration smooth nondegenerate direction derivativeDirection
    unfold momentumDerivative momentum fieldDirectionalDerivative
    exact (momentumSmooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  have derivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point := fun derivativeDirection =>
    compactScalarDerivative_mul_continuous_integrable variation
      (momentum derivativeDirection) (momentumContinuous derivativeDirection)
      derivativeDirection
  have derivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      derivativeTermIntegrable derivativeDirection
  have algebraicContinuous : Continuous algebraic :=
    diracDualMatterAlgebraicDirectionalCoefficient_continuous source
      configuration smooth nondegenerate direction
  have algebraicTermIntegrable : Integrable fun point =>
      variation point * algebraic point :=
    compactScalar_mul_continuous_integrable variation algebraic
      algebraicContinuous
  have momentumDerivativeTermIntegrable : ∀ derivativeDirection,
      Integrable fun point =>
        variation point * momentumDerivative derivativeDirection point :=
    fun derivativeDirection =>
      compactScalar_mul_continuous_integrable variation
        (momentumDerivative derivativeDirection)
        (momentumDerivativeContinuous derivativeDirection)
  have momentumDerivativeSumIntegrable : Integrable fun point =>
      ∑ derivativeDirection : LorentzianIndex,
        variation point * momentumDerivative derivativeDirection point :=
    integrable_finsetSum Finset.univ fun derivativeDirection _ =>
      momentumDerivativeTermIntegrable derivativeDirection
  have weakDirection := weakEquation
    (scalarTimesMatterVariation direction variation)
  rw [show (fun point : BasePoint =>
      holonomicDiracDualMatterFirstVariationDensity source configuration
        (scalarTimesMatterVariation direction variation) point) =
    fun point =>
      (∑ derivativeDirection : LorentzianIndex,
        fieldDirectionalDerivative variation point derivativeDirection *
          momentum derivativeDirection point) +
        variation point * algebraic point by
    funext point
    exact holonomicDiracDualMatterFirstVariationDensity_scalarTimes source
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
    exact matterDifferentialMomentum_integrationByParts source configuration
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
          diracDualMatterEulerLagrangeDirectionalCoefficient source
            configuration direction point) =
      fun point =>
        variation point * algebraic point -
          ∑ derivativeDirection : LorentzianIndex,
            variation point * momentumDerivative derivativeDirection point := by
    funext point
    unfold diracDualMatterEulerLagrangeDirectionalCoefficient
      matterDifferentialMomentumDivergence algebraic momentumDerivative
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

/-- New pointwise adjoint matter equation belonging to the repaired root. -/
def DiracDualFormNativeMatterPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : MatterCoordinateCarrier,
    diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
      direction = 0

theorem diracDualFormNativeMatterWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      DiracDualFormNativeMatterWeakEquation source configuration) :
    DiracDualFormNativeMatterPointwiseEquation source configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (diracDualMatterEulerLagrangeDirectionalCoefficient source configuration
      direction)
    (diracDualMatterEulerLagrangeDirectionalCoefficient_continuous source
      configuration smooth nondegenerate direction)
  intro variation
  exact diracDualFormNativeMatterWeakEquation_direction_integral source
    configuration smooth nondegenerate weakEquation direction variation

theorem diracDualFormNativeMatterActionStationary_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (stationary :
      DiracDualFormNativeMatterActionStationary source configuration) :
    DiracDualFormNativeMatterPointwiseEquation source configuration := by
  apply diracDualFormNativeMatterWeakEquation_implies_pointwiseEquation source
    configuration smooth nondegenerate
  exact (diracDualFormNativeMatterActionStationary_iff_weakEquation source
    configuration smooth nondegenerate densityIntegrable).1 stationary

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeMatterVariation
