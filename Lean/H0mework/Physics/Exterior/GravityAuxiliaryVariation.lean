import H0mework.Physics.Exterior.PlebanskiMultiplierVariation
import H0mework.Physics.Coframe.CoframeTwoFormPairing

namespace SaturationMonoid.PhysicsCore.StageNineGravityAuxiliaryVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open StageNinePlebanskiMultiplierVariation
open StageNineCoframeTwoFormPairing
open EmpiricalReferenceScaleCouplingBoundary
open MeasureTheory
open scoped ContDiff

noncomputable section

theorem coframeTwoFormMetricPairing_add_left
    (coframe : LorentzianCoframe)
    (first second residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe (first + second) residual =
      coframeTwoFormMetricPairing coframe first residual +
        coframeTwoFormMetricPairing coframe second residual := by
  unfold coframeTwoFormMetricPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pair _
  rw [map_add]
  simp only [Pi.add_apply]
  ring

theorem coframeTwoFormMetricPairing_smul_left
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (first residual : GaugeTwoForm) :
    coframeTwoFormMetricPairing coframe (parameter • first) residual =
      parameter * coframeTwoFormMetricPairing coframe first residual := by
  unfold coframeTwoFormMetricPairing
  simp only [map_smul, Pi.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem gravityCoframePairing_add_left
    (coframe : LorentzianCoframe)
    (first second residual : PhysicalBivector) :
    gravityCoframePairing coframe (first + second) residual =
      gravityCoframePairing coframe first residual +
        gravityCoframePairing coframe second residual := by
  unfold gravityCoframePairing
  simp only [Pi.add_apply, coframeTwoFormMetricPairing_add_left,
    mul_add, Finset.sum_add_distrib]

theorem gravityCoframePairing_smul_left
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (first residual : PhysicalBivector) :
    gravityCoframePairing coframe (parameter • first) residual =
      parameter * gravityCoframePairing coframe first residual := by
  unfold gravityCoframePairing
  simp only [Pi.smul_apply, coframeTwoFormMetricPairing_smul_left,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem gravityCoframePairing_add_right
    (coframe : LorentzianCoframe)
    (first second residual : PhysicalBivector) :
    gravityCoframePairing coframe residual (first + second) =
      gravityCoframePairing coframe residual first +
        gravityCoframePairing coframe residual second := by
  rw [gravityCoframePairing_symmetric coframe residual,
    gravityCoframePairing_add_left,
    gravityCoframePairing_symmetric coframe first,
    gravityCoframePairing_symmetric coframe second]

theorem gravityCoframePairing_smul_right
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (first residual : PhysicalBivector) :
    gravityCoframePairing coframe residual (parameter • first) =
      parameter * gravityCoframePairing coframe residual first := by
  rw [gravityCoframePairing_symmetric coframe residual,
    gravityCoframePairing_smul_left,
    gravityCoframePairing_symmetric coframe first]

theorem gravitySpacetimeHodge_add
    (coframe : LorentzianCoframe) (first second : PhysicalBivector) :
    gravitySpacetimeHodge coframe (first + second) =
      gravitySpacetimeHodge coframe first +
        gravitySpacetimeHodge coframe second := by
  funext internalPair spacetimePair
  simp [gravitySpacetimeHodge]

theorem gravitySpacetimeHodge_smul
    (coframe : LorentzianCoframe) (parameter : ℝ)
    (bivector : PhysicalBivector) :
    gravitySpacetimeHodge coframe (parameter • bivector) =
      parameter • gravitySpacetimeHodge coframe bivector := by
  funext internalPair spacetimePair
  simp [gravitySpacetimeHodge]

def withGravityAuxiliary
    (field : StageNineContinuumPointField)
    (auxiliary : PhysicalBivector) : StageNineContinuumPointField :=
  { field with gravityAuxiliary := auxiliary }

def gravityAuxiliaryBFFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  gravityCoframePairing field.coframe variation
      (gravitySpacetimeHodge field.coframe field.gravityCurvature) -
    (1 / 2 : ℝ) *
      (gravityCoframePairing field.coframe variation
          (gravitySpacetimeHodge field.coframe
            (gravityInternalDualEquiv field.gravityAuxiliary)) +
        gravityCoframePairing field.coframe field.gravityAuxiliary
          (gravitySpacetimeHodge field.coframe
            (gravityInternalDualEquiv variation)))

def gravityAuxiliaryBFSecondVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  -(1 / 2 : ℝ) *
    gravityCoframePairing field.coframe variation
      (gravitySpacetimeHodge field.coframe
        (gravityInternalDualEquiv variation))

theorem generatedGravityBFDensity_auxiliary_quadratic
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedGravityBFDensity
        (withGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedGravityBFDensity field +
        parameter * gravityAuxiliaryBFFirstVariationDensity field variation +
        parameter ^ 2 * gravityAuxiliaryBFSecondVariationDensity field variation := by
  unfold generatedGravityBFDensity withGravityAuxiliary
  simp only [gravityCoframePairing_add_left,
    gravityCoframePairing_smul_left,
    gravityCoframePairing_add_right,
    gravityCoframePairing_smul_right,
    gravitySpacetimeHodge_add, gravitySpacetimeHodge_smul,
    map_add, map_smul]
  unfold gravityAuxiliaryBFFirstVariationDensity
    gravityAuxiliaryBFSecondVariationDensity
  ring

def gravityAuxiliarySimplicityFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    ∑ spacetimePair : Fin 6,
      2 * field.gravitySimplicityMultiplier internalPair spacetimePair *
        generatedGravitySimplicityResidual field
          internalPair spacetimePair *
        variation internalPair spacetimePair

def gravityAuxiliarySimplicitySecondVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    ∑ spacetimePair : Fin 6,
      field.gravitySimplicityMultiplier internalPair spacetimePair *
        variation internalPair spacetimePair ^ 2

theorem generatedGravitySimplicityDensity_auxiliary_quadratic
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedGravitySimplicityDensity
        (withGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedGravitySimplicityDensity field +
        parameter *
          gravityAuxiliarySimplicityFirstVariationDensity field variation +
        parameter ^ 2 *
          gravityAuxiliarySimplicitySecondVariationDensity field variation := by
  have residualEquality :
      generatedGravitySimplicityResidual
          (withGravityAuxiliary field
            (field.gravityAuxiliary + parameter • variation)) =
        generatedGravitySimplicityResidual field + parameter • variation := by
    funext internalPair spacetimePair
    simp [generatedGravitySimplicityResidual, withGravityAuxiliary]
    ring
  rw [generatedGravitySimplicityDensity,
    generatedGravitySimplicityDensity, residualEquality]
  unfold gravitySimplicityMultiplierPairing
    gravityAuxiliarySimplicityFirstVariationDensity
    gravityAuxiliarySimplicitySecondVariationDensity
  simp only [withGravityAuxiliary, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ (multiplier residual varied : ℝ),
      multiplier * (residual + parameter * varied) ^ 2 =
        multiplier * residual ^ 2 +
          parameter * (2 * multiplier * residual * varied) +
          parameter ^ 2 * (multiplier * varied ^ 2) by
    intro multiplier residual varied
    ring]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

def gravityAuxiliaryFirstVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  generatedVolumeDensity field *
    (gravityAuxiliaryBFFirstVariationDensity field variation +
      gravityAuxiliarySimplicityFirstVariationDensity field variation)

def gravityAuxiliarySecondVariationDensity
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) : ℝ :=
  generatedVolumeDensity field *
    (gravityAuxiliaryBFSecondVariationDensity field variation +
      gravityAuxiliarySimplicitySecondVariationDensity field variation)

@[simp] theorem generatedVolumeDensity_withGravityAuxiliary
    (field : StageNineContinuumPointField) (auxiliary : PhysicalBivector) :
    generatedVolumeDensity (withGravityAuxiliary field auxiliary) =
      generatedVolumeDensity field := by
  rfl

@[simp] theorem generatedUnifiedLocalDensityNonGravityCore_withGravityAuxiliary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) (auxiliary : PhysicalBivector) :
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
        source boundary chart point (withGravityAuxiliary field auxiliary) =
      generatedUnifiedLocalDensityNonGravityCoreAtBoundary
        source boundary chart point field := by
  rfl

theorem generatedUnifiedLocalDensity_gravityAuxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source boundary chart point
        (withGravityAuxiliary field
          (field.gravityAuxiliary + parameter • variation)) =
      generatedUnifiedLocalDensityAtBoundary source boundary chart point field +
        parameter * gravityAuxiliaryFirstVariationDensity field variation +
        parameter ^ 2 * gravityAuxiliarySecondVariationDensity field variation := by
  unfold generatedUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
  rw [generatedGravityBFDensity_auxiliary_quadratic,
    generatedGravitySimplicityDensity_auxiliary_quadratic]
  rw [generatedVolumeDensity_withGravityAuxiliary,
    generatedUnifiedLocalDensityNonGravityCore_withGravityAuxiliary]
  unfold gravityAuxiliaryFirstVariationDensity
    gravityAuxiliarySecondVariationDensity
  ring

def varyGravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityAuxiliary := fun point =>
      configuration.gravityAuxiliary point + parameter • variation point }

theorem toContinuumPointField_varyGravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyGravityAuxiliary configuration variation parameter) point =
      withGravityAuxiliary (toContinuumPointField configuration point)
        (configuration.gravityAuxiliary point + parameter • variation point) := by
  rfl

def holonomicGravityAuxiliaryFirstVariationDensity
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (point : BasePoint) : ℝ :=
  gravityAuxiliaryFirstVariationDensity
    (toContinuumPointField configuration point) (variation point)

def holonomicGravityAuxiliarySecondVariationDensity
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (point : BasePoint) : ℝ :=
  gravityAuxiliarySecondVariationDensity
    (toContinuumPointField configuration point) (variation point)

theorem holonomicLocalDensity_gravityAuxiliary_quadratic
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source boundary chart point
        (toContinuumPointField
          (varyGravityAuxiliary configuration variation parameter) point) =
      generatedUnifiedLocalDensityAtBoundary source boundary chart point
          (toContinuumPointField configuration point) +
        parameter * holonomicGravityAuxiliaryFirstVariationDensity
          configuration variation point +
        parameter ^ 2 * holonomicGravityAuxiliarySecondVariationDensity
          configuration variation point := by
  rw [toContinuumPointField_varyGravityAuxiliary]
  exact generatedUnifiedLocalDensity_gravityAuxiliary_quadratic
    source boundary chart point (toContinuumPointField configuration point)
      (variation point) parameter

theorem holonomicGravitySimplicityMultiplier_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.gravitySimplicityMultiplier := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  exact (smooth.2.2.2.1 internalPair spacetimePair).continuous

theorem gravityConnectionDerivative_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    Continuous fun point =>
      gravityConnectionDerivative configuration point derivativeDirection
        formDirection internalOut internalIn := by
  unfold gravityConnectionDerivative
  have derivativeContinuous : Continuous
      (fderiv ℝ (fun candidate =>
        configuration.gravityConnection candidate formDirection
          internalOut internalIn)) :=
    (smooth.2.1 formDirection internalOut internalIn).continuous_fderiv (by simp)
  exact isBoundedBilinearMap_apply.continuous.comp
    (derivativeContinuous.prodMk continuous_const)

theorem holonomicGravityCurvature_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point => holonomicGravityCurvature configuration point := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  have derivativeContinuous : ∀
      (derivativeDirection formDirection internalOut internalIn :
        LorentzianIndex),
      Continuous fun point =>
        gravityConnectionDerivative configuration point derivativeDirection
          formDirection internalOut internalIn :=
    gravityConnectionDerivative_continuous configuration smooth
  have connectionContinuous : ∀
      (direction internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        configuration.gravityConnection point direction
          internalOut internalIn := fun direction internalOut internalIn =>
    (smooth.2.1 direction internalOut internalIn).continuous
  unfold holonomicGravityCurvature
  dsimp only
  fun_prop

theorem holonomicCoframe_inv_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point => (configuration.coframe point)⁻¹ := by
  rw [continuous_iff_continuousAt]
  intro point
  have ringInverseContinuous :
      ContinuousAt Ring.inverse (Matrix.det (configuration.coframe point)) := by
    have actual := NormedRing.inverse_continuousAt
      (isUnit_iff_ne_zero.mpr (nondegenerate point)).unit
    simpa only [← Ring.inverse_unit, IsUnit.unit_spec] using actual
  exact (continuousAt_matrix_inv (configuration.coframe point)
      ringInverseContinuous).comp
        ((holonomicCoframe_continuous configuration smooth).continuousAt)

theorem coframeTwoFormLinear_apply_continuous
    (coframe : BasePoint → LorentzianCoframe)
    (coframeContinuous : Continuous coframe)
    (form : BasePoint → GaugeTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point => coframeTwoFormLinear (coframe point) (form point) := by
  apply continuous_pi
  intro outputPair
  change Continuous fun point =>
    ∑ inputPair : Fin 6,
      coframeWedge (coframe point) outputPair inputPair * form point inputPair
  apply continuous_finsetSum
  intro inputPair _
  have coframeEntryContinuous : ∀ row column,
      Continuous fun point => coframe point row column := fun row column =>
    (continuous_apply column).comp
      ((continuous_apply row).comp coframeContinuous)
  have formEntryContinuous : ∀ pair,
      Continuous fun point => form point pair := fun pair =>
    (continuous_apply pair).comp formContinuous
  unfold coframeWedge
  fun_prop

theorem lorentzianCoframeHodge_apply_continuous
    (form : BasePoint → GaugeTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point => lorentzianCoframeHodge (form point) := by
  apply continuous_pi
  intro pair
  fin_cases pair <;>
    simp [lorentzianCoframeHodge] <;> fun_prop

theorem holonomicGaugeSpacetimeHodge_apply_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (form : BasePoint → GaugeTwoForm)
    (formContinuous : Continuous form) :
    Continuous fun point =>
      coframeGaugeSpacetimeHodgeLinear
        (configuration.coframe point) (form point) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have forwardContinuous := coframeTwoFormLinear_apply_continuous
    configuration.coframe coframeContinuous form formContinuous
  have fixedHodgeContinuous := lorentzianCoframeHodge_apply_continuous
    (fun point => coframeTwoFormLinear
      (configuration.coframe point) (form point)) forwardContinuous
  have inverseContinuous := holonomicCoframe_inv_continuous
    configuration smooth nondegenerate
  have pulledBackContinuous := coframeTwoFormLinear_apply_continuous
    (fun point => (configuration.coframe point)⁻¹) inverseContinuous
    (fun point => lorentzianCoframeHodge
      (coframeTwoFormLinear (configuration.coframe point) (form point)))
    fixedHodgeContinuous
  simpa [coframeGaugeSpacetimeHodgeLinear,
    inverseCoframeTwoFormLinear, LinearMap.comp_apply,
    lorentzianCoframeHodgeEquiv] using
      pulledBackContinuous

theorem holonomicGravitySpacetimeHodge_apply_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (bivector : BasePoint → PhysicalBivector)
    (bivectorContinuous : Continuous bivector) :
    Continuous fun point =>
      gravitySpacetimeHodge (configuration.coframe point)
        (bivector point) := by
  apply continuous_pi
  intro internalPair
  exact holonomicGaugeSpacetimeHodge_apply_continuous
    configuration smooth nondegenerate
      (fun point => bivector point internalPair)
      ((continuous_apply internalPair).comp bivectorContinuous)

theorem gravityCoframePairing_apply_continuous
    (coframe : BasePoint → LorentzianCoframe)
    (coframeContinuous : Continuous coframe)
    (first second : BasePoint → PhysicalBivector)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      gravityCoframePairing (coframe point) (first point) (second point) := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
  apply continuous_finsetSum
  intro internalPair _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro spacetimePair _
  have firstEntryContinuous := (continuous_apply spacetimePair).comp
    (coframeTwoFormLinear_apply_continuous coframe coframeContinuous
      (fun point => first point internalPair)
      ((continuous_apply internalPair).comp firstContinuous))
  have secondEntryContinuous := (continuous_apply spacetimePair).comp
    (coframeTwoFormLinear_apply_continuous coframe coframeContinuous
      (fun point => second point internalPair)
      ((continuous_apply internalPair).comp secondContinuous))
  exact (continuous_const.mul firstEntryContinuous).mul secondEntryContinuous

theorem gravityInternalDual_apply_continuous
    (bivector : BasePoint → PhysicalBivector)
    (bivectorContinuous : Continuous bivector) :
    Continuous fun point => gravityInternalDualEquiv (bivector point) := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  have componentContinuous : ∀ sourceInternalPair,
      Continuous fun point =>
        bivector point sourceInternalPair spacetimePair :=
    fun sourceInternalPair => (continuous_apply spacetimePair).comp
      ((continuous_apply sourceInternalPair).comp bivectorContinuous)
  change Continuous fun point =>
    internalBivectorDual (bivector point) internalPair spacetimePair
  unfold internalBivectorDual
  fin_cases internalPair <;>
    simp [lorentzianCoframeHodge] <;> fun_prop

theorem holonomicGravityInternalDual_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      gravityInternalDualEquiv (configuration.gravityAuxiliary point) := by
  exact gravityInternalDual_apply_continuous configuration.gravityAuxiliary
    (holonomicGravityAuxiliary_continuous configuration smooth)

theorem gravityAuxiliaryFirstVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Continuous
      (holonomicGravityAuxiliaryFirstVariationDensity
        configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous (variation : BasePoint → PhysicalBivector) :=
    variation.smooth.continuous
  have curvatureContinuous := holonomicGravityCurvature_continuous
    configuration smooth
  have auxiliaryContinuous := holonomicGravityAuxiliary_continuous
    configuration smooth
  have internalDualContinuous := holonomicGravityInternalDual_continuous
    configuration smooth
  have internalDualVariationContinuous := gravityInternalDual_apply_continuous
    variation variationContinuous
  have hodgeCurvatureContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate (holonomicGravityCurvature configuration)
      curvatureContinuous
  have hodgeInternalDualContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (fun point => gravityInternalDualEquiv
        (configuration.gravityAuxiliary point)) internalDualContinuous
  have hodgeVariationContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (fun point => gravityInternalDualEquiv (variation point))
      internalDualVariationContinuous
  have firstPairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous variation
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (holonomicGravityCurvature configuration point))
      variationContinuous hodgeCurvatureContinuous
  have secondPairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous variation
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (gravityInternalDualEquiv (configuration.gravityAuxiliary point)))
      variationContinuous hodgeInternalDualContinuous
  have thirdPairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous configuration.gravityAuxiliary
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (gravityInternalDualEquiv (variation point)))
      auxiliaryContinuous hodgeVariationContinuous
  have multiplierContinuous :=
    holonomicGravitySimplicityMultiplier_continuous configuration smooth
  have residualContinuous : Continuous fun point =>
      generatedGravitySimplicityResidual
        (toContinuumPointField configuration point) := by
    apply continuous_pi
    intro internalPair
    apply continuous_pi
    intro spacetimePair
    exact generatedGravitySimplicityResidual_component_continuous
      configuration smooth internalPair spacetimePair
  have simplicityFirstContinuous : Continuous fun point =>
      gravityAuxiliarySimplicityFirstVariationDensity
        (toContinuumPointField configuration point) (variation point) := by
    unfold gravityAuxiliarySimplicityFirstVariationDensity
    apply continuous_finsetSum
    intro internalPair _
    apply continuous_finsetSum
    intro spacetimePair _
    fun_prop
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold holonomicGravityAuxiliaryFirstVariationDensity
    gravityAuxiliaryFirstVariationDensity
    gravityAuxiliaryBFFirstVariationDensity
  exact volumeContinuous.mul
    ((firstPairingContinuous.sub
      (continuous_const.mul
        (secondPairingContinuous.add thirdPairingContinuous))).add
      simplicityFirstContinuous)

theorem gravityAuxiliarySecondVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Continuous
      (holonomicGravityAuxiliarySecondVariationDensity
        configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have variationContinuous : Continuous (variation : BasePoint → PhysicalBivector) :=
    variation.smooth.continuous
  have internalDualVariationContinuous : Continuous fun point =>
      gravityInternalDualEquiv (variation point) :=
    gravityInternalDual_apply_continuous variation variationContinuous
  have hodgeVariationContinuous :=
    holonomicGravitySpacetimeHodge_apply_continuous configuration smooth
      nondegenerate
      (fun point => gravityInternalDualEquiv (variation point))
      internalDualVariationContinuous
  have pairingContinuous := gravityCoframePairing_apply_continuous
    configuration.coframe coframeContinuous variation
      (fun point => gravitySpacetimeHodge (configuration.coframe point)
        (gravityInternalDualEquiv (variation point)))
      variationContinuous hodgeVariationContinuous
  have multiplierContinuous :=
    holonomicGravitySimplicityMultiplier_continuous configuration smooth
  have simplicitySecondContinuous : Continuous fun point =>
      gravityAuxiliarySimplicitySecondVariationDensity
        (toContinuumPointField configuration point) (variation point) := by
    unfold gravityAuxiliarySimplicitySecondVariationDensity
    apply continuous_finsetSum
    intro internalPair _
    apply continuous_finsetSum
    intro spacetimePair _
    fun_prop
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold holonomicGravityAuxiliarySecondVariationDensity
    gravityAuxiliarySecondVariationDensity
    gravityAuxiliaryBFSecondVariationDensity
  exact volumeContinuous.mul
    ((continuous_const.mul pairingContinuous).add simplicitySecondContinuous)

@[simp] theorem gravitySpacetimeHodge_zero
    (coframe : LorentzianCoframe) :
    gravitySpacetimeHodge coframe 0 = 0 := by
  funext internalPair spacetimePair
  simp [gravitySpacetimeHodge]

theorem gravityAuxiliaryFirstVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasCompactSupport
      (holonomicGravityAuxiliaryFirstVariationDensity
        configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicGravityAuxiliaryFirstVariationDensity,
    gravityAuxiliaryFirstVariationDensity,
    gravityAuxiliaryBFFirstVariationDensity,
    gravityAuxiliarySimplicityFirstVariationDensity,
    gravityCoframePairing, coframeTwoFormMetricPairing,
    variationZero]

theorem gravityAuxiliarySecondVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasCompactSupport
      (holonomicGravityAuxiliarySecondVariationDensity
        configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicGravityAuxiliarySecondVariationDensity,
    gravityAuxiliarySecondVariationDensity,
    gravityAuxiliaryBFSecondVariationDensity,
    gravityAuxiliarySimplicitySecondVariationDensity,
    gravityCoframePairing, coframeTwoFormMetricPairing,
    variationZero]

theorem gravityAuxiliaryFirstVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Integrable
      (holonomicGravityAuxiliaryFirstVariationDensity
        configuration variation) :=
  (gravityAuxiliaryFirstVariationDensity_continuous configuration smooth
      nondegenerate variation).integrable_of_hasCompactSupport
    (gravityAuxiliaryFirstVariationDensity_compact configuration variation)

theorem gravityAuxiliarySecondVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Integrable
      (holonomicGravityAuxiliarySecondVariationDensity
        configuration variation) :=
  (gravityAuxiliarySecondVariationDensity_continuous configuration smooth
      nondegenerate variation).integrable_of_hasCompactSupport
    (gravityAuxiliarySecondVariationDensity_compact configuration variation)

theorem holonomicIntegratedUnifiedAction_gravityAuxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source chart
        (varyGravityAuxiliary configuration variation parameter) =
      holonomicIntegratedUnifiedAction source chart configuration +
        parameter * (
          ∫ point : BasePoint,
            holonomicGravityAuxiliaryFirstVariationDensity
              configuration variation point) +
        parameter ^ 2 * (
          ∫ point : BasePoint,
            holonomicGravityAuxiliarySecondVariationDensity
              configuration variation point) := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (varyGravityAuxiliary configuration variation parameter) point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicGravityAuxiliaryFirstVariationDensity
            configuration variation point +
        parameter ^ 2 *
          holonomicGravityAuxiliarySecondVariationDensity
            configuration variation point := by
    funext point
    exact holonomicLocalDensity_gravityAuxiliary_quadratic source
      (sourceGeneratedUnifiedCouplings source) chart point configuration
        variation parameter
  rw [pointwise]
  have firstIntegrable := gravityAuxiliaryFirstVariationDensity_integrable
    configuration smooth nondegenerate variation
  have secondIntegrable := gravityAuxiliarySecondVariationDensity_integrable
    configuration smooth nondegenerate variation
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter * holonomicGravityAuxiliaryFirstVariationDensity
              configuration variation point +
          parameter ^ 2 * holonomicGravityAuxiliarySecondVariationDensity
            configuration variation point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter * holonomicGravityAuxiliaryFirstVariationDensity
              configuration variation point) +
        ∫ point : BasePoint,
          parameter ^ 2 * holonomicGravityAuxiliarySecondVariationDensity
            configuration variation point := by
      exact integral_add
        (densityIntegrable.add (firstIntegrable.const_mul parameter))
        (secondIntegrable.const_mul (parameter ^ 2))
    _ = ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) chart point
            (toContinuumPointField configuration point)) +
        ∫ point : BasePoint,
          parameter * holonomicGravityAuxiliaryFirstVariationDensity
            configuration variation point) +
        ∫ point : BasePoint,
          parameter ^ 2 * holonomicGravityAuxiliarySecondVariationDensity
            configuration variation point := by
      rw [integral_add densityIntegrable
        (firstIntegrable.const_mul parameter)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

theorem holonomicIntegratedUnifiedAction_gravityAuxiliary_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyGravityAuxiliary configuration variation parameter))
      (∫ point : BasePoint,
        holonomicGravityAuxiliaryFirstVariationDensity
          configuration variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    holonomicGravityAuxiliaryFirstVariationDensity
      configuration variation point
  let secondIntegral := ∫ point : BasePoint,
    holonomicGravityAuxiliarySecondVariationDensity
      configuration variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyGravityAuxiliary configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source chart configuration +
          parameter * firstIntegral + parameter ^ 2 * secondIntegral := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_gravityAuxiliary_quadratic
      source chart configuration smooth nondegenerate densityIntegrable
        variation parameter
  rw [actionEquality]
  change HasDerivAt
    ((fun parameter =>
      holonomicIntegratedUnifiedAction source chart configuration +
        parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * secondIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicIntegratedUnifiedAction source chart configuration)).add
        (((hasDerivAt_id (x := 0)).pow 2).mul_const secondIntegral))

def GravityAuxiliaryActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyGravityAuxiliary configuration variation parameter))
      0 0

def GravityAuxiliaryWeakEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    (∫ point : BasePoint,
      holonomicGravityAuxiliaryFirstVariationDensity
        configuration variation point) = 0

theorem gravityAuxiliaryActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (stationary : GravityAuxiliaryActionStationary
      source chart configuration) :
    GravityAuxiliaryWeakEquation configuration := by
  intro variation
  have actual := holonomicIntegratedUnifiedAction_gravityAuxiliary_hasDerivAt
    source chart configuration smooth nondegenerate densityIntegrable variation
  exact ((stationary variation).unique actual).symm

theorem gravityCoframePairing_sub_right
    (coframe : LorentzianCoframe)
    (first second residual : PhysicalBivector) :
    gravityCoframePairing coframe residual (first - second) =
      gravityCoframePairing coframe residual first -
        gravityCoframePairing coframe residual second := by
  simp only [sub_eq_add_neg, gravityCoframePairing_add_right]
  rw [show -second = (-1 : ℝ) • second by ext; simp]
  rw [gravityCoframePairing_smul_right]
  ring

theorem gravitySpacetimeHodge_sub
    (coframe : LorentzianCoframe) (first second : PhysicalBivector) :
    gravitySpacetimeHodge coframe (first - second) =
      gravitySpacetimeHodge coframe first -
        gravitySpacetimeHodge coframe second := by
  funext internalPair spacetimePair
  simp [gravitySpacetimeHodge, map_sub]

def gravityAuxiliaryEquationResidual
    (field : StageNineContinuumPointField) : PhysicalBivector :=
  field.gravityCurvature - gravityInternalDualEquiv field.gravityAuxiliary

def holonomicGravityAuxiliaryEquationResidual
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : PhysicalBivector :=
  gravityAuxiliaryEquationResidual (toContinuumPointField configuration point)

theorem gravityAuxiliaryBFFirstVariationDensity_eq_residualPairing
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0)
    (variation : PhysicalBivector) :
    gravityAuxiliaryBFFirstVariationDensity field variation =
      gravityCoframePairing field.coframe variation
        (gravitySpacetimeHodge field.coframe
          (gravityAuxiliaryEquationResidual field)) := by
  unfold gravityAuxiliaryBFFirstVariationDensity
    gravityAuxiliaryEquationResidual
  rw [← gravityConstitutiveBilinear_symmetric field.coframe nondegenerate
    variation field.gravityAuxiliary]
  rw [gravitySpacetimeHodge_sub, gravityCoframePairing_sub_right]
  ring

theorem generatedGravitySimplicityResidual_eq_zero_of_simplicity
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : GravitySimplicityEquation configuration)
    (point : BasePoint) :
    generatedGravitySimplicityResidual
      (toContinuumPointField configuration point) = 0 := by
  unfold generatedGravitySimplicityResidual toContinuumPointField
  rw [simplicity point]
  exact sub_self _

theorem gravityAuxiliarySimplicityFirstVariationDensity_eq_zero_of_simplicity
    (configuration : StageNineHolonomicConfiguration)
    (simplicity : GravitySimplicityEquation configuration)
    (variation : PhysicalBivector) (point : BasePoint) :
    gravityAuxiliarySimplicityFirstVariationDensity
        (toContinuumPointField configuration point) variation = 0 := by
  unfold gravityAuxiliarySimplicityFirstVariationDensity
  rw [generatedGravitySimplicityResidual_eq_zero_of_simplicity
    configuration simplicity point]
  simp

theorem holonomicGravityAuxiliaryFirstVariationDensity_eq_residualPairing
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration)
    (variation : BasePoint → PhysicalBivector) (point : BasePoint) :
    holonomicGravityAuxiliaryFirstVariationDensity
        configuration variation point =
      generatedVolumeDensity (toContinuumPointField configuration point) *
        gravityCoframePairing (configuration.coframe point)
          (variation point)
          (gravitySpacetimeHodge (configuration.coframe point)
            (holonomicGravityAuxiliaryEquationResidual configuration point)) := by
  unfold holonomicGravityAuxiliaryFirstVariationDensity
    gravityAuxiliaryFirstVariationDensity
  rw [gravityAuxiliaryBFFirstVariationDensity_eq_residualPairing
    (toContinuumPointField configuration point) (nondegenerate point)]
  rw [gravityAuxiliarySimplicityFirstVariationDensity_eq_zero_of_simplicity
    configuration simplicity (variation point) point]
  simp [holonomicGravityAuxiliaryEquationResidual, toContinuumPointField]

def physicalBivectorCoordinateDirection
    (internalPair spacetimePair : Fin 6) : PhysicalBivector :=
  fun candidateInternal candidateSpacetime =>
    if candidateInternal = internalPair then
      if candidateSpacetime = spacetimePair then 1 else 0
    else 0

theorem singlePhysicalBivectorVariation_apply
    (internalPair spacetimePair : Fin 6)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    singlePhysicalBivectorVariation internalPair spacetimePair variation point =
      variation point • physicalBivectorCoordinateDirection
        internalPair spacetimePair := by
  funext candidateInternal candidateSpacetime
  simp [singlePhysicalBivectorVariation,
    physicalBivectorCoordinateDirection]

/-- Polynomial form of `⟨first, *_e residual⟩_e`.  The inverse coframe
has cancelled by the same-coframe intertwining theorem, so continuity follows
from primitive smooth fields without an extra regularity certificate. -/
def gravityAuxiliaryHodgePairingPolynomial
    (coframe : LorentzianCoframe)
    (first residual : PhysicalBivector) : ℝ :=
  ∑ internalPair : Fin 6,
    lorentzianTwoFormSign internalPair *
      ∑ spacetimePair : Fin 6,
        lorentzianTwoFormSign spacetimePair *
          coframeTwoFormLinear coframe (first internalPair) spacetimePair *
          lorentzianCoframeHodge
            (coframeTwoFormLinear coframe (residual internalPair))
              spacetimePair

theorem gravityAuxiliaryHodgePairingPolynomial_eq
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (first residual : PhysicalBivector) :
    gravityAuxiliaryHodgePairingPolynomial coframe first residual =
      gravityCoframePairing coframe first
        (gravitySpacetimeHodge coframe residual) := by
  unfold gravityAuxiliaryHodgePairingPolynomial
    gravityCoframePairing coframeTwoFormMetricPairing
    gravitySpacetimeHodge
  simp_rw [coframeTwoFormLinear_dynamicHodge coframe nondegenerate]

def gravityAuxiliaryCoordinateCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    gravityAuxiliaryHodgePairingPolynomial
      (configuration.coframe point)
      (physicalBivectorCoordinateDirection internalPair spacetimePair)
      (holonomicGravityAuxiliaryEquationResidual configuration point)

theorem holonomicGravityAuxiliaryEquationResidual_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous
      (holonomicGravityAuxiliaryEquationResidual configuration) := by
  have curvatureContinuous := holonomicGravityCurvature_continuous
    configuration smooth
  have internalDualContinuous := holonomicGravityInternalDual_continuous
    configuration smooth
  unfold holonomicGravityAuxiliaryEquationResidual
    gravityAuxiliaryEquationResidual toContinuumPointField
  exact curvatureContinuous.sub internalDualContinuous

theorem gravityAuxiliaryCoordinateCoefficient_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (internalPair spacetimePair : Fin 6) :
    Continuous (gravityAuxiliaryCoordinateCoefficient configuration
      internalPair spacetimePair) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have residualContinuous :=
    holonomicGravityAuxiliaryEquationResidual_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  unfold gravityAuxiliaryCoordinateCoefficient
    gravityAuxiliaryHodgePairingPolynomial
  apply volumeContinuous.mul
  apply continuous_finsetSum
  intro candidateInternal _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro candidateSpacetime _
  have directionTransformContinuous :=
    (continuous_apply candidateSpacetime).comp
      (coframeTwoFormLinear_apply_continuous configuration.coframe
        coframeContinuous
        (fun _ => physicalBivectorCoordinateDirection
          internalPair spacetimePair candidateInternal)
        continuous_const)
  have residualTransformContinuous :=
    coframeTwoFormLinear_apply_continuous configuration.coframe
      coframeContinuous
      (fun point => holonomicGravityAuxiliaryEquationResidual
        configuration point candidateInternal)
      ((continuous_apply candidateInternal).comp residualContinuous)
  have hodgeResidualContinuous :=
    (continuous_apply candidateSpacetime).comp
      (lorentzianCoframeHodge_apply_continuous
        (fun point => coframeTwoFormLinear (configuration.coframe point)
          (holonomicGravityAuxiliaryEquationResidual
            configuration point candidateInternal))
        residualTransformContinuous)
  exact (continuous_const.mul directionTransformContinuous).mul
    hodgeResidualContinuous

theorem holonomicGravityAuxiliaryFirstVariationDensity_single
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration)
    (internalPair spacetimePair : Fin 6)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    holonomicGravityAuxiliaryFirstVariationDensity configuration
        (singlePhysicalBivectorVariation
          internalPair spacetimePair variation) point =
      variation point * gravityAuxiliaryCoordinateCoefficient
        configuration internalPair spacetimePair point := by
  rw [holonomicGravityAuxiliaryFirstVariationDensity_eq_residualPairing
    configuration nondegenerate simplicity]
  rw [singlePhysicalBivectorVariation_apply]
  rw [gravityCoframePairing_smul_left]
  rw [← gravityAuxiliaryHodgePairingPolynomial_eq
    (configuration.coframe point) (nondegenerate point)]
  unfold gravityAuxiliaryCoordinateCoefficient
  ring

theorem gravityAuxiliaryWeakEquation_coordinate_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration)
    (weakEquation : GravityAuxiliaryWeakEquation configuration)
    (internalPair spacetimePair : Fin 6) :
    gravityAuxiliaryCoordinateCoefficient configuration
        internalPair spacetimePair = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (gravityAuxiliaryCoordinateCoefficient configuration
      internalPair spacetimePair)
    (gravityAuxiliaryCoordinateCoefficient_continuous configuration smooth
      internalPair spacetimePair)
  intro variation
  have weakCoordinate := weakEquation
    (singlePhysicalBivectorVariation
      internalPair spacetimePair variation)
  have integrandEquality :
      (fun point : BasePoint =>
        holonomicGravityAuxiliaryFirstVariationDensity configuration
          (singlePhysicalBivectorVariation
            internalPair spacetimePair variation) point) =
      fun point => variation point *
        gravityAuxiliaryCoordinateCoefficient configuration
          internalPair spacetimePair point := by
    funext point
    exact holonomicGravityAuxiliaryFirstVariationDensity_single
      configuration nondegenerate simplicity internalPair spacetimePair
        variation point
  rw [integrandEquality] at weakCoordinate
  exact weakCoordinate

theorem lorentzianTwoFormSign_sq (pair : Fin 6) :
    lorentzianTwoFormSign pair ^ 2 = 1 := by
  fin_cases pair <;>
    simp [lorentzianTwoFormSign, minkowskiInternalSign,
      pairFirst, pairSecond]

def gravityMetricPositiveTestDirection
    (coframe : LorentzianCoframe)
    (residual : PhysicalBivector) : PhysicalBivector :=
  fun internalPair =>
    coframeTwoFormLinear coframe⁻¹ fun spacetimePair =>
      lorentzianTwoFormSign internalPair *
        lorentzianTwoFormSign spacetimePair *
        coframeTwoFormLinear coframe (residual internalPair) spacetimePair

theorem gravityMetricPositiveTestDirection_transform
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : PhysicalBivector) (internalPair : Fin 6) :
    coframeTwoFormLinear coframe
        (gravityMetricPositiveTestDirection coframe residual internalPair) =
      fun spacetimePair =>
        lorentzianTwoFormSign internalPair *
          lorentzianTwoFormSign spacetimePair *
          coframeTwoFormLinear coframe (residual internalPair) spacetimePair := by
  unfold gravityMetricPositiveTestDirection
  have cancellation := congrArg
    (fun operator : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm =>
      operator (fun spacetimePair =>
        lorentzianTwoFormSign internalPair *
          lorentzianTwoFormSign spacetimePair *
          coframeTwoFormLinear coframe
            (residual internalPair) spacetimePair))
    (coframeTwoFormLinear_comp_inv coframe nondegenerate)
  simpa [LinearMap.comp_apply] using cancellation

theorem gravityCoframePairing_positiveTestDirection
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : PhysicalBivector) :
    gravityCoframePairing coframe
        (gravityMetricPositiveTestDirection coframe residual) residual =
      ∑ internalPair : Fin 6,
        ∑ spacetimePair : Fin 6,
          coframeTwoFormLinear coframe
            (residual internalPair) spacetimePair ^ 2 := by
  unfold gravityCoframePairing coframeTwoFormMetricPairing
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [gravityMetricPositiveTestDirection_transform coframe nondegenerate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  calc
    lorentzianTwoFormSign internalPair *
        (lorentzianTwoFormSign spacetimePair *
          (lorentzianTwoFormSign internalPair *
            lorentzianTwoFormSign spacetimePair *
            coframeTwoFormLinear coframe
              (residual internalPair) spacetimePair) *
          coframeTwoFormLinear coframe
            (residual internalPair) spacetimePair) =
      lorentzianTwoFormSign internalPair ^ 2 *
        lorentzianTwoFormSign spacetimePair ^ 2 *
        coframeTwoFormLinear coframe
          (residual internalPair) spacetimePair ^ 2 := by ring
    _ = coframeTwoFormLinear coframe
          (residual internalPair) spacetimePair ^ 2 := by
      rw [lorentzianTwoFormSign_sq, lorentzianTwoFormSign_sq]
      ring

theorem gravityCoframePairing_nondegenerate_right
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (residual : PhysicalBivector)
    (annihilates : ∀ first,
      gravityCoframePairing coframe first residual = 0) :
    residual = 0 := by
  have sumSquaresZero :
      (∑ internalPair : Fin 6,
        ∑ spacetimePair : Fin 6,
          coframeTwoFormLinear coframe
            (residual internalPair) spacetimePair ^ 2) = 0 := by
    rw [← gravityCoframePairing_positiveTestDirection
      coframe nondegenerate residual]
    exact annihilates (gravityMetricPositiveTestDirection coframe residual)
  funext internalPair spacetimePair
  have innerSumZero :
      (∑ candidateSpacetime : Fin 6,
        coframeTwoFormLinear coframe
          (residual internalPair) candidateSpacetime ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp sumSquaresZero
        internalPair (Finset.mem_univ internalPair)
  have transformedSquareZero :
      coframeTwoFormLinear coframe
        (residual internalPair) spacetimePair ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp
      innerSumZero spacetimePair (Finset.mem_univ spacetimePair)
  have transformedZero :
      coframeTwoFormLinear coframe (residual internalPair) = 0 := by
    funext candidateSpacetime
    have candidateSquareZero :
        coframeTwoFormLinear coframe
          (residual internalPair) candidateSpacetime ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp
        innerSumZero candidateSpacetime (Finset.mem_univ candidateSpacetime)
    exact sq_eq_zero_iff.mp candidateSquareZero
  have residualInternalZero : residual internalPair = 0 := by
    apply coframeTwoFormLinear_injective coframe nondegenerate
    simpa using transformedZero
  exact congrFun residualInternalZero spacetimePair

def gravityCoframePairingLeftLinear
    (coframe : LorentzianCoframe)
    (residual : PhysicalBivector) : PhysicalBivector →ₗ[ℝ] ℝ where
  toFun := fun first => gravityCoframePairing coframe first residual
  map_add' := fun first second =>
    gravityCoframePairing_add_left coframe first second residual
  map_smul' := by
    intro parameter first
    simpa [smul_eq_mul] using
      gravityCoframePairing_smul_left coframe parameter first residual

theorem physicalBivector_eq_sum_coordinates (bivector : PhysicalBivector) :
    bivector =
      ∑ internalPair : Fin 6,
        ∑ spacetimePair : Fin 6,
          bivector internalPair spacetimePair •
            physicalBivectorCoordinateDirection
              internalPair spacetimePair := by
  funext candidateInternal candidateSpacetime
  simp [physicalBivectorCoordinateDirection]

theorem gravityCoframePairing_eq_zero_of_coordinate_zero
    (coframe : LorentzianCoframe) (residual : PhysicalBivector)
    (coordinateZero : ∀ internalPair spacetimePair,
      gravityCoframePairing coframe
        (physicalBivectorCoordinateDirection internalPair spacetimePair)
        residual = 0) :
    ∀ first, gravityCoframePairing coframe first residual = 0 := by
  intro first
  change gravityCoframePairingLeftLinear coframe residual first = 0
  rw [physicalBivector_eq_sum_coordinates first]
  simp [gravityCoframePairingLeftLinear, coordinateZero]

theorem gravitySpacetimeHodge_injective
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    Function.Injective (gravitySpacetimeHodge coframe) := by
  intro first second equality
  funext internalPair spacetimePair
  have componentEquality := congrFun equality internalPair
  have twiceEquality := congrArg
    (coframeGaugeSpacetimeHodgeLinear coframe) componentEquality
  have formEquality : first internalPair = second internalPair := by
    simpa [gravitySpacetimeHodge,
      coframeGaugeSpacetimeHodgeLinear_square coframe nondegenerate] using
        twiceEquality
  exact congrFun formEquality spacetimePair

def GravityAuxiliaryEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point,
    holonomicGravityCurvature configuration point =
      gravityInternalDualEquiv (configuration.gravityAuxiliary point)

theorem gravityAuxiliaryWeakEquation_implies_equation
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (simplicity : GravitySimplicityEquation configuration)
    (weakEquation : GravityAuxiliaryWeakEquation configuration) :
    GravityAuxiliaryEquation configuration := by
  intro point
  have coordinatePairingZero : ∀ internalPair spacetimePair,
      gravityCoframePairing (configuration.coframe point)
        (physicalBivectorCoordinateDirection internalPair spacetimePair)
        (gravitySpacetimeHodge (configuration.coframe point)
          (holonomicGravityAuxiliaryEquationResidual configuration point)) = 0 := by
    intro internalPair spacetimePair
    have coefficientZero := congrFun
      (gravityAuxiliaryWeakEquation_coordinate_zero configuration smooth
        nondegenerate simplicity weakEquation internalPair spacetimePair) point
    have coefficientZeroScalar :
        gravityAuxiliaryCoordinateCoefficient configuration
          internalPair spacetimePair point = 0 := by
      simpa using coefficientZero
    have volumeNonzero :
        generatedVolumeDensity
          (toContinuumPointField configuration point) ≠ 0 := by
      simp only [generatedVolumeDensity, toContinuumPointField]
      exact abs_ne_zero.mpr (nondegenerate point)
    have polynomialZero :
        gravityAuxiliaryHodgePairingPolynomial
          (configuration.coframe point)
          (physicalBivectorCoordinateDirection internalPair spacetimePair)
          (holonomicGravityAuxiliaryEquationResidual configuration point) = 0 := by
      exact (mul_eq_zero.mp (by
        simpa only [gravityAuxiliaryCoordinateCoefficient] using
          coefficientZeroScalar)).resolve_left volumeNonzero
    rw [← gravityAuxiliaryHodgePairingPolynomial_eq
      (configuration.coframe point) (nondegenerate point)]
    exact polynomialZero
  have allPairingZero :=
    gravityCoframePairing_eq_zero_of_coordinate_zero
      (configuration.coframe point)
      (gravitySpacetimeHodge (configuration.coframe point)
        (holonomicGravityAuxiliaryEquationResidual configuration point))
      coordinatePairingZero
  have hodgeResidualZero :
      gravitySpacetimeHodge (configuration.coframe point)
        (holonomicGravityAuxiliaryEquationResidual configuration point) = 0 :=
    gravityCoframePairing_nondegenerate_right
      (configuration.coframe point) (nondegenerate point) _ allPairingZero
  have residualZero :
      holonomicGravityAuxiliaryEquationResidual configuration point = 0 := by
    apply gravitySpacetimeHodge_injective
      (configuration.coframe point) (nondegenerate point)
    simpa using hodgeResidualZero
  simpa [holonomicGravityAuxiliaryEquationResidual,
    gravityAuxiliaryEquationResidual, toContinuumPointField,
    sub_eq_zero] using residualZero

theorem gravityAuxiliaryActionStationary_implies_equation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable
      source chart configuration)
    (simplicity : GravitySimplicityEquation configuration)
    (stationary : GravityAuxiliaryActionStationary
      source chart configuration) :
    GravityAuxiliaryEquation configuration :=
  gravityAuxiliaryWeakEquation_implies_equation configuration smooth
    nondegenerate simplicity
    (gravityAuxiliaryActionStationary_implies_weakEquation source chart
      configuration smooth nondegenerate densityIntegrable stationary)

end

end SaturationMonoid.PhysicsCore.StageNineGravityAuxiliaryVariation
