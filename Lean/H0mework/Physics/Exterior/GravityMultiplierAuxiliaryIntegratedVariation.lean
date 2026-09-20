import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryVariation
import H0mework.Physics.Geometry.TopologicalWeakEquation

/-!
# Integrated form-native gravity multiplier and auxiliary variations

This module promotes the two pointwise algebraic gravity variations of the
form-native mother action to its actual four-dimensional integral.  The same
new action hash generates the compact-support derivatives, weak equations,
selected-branch simplicity equation, and the unique gravity reaction

`lambda = star_internal(B) - N(F_raw)`.

All analytic regularity is reconstructed from
`StageNineHolonomicConfiguration.Smooth` and finite-dimensional continuity.
No historical action variation, nondegeneracy premise, fixed actual,
stationarity receipt, shell certificate, or supplied reaction enters a
producer mouth.  These are the two algebraic gravity legs only; no coframe or
Lorentz-connection equation is claimed here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCompactSupportIntegrationByParts
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalWeakEquation
open MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! ## Form-native regularity from the primitive smooth configuration -/

private theorem formNativeHolonomicCoframe_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ configuration.coframe := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  exact smooth.1 row column

private theorem formNativeHolonomicGravityAuxiliary_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.gravityAuxiliary := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  exact (smooth.2.2.1 internalPair spacetimePair).continuous

private theorem formNativeHolonomicGravityMultiplier_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.gravitySimplicityMultiplier := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  exact (smooth.2.2.2.1 internalPair spacetimePair).continuous

/-- The primitive multiplier path remains inside the smooth holonomic
configuration domain for every real parameter.  This is an admissible-path
receipt, not another action equation. -/
theorem varyFormNativeGravityMultiplier_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    (varyFormNativeGravityMultiplier configuration variation parameter).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  have scaledVariationSmooth : ContDiff ℝ ∞ fun point =>
      parameter • variation point :=
    (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
      contDiff_const).smul variation.smooth
  have variedMultiplierSmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        (varyFormNativeGravityMultiplier configuration variation parameter)
          |>.gravitySimplicityMultiplier point internalPair spacetimePair := by
    intro internalPair spacetimePair
    have scaledCoordinateSmooth :=
      contDiff_pi.mp
        (contDiff_pi.mp scaledVariationSmooth internalPair) spacetimePair
    simpa [varyFormNativeGravityMultiplier] using
      (gravityMultiplierSmooth internalPair spacetimePair).add
        scaledCoordinateSmooth
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    variedMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
    scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-- The primitive gravity-auxiliary path likewise remains in the smooth
holonomic domain.  It changes no multiplier, connection, or matter slot. -/
theorem varyFormNativeGravityAuxiliary_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    (varyFormNativeGravityAuxiliary configuration variation parameter).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  have scaledVariationSmooth : ContDiff ℝ ∞ fun point =>
      parameter • variation point :=
    (show ContDiff ℝ ∞ fun _ : BasePoint => parameter from
      contDiff_const).smul variation.smooth
  have variedAuxiliarySmooth : ∀ internalPair spacetimePair,
      ContDiff ℝ ∞ fun point =>
        (varyFormNativeGravityAuxiliary configuration variation parameter)
          |>.gravityAuxiliary point internalPair spacetimePair := by
    intro internalPair spacetimePair
    have scaledCoordinateSmooth :=
      contDiff_pi.mp
        (contDiff_pi.mp scaledVariationSmooth internalPair) spacetimePair
    simpa [varyFormNativeGravityAuxiliary] using
      (gravityAuxiliarySmooth internalPair spacetimePair).add
        scaledCoordinateSmooth
  exact ⟨coframeSmooth, gravityConnectionSmooth, variedAuxiliarySmooth,
    gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
    scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

/-- The selected-branch multiplier residual is continuous without a
nondegeneracy premise. -/
theorem holonomicFormNativeGravityMultiplierEulerResidual_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      formNativeGravityMultiplierEulerResidual
        (toContinuumPointField configuration point) := by
  have auxiliaryContinuous :=
    formNativeHolonomicGravityAuxiliary_continuous configuration smooth
  have coframeSmooth := formNativeHolonomicCoframe_contDiff configuration smooth
  have iiPlusContinuous : Continuous fun point =>
      physicalIIPlusBivector (configuration.coframe point) :=
    (physicalIIPlusBivector_contDiff.comp coframeSmooth).continuous
  unfold formNativeGravityMultiplierEulerResidual
    generatedGravitySimplicityResidual toContinuumPointField
  exact auxiliaryContinuous.sub iiPlusContinuous

private theorem gravityTopologicalWedgeCoefficient_apply_continuous
    (first second : BasePoint → PhysicalBivector)
    (firstContinuous : Continuous first)
    (secondContinuous : Continuous second) :
    Continuous fun point =>
      gravityTopologicalWedgeCoefficient (first point) (second point) := by
  unfold gravityTopologicalWedgeCoefficient
  apply continuous_finsetSum
  intro internalPair _
  have firstPairContinuous : Continuous fun point =>
      first point internalPair :=
    (continuous_apply internalPair).comp firstContinuous
  have secondPairContinuous : Continuous fun point =>
      second point internalPair :=
    (continuous_apply internalPair).comp secondContinuous
  have firstCoordinateContinuous : ∀ spacetimePair,
      Continuous fun point => first point internalPair spacetimePair :=
    fun spacetimePair =>
      (continuous_apply spacetimePair).comp firstPairContinuous
  have secondCoordinateContinuous : ∀ spacetimePair,
      Continuous fun point => second point internalPair spacetimePair :=
    fun spacetimePair =>
      (continuous_apply spacetimePair).comp secondPairContinuous
  rw [show (fun point =>
      lorentzianTwoFormSign internalPair *
        orientedTwoFormWedgeCoefficient
          (first point internalPair) (second point internalPair)) =
      fun point =>
        lorentzianTwoFormSign internalPair *
          (first point internalPair 0 * second point internalPair 3 +
            first point internalPair 1 * second point internalPair 4 +
            first point internalPair 2 * second point internalPair 5 +
            first point internalPair 3 * second point internalPair 0 +
            first point internalPair 4 * second point internalPair 1 +
            first point internalPair 5 * second point internalPair 2) by
    funext point
    rw [orientedTwoFormWedgeCoefficient_explicit]]
  fun_prop

/-! ## Compact multiplier coefficient and integrated action -/

theorem holonomicFormNativeGravityMultiplierFirstVariationDensity_eq_pairing
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector)
    (point : BasePoint) :
    holonomicFormNativeGravityMultiplierFirstVariationDensity configuration
        variation point =
      gravityTopologicalWedgeCoefficient (variation point)
        (formNativeGravityMultiplierEulerResidual
          (toContinuumPointField configuration point)) :=
  rfl

theorem holonomicFormNativeGravityMultiplierFirstVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Continuous
      (holonomicFormNativeGravityMultiplierFirstVariationDensity configuration
        variation) := by
  rw [show holonomicFormNativeGravityMultiplierFirstVariationDensity
      configuration variation = fun point =>
        gravityTopologicalWedgeCoefficient (variation point)
          (formNativeGravityMultiplierEulerResidual
            (toContinuumPointField configuration point)) by
    funext point
    exact holonomicFormNativeGravityMultiplierFirstVariationDensity_eq_pairing
      configuration variation point]
  exact gravityTopologicalWedgeCoefficient_apply_continuous variation
    (fun point => formNativeGravityMultiplierEulerResidual
      (toContinuumPointField configuration point))
    variation.smooth.continuous
    (holonomicFormNativeGravityMultiplierEulerResidual_continuous
      configuration smooth)

theorem holonomicFormNativeGravityMultiplierFirstVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasCompactSupport
      (holonomicFormNativeGravityMultiplierFirstVariationDensity configuration
        variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  rw [holonomicFormNativeGravityMultiplierFirstVariationDensity_eq_pairing,
    variationZero]
  exact gravityTopologicalWedgeCoefficient_zero_left _

theorem holonomicFormNativeGravityMultiplierFirstVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Integrable
      (holonomicFormNativeGravityMultiplierFirstVariationDensity configuration
        variation) :=
  (holonomicFormNativeGravityMultiplierFirstVariationDensity_continuous
      configuration smooth variation).integrable_of_hasCompactSupport
    (holonomicFormNativeGravityMultiplierFirstVariationDensity_compact
      configuration variation)

/-- The actual form-native integrated action is affine along every compactly
supported primitive multiplier path. -/
theorem holonomicFormNativeIntegratedAction_multiplier_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    holonomicFormNativeIntegratedUnifiedAction source chart
        (varyFormNativeGravityMultiplier configuration variation parameter) =
      holonomicFormNativeIntegratedUnifiedAction source chart configuration +
        parameter *
          ∫ point : BasePoint,
            holonomicFormNativeGravityMultiplierFirstVariationDensity
              configuration variation point := by
  unfold holonomicFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedFormNativeUnifiedAction
    integratedFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise :
      (fun point : BasePoint =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField
            (varyFormNativeGravityMultiplier configuration variation parameter)
            point)) =
      fun point =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityMultiplierFirstVariationDensity
            configuration variation point := by
    funext point
    exact holonomicFormNativeLocalDensity_multiplier_affine source
      (sourceGeneratedUnifiedCouplings source) chart point configuration
      variation parameter
  rw [pointwise]
  have firstIntegrable :=
    holonomicFormNativeGravityMultiplierFirstVariationDensity_integrable
      configuration smooth variation
  change Integrable (fun point : BasePoint =>
      generatedFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField configuration point)) at densityIntegrable
  rw [integral_add densityIntegrable
    (firstIntegrable.const_mul parameter), integral_const_mul]

theorem holonomicFormNativeIntegratedAction_multiplier_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityMultiplier configuration variation parameter))
      (∫ point : BasePoint,
        holonomicFormNativeGravityMultiplierFirstVariationDensity
          configuration variation point) 0 := by
  let coefficient := ∫ point : BasePoint,
    holonomicFormNativeGravityMultiplierFirstVariationDensity
      configuration variation point
  have formula :
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityMultiplier configuration variation parameter)) =
      fun parameter =>
        holonomicFormNativeIntegratedUnifiedAction source chart configuration +
          parameter * coefficient := by
    funext parameter
    exact holonomicFormNativeIntegratedAction_multiplier_affine source chart
      configuration smooth densityIntegrable variation parameter
  rw [formula]
  simpa [coefficient] using
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const coefficient).const_add
      (holonomicFormNativeIntegratedUnifiedAction source chart configuration)

/-! ## Multiplier stationarity and the selected simplicity equation -/

/-- Compact-support multiplier stationarity of the new form-native action. -/
def FormNativeGravityMultiplierActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityMultiplier configuration variation parameter))
      0 0

def FormNativeGravityMultiplierWeakEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  TopologicalGravityWeakEquation fun point =>
    formNativeGravityMultiplierEulerResidual
      (toContinuumPointField configuration point)

def FormNativeGravitySimplicityEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    configuration.gravityAuxiliary point =
      physicalIIPlusBivector (configuration.coframe point)

theorem formNativeGravityMultiplierActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    FormNativeGravityMultiplierActionStationary source chart configuration ↔
      FormNativeGravityMultiplierWeakEquation configuration := by
  constructor
  · intro stationary variation
    have actual := holonomicFormNativeIntegratedAction_multiplier_hasDerivAt
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
    have actual := holonomicFormNativeIntegratedAction_multiplier_hasDerivAt
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

theorem formNativeGravityMultiplierWeakEquation_iff_residual_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    FormNativeGravityMultiplierWeakEquation configuration ↔
      (fun point =>
        formNativeGravityMultiplierEulerResidual
          (toContinuumPointField configuration point)) = 0 :=
  topologicalGravityWeakEquation_iff_residual_eq_zero _
    (holonomicFormNativeGravityMultiplierEulerResidual_continuous
      configuration smooth)

theorem formNativeGravityMultiplierResidual_eq_zero_iff_simplicity
    (configuration : StageNineHolonomicConfiguration) :
    (fun point =>
      formNativeGravityMultiplierEulerResidual
        (toContinuumPointField configuration point)) = 0 ↔
      FormNativeGravitySimplicityEquation configuration := by
  constructor
  · intro residualZero point
    apply (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField configuration point)).mp
    exact congrFun residualZero point
  · intro simplicity
    funext point
    apply (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField configuration point)).mpr
    exact simplicity point

/-- The multiplier action equation is exactly the computed `II+` zero fiber;
no Boolean simplicity certificate is consumed. -/
theorem formNativeGravityMultiplierActionStationary_iff_simplicity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    FormNativeGravityMultiplierActionStationary source chart configuration ↔
      FormNativeGravitySimplicityEquation configuration := by
  rw [formNativeGravityMultiplierActionStationary_iff_weakEquation source chart
    configuration smooth densityIntegrable]
  rw [formNativeGravityMultiplierWeakEquation_iff_residual_eq_zero
    configuration smooth]
  exact formNativeGravityMultiplierResidual_eq_zero_iff_simplicity
    configuration

/-! ## Form-native auxiliary residual regularity -/

private theorem formNativeGravityConnectionDerivative_continuous
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
    (smooth.2.1 formDirection internalOut internalIn).continuous_fderiv
      (by simp)
  exact isBoundedBilinearMap_apply.continuous.comp
    (derivativeContinuous.prodMk continuous_const)

private theorem formNativeHolonomicGravityCurvature_continuous
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
    formNativeGravityConnectionDerivative_continuous configuration smooth
  have connectionContinuous : ∀
      (direction internalOut internalIn : LorentzianIndex),
      Continuous fun point =>
        configuration.gravityConnection point direction
          internalOut internalIn := fun direction internalOut internalIn =>
    (smooth.2.1 direction internalOut internalIn).continuous
  unfold holonomicGravityCurvature
  dsimp only
  fun_prop

private theorem formNativeGravityVarianceNormalization_apply_continuous
    (bivector : BasePoint → PhysicalBivector)
    (bivectorContinuous : Continuous bivector) :
    Continuous fun point =>
      gravityInternalPairVarianceNormalization (bivector point) :=
  gravityInternalPairVarianceNormalization.toLinearMap
    |>.continuous_of_finiteDimensional.comp bivectorContinuous

private theorem formNativeGravityInternalDual_apply_continuous
    (bivector : BasePoint → PhysicalBivector)
    (bivectorContinuous : Continuous bivector) :
    Continuous fun point => gravityInternalDualEquiv (bivector point) :=
  gravityInternalDualEquiv.toLinearMap
    |>.continuous_of_finiteDimensional.comp bivectorContinuous

/-- The `B` Euler residual of the new action is continuous after the raw
curvature has passed through the once-only variance normalization. -/
theorem holonomicFormNativeGravityAuxiliaryEulerResidual_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous
      (holonomicFormNativeGravityAuxiliaryEulerResidual configuration) := by
  have curvatureContinuous :=
    formNativeHolonomicGravityCurvature_continuous configuration smooth
  have normalizedCurvatureContinuous :=
    formNativeGravityVarianceNormalization_apply_continuous
      (holonomicGravityCurvature configuration) curvatureContinuous
  have auxiliaryContinuous :=
    formNativeHolonomicGravityAuxiliary_continuous configuration smooth
  have dualAuxiliaryContinuous :=
    formNativeGravityInternalDual_apply_continuous
      configuration.gravityAuxiliary auxiliaryContinuous
  have multiplierContinuous :=
    formNativeHolonomicGravityMultiplier_continuous configuration smooth
  unfold holonomicFormNativeGravityAuxiliaryEulerResidual
    formNativeGravityAuxiliaryEulerResidual toContinuumPointField
  exact (normalizedCurvatureContinuous.sub dualAuxiliaryContinuous).add
    multiplierContinuous

/-! ## Compact auxiliary coefficients -/

theorem holonomicFormNativeGravityAuxiliaryFirstVariationDensity_eq_pairing
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector)
    (point : BasePoint) :
    holonomicFormNativeGravityAuxiliaryFirstVariationDensity configuration
        variation point =
      gravityTopologicalWedgeCoefficient (variation point)
        (holonomicFormNativeGravityAuxiliaryEulerResidual configuration point) :=
  formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing
    (toContinuumPointField configuration point) (variation point)

theorem holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_eq_pairing
    (variation : BasePoint → PhysicalBivector)
    (point : BasePoint) :
    holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity variation
        point =
      -(1 / 2 : ℝ) *
        gravityTopologicalWedgeCoefficient (variation point)
          (gravityInternalDualEquiv (variation point)) :=
  rfl

theorem holonomicFormNativeGravityAuxiliaryFirstVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Continuous
      (holonomicFormNativeGravityAuxiliaryFirstVariationDensity configuration
        variation) := by
  rw [show holonomicFormNativeGravityAuxiliaryFirstVariationDensity
      configuration variation = fun point =>
        gravityTopologicalWedgeCoefficient (variation point)
          (holonomicFormNativeGravityAuxiliaryEulerResidual configuration point) by
    funext point
    exact holonomicFormNativeGravityAuxiliaryFirstVariationDensity_eq_pairing
      configuration variation point]
  exact gravityTopologicalWedgeCoefficient_apply_continuous variation
    (holonomicFormNativeGravityAuxiliaryEulerResidual configuration)
    variation.smooth.continuous
    (holonomicFormNativeGravityAuxiliaryEulerResidual_continuous
      configuration smooth)

theorem holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_continuous
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Continuous
      (holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
        variation) := by
  have variationContinuous : Continuous
      (variation : BasePoint → PhysicalBivector) :=
    variation.smooth.continuous
  have dualVariationContinuous :=
    formNativeGravityInternalDual_apply_continuous variation
      variationContinuous
  rw [show holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
      variation = fun point =>
        -(1 / 2 : ℝ) *
          gravityTopologicalWedgeCoefficient (variation point)
            (gravityInternalDualEquiv (variation point)) by
    funext point
    exact
      holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_eq_pairing
        variation point]
  exact continuous_const.mul
    (gravityTopologicalWedgeCoefficient_apply_continuous variation
      (fun point => gravityInternalDualEquiv (variation point))
      variationContinuous dualVariationContinuous)

theorem holonomicFormNativeGravityAuxiliaryFirstVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasCompactSupport
      (holonomicFormNativeGravityAuxiliaryFirstVariationDensity configuration
        variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  rw [holonomicFormNativeGravityAuxiliaryFirstVariationDensity_eq_pairing,
    variationZero]
  exact gravityTopologicalWedgeCoefficient_zero_left _

theorem holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_compact
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasCompactSupport
      (holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
        variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity,
    formNativeGravityAuxiliaryBFQuadraticCoefficientDensity, variationZero]

theorem holonomicFormNativeGravityAuxiliaryFirstVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Integrable
      (holonomicFormNativeGravityAuxiliaryFirstVariationDensity configuration
        variation) :=
  (holonomicFormNativeGravityAuxiliaryFirstVariationDensity_continuous
      configuration smooth variation).integrable_of_hasCompactSupport
    (holonomicFormNativeGravityAuxiliaryFirstVariationDensity_compact
      configuration variation)

theorem holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_integrable
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Integrable
      (holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
        variation) :=
  (holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_continuous
      variation).integrable_of_hasCompactSupport
    (holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity_compact
      variation)

/-! ## Integrated auxiliary polynomial and derivative -/

/-- The new form-native global action is genuinely quadratic along every
compactly supported primitive `B` path. -/
theorem holonomicFormNativeIntegratedAction_auxiliary_quadratic
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    holonomicFormNativeIntegratedUnifiedAction source chart
        (varyFormNativeGravityAuxiliary configuration variation parameter) =
      holonomicFormNativeIntegratedUnifiedAction source chart configuration +
        parameter *
          (∫ point : BasePoint,
            holonomicFormNativeGravityAuxiliaryFirstVariationDensity
              configuration variation point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
              variation point) := by
  unfold holonomicFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedFormNativeUnifiedAction
    integratedFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise :
      (fun point : BasePoint =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField
            (varyFormNativeGravityAuxiliary configuration variation parameter)
            point)) =
      fun point =>
        generatedFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          holonomicFormNativeGravityAuxiliaryFirstVariationDensity
            configuration variation point +
        parameter ^ 2 *
          holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
            variation point := by
    funext point
    exact holonomicFormNativeLocalDensity_auxiliary_quadratic source
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
      generatedFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField configuration point)) at densityIntegrable
  calc
    (∫ point : BasePoint,
        generatedFormNativeUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) chart point
              (toContinuumPointField configuration point) +
            parameter *
              holonomicFormNativeGravityAuxiliaryFirstVariationDensity
                configuration variation point +
          parameter ^ 2 *
            holonomicFormNativeGravityAuxiliaryQuadraticCoefficientDensity
              variation point) =
      (∫ point : BasePoint,
          generatedFormNativeUnifiedLocalDensityAtBoundary source
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
          generatedFormNativeUnifiedLocalDensityAtBoundary source
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

theorem holonomicFormNativeIntegratedAction_auxiliary_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
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
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityAuxiliary configuration variation parameter)) =
      fun parameter =>
        holonomicFormNativeIntegratedUnifiedAction source chart configuration +
          parameter * firstIntegral + parameter ^ 2 * quadraticIntegral := by
    funext parameter
    exact holonomicFormNativeIntegratedAction_auxiliary_quadratic source chart
      configuration smooth densityIntegrable variation parameter
  rw [formula]
  change HasDerivAt
    ((fun parameter =>
      holonomicFormNativeIntegratedUnifiedAction source chart configuration +
        parameter * firstIntegral) +
      fun parameter => parameter ^ 2 * quadraticIntegral)
    firstIntegral 0
  simpa using
    ((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstIntegral).const_add
      (holonomicFormNativeIntegratedUnifiedAction source chart configuration)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const
        quadraticIntegral))

/-! ## Auxiliary stationarity, unique reaction, and joint checkpoint -/

def FormNativeGravityAuxiliaryActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    HasDerivAt
      (fun parameter : ℝ =>
        holonomicFormNativeIntegratedUnifiedAction source chart
          (varyFormNativeGravityAuxiliary configuration variation parameter))
      0 0

def FormNativeGravityAuxiliaryWeakEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  TopologicalGravityWeakEquation
    (holonomicFormNativeGravityAuxiliaryEulerResidual configuration)

def FormNativeGravityAuxiliaryEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  holonomicFormNativeGravityAuxiliaryEulerResidual configuration = 0

/-- Source-free, action-derived reaction normal form computed from the
holonomic curvature generated by the live primitive gravity connection and
the gravity auxiliary field.  It is a readout of the `B` Euler zero fiber,
not a separately produced stationary actual. -/
def formNativeGravityReactionField
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint → PhysicalBivector := fun point =>
  gravityInternalDualEquiv (configuration.gravityAuxiliary point) -
    holonomicContravariantGravityCurvature configuration point

theorem formNativeGravityAuxiliaryActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    FormNativeGravityAuxiliaryActionStationary source chart configuration ↔
      FormNativeGravityAuxiliaryWeakEquation configuration := by
  constructor
  · intro stationary variation
    have actual := holonomicFormNativeIntegratedAction_auxiliary_hasDerivAt
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
    have actual := holonomicFormNativeIntegratedAction_auxiliary_hasDerivAt
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

theorem formNativeGravityAuxiliaryWeakEquation_iff_equation
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    FormNativeGravityAuxiliaryWeakEquation configuration ↔
      FormNativeGravityAuxiliaryEquation configuration :=
  topologicalGravityWeakEquation_iff_residual_eq_zero _
    (holonomicFormNativeGravityAuxiliaryEulerResidual_continuous
      configuration smooth)

theorem formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
    (configuration : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation configuration ↔
      configuration.gravitySimplicityMultiplier =
        formNativeGravityReactionField configuration := by
  constructor
  · intro equation
    funext point
    apply (formNativeGravityAuxiliaryEulerResidual_eq_zero_iff_reaction
      (toContinuumPointField configuration point)).mp
    exact congrFun equation point
  · intro reaction
    funext point
    apply (formNativeGravityAuxiliaryEulerResidual_eq_zero_iff_reaction
      (toContinuumPointField configuration point)).mpr
    exact congrFun reaction point

/-- Compact-support `B` stationarity reads exactly the unique, source-free
reaction generated by the same form-native action. -/
theorem formNativeGravityAuxiliaryActionStationary_iff_reaction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    FormNativeGravityAuxiliaryActionStationary source chart configuration ↔
      configuration.gravitySimplicityMultiplier =
        formNativeGravityReactionField configuration := by
  rw [formNativeGravityAuxiliaryActionStationary_iff_weakEquation source chart
    configuration smooth densityIntegrable]
  rw [formNativeGravityAuxiliaryWeakEquation_iff_equation configuration smooth]
  exact formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
    configuration

/-- Same-action checkpoint for the two algebraic gravity legs.  It is not a
claim about the still-open coframe or Lorentz-connection equations. -/
theorem formNativeGravityMultiplierAndAuxiliaryActionStationary_iff
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : FormNativeHolonomicLocalDensityIntegrable
      source chart configuration) :
    (FormNativeGravityMultiplierActionStationary source chart configuration ∧
      FormNativeGravityAuxiliaryActionStationary source chart configuration) ↔
      (FormNativeGravitySimplicityEquation configuration ∧
        configuration.gravitySimplicityMultiplier =
          formNativeGravityReactionField configuration) := by
  rw [formNativeGravityMultiplierActionStationary_iff_simplicity source chart
    configuration smooth densityIntegrable]
  rw [formNativeGravityAuxiliaryActionStationary_iff_reaction source chart
    configuration smooth densityIntegrable]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
