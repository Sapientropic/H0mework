import H0mework.Physics.Geometry.FundamentalLemma

namespace SaturationMonoid.PhysicsCore.StageNinePlebanskiMultiplierVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineFundamentalLemma
open EmpiricalReferenceScaleCouplingBoundary
open MeasureTheory
open scoped ContDiff

noncomputable section

def withGravitySimplicityMultiplier
    (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) : StageNineContinuumPointField :=
  { field with gravitySimplicityMultiplier := multiplier }

theorem gravityCoordinatePairing_add_left
    (first second residual : PhysicalBivector) :
    gravityCoordinatePairing (first + second) residual =
      gravityCoordinatePairing first residual +
        gravityCoordinatePairing second residual := by
  unfold gravityCoordinatePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  simp only [Pi.add_apply]
  ring

theorem gravityCoordinatePairing_smul_left
    (parameter : ℝ) (variation residual : PhysicalBivector) :
    gravityCoordinatePairing (parameter • variation) residual =
      parameter * gravityCoordinatePairing variation residual := by
  unfold gravityCoordinatePairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem gravitySimplicityMultiplierPairing_add_left
    (first second residual : PhysicalBivector) :
    gravitySimplicityMultiplierPairing (first + second) residual =
      gravitySimplicityMultiplierPairing first residual +
        gravitySimplicityMultiplierPairing second residual := by
  unfold gravitySimplicityMultiplierPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  simp only [Pi.add_apply]
  ring

theorem gravitySimplicityMultiplierPairing_smul_left
    (parameter : ℝ) (variation residual : PhysicalBivector) :
    gravitySimplicityMultiplierPairing (parameter • variation) residual =
      parameter * gravitySimplicityMultiplierPairing variation residual := by
  unfold gravitySimplicityMultiplierPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internalPair _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spacetimePair _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem generatedGravitySimplicityDensity_affine
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedGravitySimplicityDensity
        (withGravitySimplicityMultiplier field
          (field.gravitySimplicityMultiplier + parameter • variation)) =
      generatedGravitySimplicityDensity field +
        parameter * gravitySimplicityMultiplierPairing variation
          (generatedGravitySimplicityResidual field) := by
  rw [generatedGravitySimplicityDensity,
    generatedGravitySimplicityDensity]
  change gravitySimplicityMultiplierPairing
      (field.gravitySimplicityMultiplier + parameter • variation)
        (generatedGravitySimplicityResidual field) = _
  rw [gravitySimplicityMultiplierPairing_add_left,
    gravitySimplicityMultiplierPairing_smul_left]

@[simp] theorem generatedVolumeDensity_withGravitySimplicityMultiplier
    (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) :
    generatedVolumeDensity
        (withGravitySimplicityMultiplier field multiplier) =
      generatedVolumeDensity field := by
  rfl

@[simp] theorem generatedUnifiedLocalDensityCore_withGravitySimplicityMultiplier
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (multiplier : PhysicalBivector) :
    generatedUnifiedLocalDensityCoreAtBoundary source boundary chart point
        (withGravitySimplicityMultiplier field multiplier) =
      generatedUnifiedLocalDensityCoreAtBoundary source boundary chart point
        field := by
  rfl

theorem generatedUnifiedLocalDensity_multiplier_affine
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : PhysicalBivector) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source boundary chart point
        (withGravitySimplicityMultiplier field
          (field.gravitySimplicityMultiplier + parameter • variation)) =
      generatedUnifiedLocalDensityAtBoundary source boundary chart point field +
        parameter * generatedVolumeDensity field *
          gravitySimplicityMultiplierPairing variation
            (generatedGravitySimplicityResidual field) := by
  unfold generatedUnifiedLocalDensityAtBoundary
  rw [generatedGravitySimplicityDensity_affine]
  rw [generatedVolumeDensity_withGravitySimplicityMultiplier,
    generatedUnifiedLocalDensityCore_withGravitySimplicityMultiplier]
  ring

def varyGravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravitySimplicityMultiplier := fun point =>
      configuration.gravitySimplicityMultiplier point +
        parameter • variation point }

theorem toContinuumPointField_varyGravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ)
    (point : BasePoint) :
    toContinuumPointField
        (varyGravitySimplicityMultiplier configuration variation parameter) point =
      withGravitySimplicityMultiplier (toContinuumPointField configuration point)
        (configuration.gravitySimplicityMultiplier point +
          parameter • variation point) := by
  rfl

def gravitySimplicityMultiplierFirstVariationDensity
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    gravitySimplicityMultiplierPairing (variation point)
      (generatedGravitySimplicityResidual
        (toContinuumPointField configuration point))

theorem holonomicLocalDensity_multiplier_affine
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → PhysicalBivector) (parameter : ℝ) :
    generatedUnifiedLocalDensityAtBoundary source boundary chart point
        (toContinuumPointField
          (varyGravitySimplicityMultiplier configuration variation parameter)
          point) =
      generatedUnifiedLocalDensityAtBoundary source boundary chart point
          (toContinuumPointField configuration point) +
        parameter *
          gravitySimplicityMultiplierFirstVariationDensity
            configuration variation point := by
  rw [toContinuumPointField_varyGravitySimplicityMultiplier]
  simpa only [gravitySimplicityMultiplierFirstVariationDensity,
    toContinuumPointField, mul_assoc] using
      generatedUnifiedLocalDensity_multiplier_affine
        source boundary chart point (toContinuumPointField configuration point)
          (variation point) parameter

theorem holonomicCoframe_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.coframe := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact (smooth.1 row column).continuous

theorem holonomicGravityAuxiliary_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous configuration.gravityAuxiliary := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro spacetimePair
  exact (smooth.2.2.1 internalPair spacetimePair).continuous

theorem physicalIIPlus_component_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (internalPair spacetimePair : Fin 6) :
    Continuous fun point =>
      physicalIIPlusBivector (configuration.coframe point)
        internalPair spacetimePair := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  unfold physicalIIPlusBivector internalBivectorDual coframeWedge
  fun_prop

theorem generatedGravitySimplicityResidual_component_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (internalPair spacetimePair : Fin 6) :
    Continuous fun point =>
      generatedGravitySimplicityResidual
        (toContinuumPointField configuration point)
          internalPair spacetimePair := by
  exact
    ((continuous_apply spacetimePair).comp
      ((continuous_apply internalPair).comp
        (holonomicGravityAuxiliary_continuous configuration smooth))).sub
        (physicalIIPlus_component_continuous configuration smooth
          internalPair spacetimePair)

theorem gravitySimplicityMultiplierFirstVariationDensity_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Continuous
      (gravitySimplicityMultiplierFirstVariationDensity configuration variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) := by
    exact coframeContinuous.matrix_det.abs
  apply volumeContinuous.mul
  unfold gravitySimplicityMultiplierPairing
  apply continuous_finsetSum
  intro internalPair _
  apply continuous_finsetSum
  intro spacetimePair _
  have variationContinuous : Continuous fun point =>
      variation point internalPair spacetimePair :=
    (continuous_apply spacetimePair).comp
      ((continuous_apply internalPair).comp variation.smooth.continuous)
  have residualContinuous :=
    generatedGravitySimplicityResidual_component_continuous
      configuration smooth internalPair spacetimePair
  fun_prop

theorem gravitySimplicityMultiplierFirstVariationDensity_compact
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasCompactSupport
      (gravitySimplicityMultiplierFirstVariationDensity configuration variation) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  simp [gravitySimplicityMultiplierFirstVariationDensity,
    gravitySimplicityMultiplierPairing, variationZero]

theorem gravitySimplicityMultiplierFirstVariationDensity_integrable
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    Integrable
      (gravitySimplicityMultiplierFirstVariationDensity configuration variation) :=
  (gravitySimplicityMultiplierFirstVariationDensity_continuous
      configuration smooth variation).integrable_of_hasCompactSupport
    (gravitySimplicityMultiplierFirstVariationDensity_compact
      configuration variation)

theorem holonomicIntegratedUnifiedAction_multiplier_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : HolonomicLocalDensityIntegrable source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source chart
        (varyGravitySimplicityMultiplier configuration variation parameter) =
      holonomicIntegratedUnifiedAction source chart configuration +
        parameter *
          ∫ point : BasePoint,
            gravitySimplicityMultiplierFirstVariationDensity
              configuration variation point := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (varyGravitySimplicityMultiplier configuration variation parameter)
          point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) chart point
          (toContinuumPointField configuration point) +
        parameter *
          gravitySimplicityMultiplierFirstVariationDensity
            configuration variation point := by
    funext point
    exact holonomicLocalDensity_multiplier_affine source
      (sourceGeneratedUnifiedCouplings source) chart point configuration
        variation parameter
  rw [pointwise]
  rw [integral_add densityIntegrable
    ((gravitySimplicityMultiplierFirstVariationDensity_integrable
      configuration smooth variation).const_mul parameter)]
  rw [integral_const_mul]

theorem holonomicIntegratedUnifiedAction_multiplier_hasDerivAt
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : HolonomicLocalDensityIntegrable source chart configuration)
    (variation : CompactlySupportedSmoothVariation PhysicalBivector) :
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyGravitySimplicityMultiplier configuration variation parameter))
      (∫ point : BasePoint,
        gravitySimplicityMultiplierFirstVariationDensity
          configuration variation point) 0 := by
  let coefficient := ∫ point : BasePoint,
    gravitySimplicityMultiplierFirstVariationDensity
      configuration variation point
  have actionEquality :
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyGravitySimplicityMultiplier configuration variation parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source chart configuration +
          parameter * coefficient := by
    funext parameter
    exact holonomicIntegratedUnifiedAction_multiplier_affine source chart
      configuration smooth densityIntegrable variation parameter
  rw [actionEquality]
  simpa [coefficient] using
    ((hasDerivAt_id (x := 0)).mul_const coefficient).const_add
      (holonomicIntegratedUnifiedAction source chart configuration)

def GravitySimplicityMultiplierActionStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    HasDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source chart
        (varyGravitySimplicityMultiplier configuration variation parameter))
      0 0

def GravitySimplicityMultiplierWeakEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation PhysicalBivector,
    (∫ point : BasePoint,
      gravitySimplicityMultiplierFirstVariationDensity
        configuration variation point) = 0

theorem gravitySimplicityMultiplierActionStationary_implies_weakEquation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (densityIntegrable : HolonomicLocalDensityIntegrable source chart configuration)
    (stationary : GravitySimplicityMultiplierActionStationary
      source chart configuration) :
    GravitySimplicityMultiplierWeakEquation configuration := by
  intro variation
  have actual := holonomicIntegratedUnifiedAction_multiplier_hasDerivAt
    source chart configuration smooth densityIntegrable variation
  exact ((stationary variation).unique actual).symm

def singlePhysicalBivectorVariation
    (internalPair spacetimePair : Fin 6)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    CompactlySupportedSmoothVariation PhysicalBivector where
  toFun := fun point candidateInternal candidateSpacetime =>
    if candidateInternal = internalPair then
      if candidateSpacetime = spacetimePair then variation point else 0
    else 0
  smooth := by
    apply contDiff_pi'
    intro candidateInternal
    apply contDiff_pi'
    intro candidateSpacetime
    by_cases internalEquality : candidateInternal = internalPair
    · by_cases spacetimeEquality : candidateSpacetime = spacetimePair
      · simpa [internalEquality, spacetimeEquality] using variation.smooth
      · simpa [internalEquality, spacetimeEquality] using
          (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint => (0 : ℝ)))
    · simpa [internalEquality] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint => (0 : ℝ)))
  compactSupport := by
    have variationCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
    filter_upwards [variationCompact] with point variationZero
    funext candidateInternal candidateSpacetime
    simp [variationZero]

theorem gravitySimplicityMultiplierPairing_singlePhysicalBivectorVariation
    (internalPair spacetimePair : Fin 6)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) (residual : PhysicalBivector) :
    gravitySimplicityMultiplierPairing
        (singlePhysicalBivectorVariation
          internalPair spacetimePair variation point) residual =
      variation point * residual internalPair spacetimePair ^ 2 := by
  simp [gravitySimplicityMultiplierPairing,
    singlePhysicalBivectorVariation]

def gravitySimplicityCoordinateCoefficient
    (configuration : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6) (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (generatedGravitySimplicityResidual
        (toContinuumPointField configuration point)
          internalPair spacetimePair) ^ 2

theorem gravitySimplicityFirstVariationDensity_single
    (configuration : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    gravitySimplicityMultiplierFirstVariationDensity configuration
        (singlePhysicalBivectorVariation
          internalPair spacetimePair variation) point =
      variation point *
        gravitySimplicityCoordinateCoefficient configuration
          internalPair spacetimePair point := by
  rw [gravitySimplicityMultiplierFirstVariationDensity,
    gravitySimplicityMultiplierPairing_singlePhysicalBivectorVariation]
  unfold gravitySimplicityCoordinateCoefficient
  ring

theorem gravitySimplicityCoordinateCoefficient_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (internalPair spacetimePair : Fin 6) :
    Continuous
      (gravitySimplicityCoordinateCoefficient configuration
        internalPair spacetimePair) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) := by
    exact coframeContinuous.matrix_det.abs
  have residualContinuous :=
    generatedGravitySimplicityResidual_component_continuous
      configuration smooth internalPair spacetimePair
  unfold gravitySimplicityCoordinateCoefficient
  fun_prop

theorem gravitySimplicityMultiplierWeakEquation_coordinate_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (weakEquation : GravitySimplicityMultiplierWeakEquation configuration)
    (internalPair spacetimePair : Fin 6) :
    gravitySimplicityCoordinateCoefficient configuration
        internalPair spacetimePair = 0 := by
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (gravitySimplicityCoordinateCoefficient configuration
      internalPair spacetimePair)
    (gravitySimplicityCoordinateCoefficient_continuous
      configuration smooth internalPair spacetimePair)
  intro variation
  have weakCoordinate := weakEquation
    (singlePhysicalBivectorVariation
      internalPair spacetimePair variation)
  have integrandEquality :
      (fun point : BasePoint =>
        gravitySimplicityMultiplierFirstVariationDensity configuration
          (singlePhysicalBivectorVariation
            internalPair spacetimePair variation) point) =
      fun point => variation point *
        gravitySimplicityCoordinateCoefficient configuration
          internalPair spacetimePair point := by
    funext point
    exact gravitySimplicityFirstVariationDensity_single configuration
      internalPair spacetimePair variation point
  rw [integrandEquality] at weakCoordinate
  exact weakCoordinate

def GravitySimplicityEquation
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point,
    configuration.gravityAuxiliary point =
      physicalIIPlusBivector (configuration.coframe point)

theorem gravitySimplicityMultiplierWeakEquation_implies_simplicity
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation : GravitySimplicityMultiplierWeakEquation configuration) :
    GravitySimplicityEquation configuration := by
  intro point
  funext internalPair spacetimePair
  have coefficientZero := congrFun
    (gravitySimplicityMultiplierWeakEquation_coordinate_zero
      configuration smooth weakEquation internalPair spacetimePair) point
  have coefficientZeroScalar :
      gravitySimplicityCoordinateCoefficient configuration
        internalPair spacetimePair point = 0 := by
    simpa using coefficientZero
  have volumeNonzero :
      generatedVolumeDensity (toContinuumPointField configuration point) ≠ 0 := by
    simp only [generatedVolumeDensity, toContinuumPointField]
    exact abs_ne_zero.mpr (nondegenerate point)
  have residualZero :
      generatedGravitySimplicityResidual
        (toContinuumPointField configuration point)
          internalPair spacetimePair = 0 := by
    have squareZero :
        (generatedGravitySimplicityResidual
            (toContinuumPointField configuration point)
              internalPair spacetimePair) ^ 2 = 0 := by
      exact (mul_eq_zero.mp (by
        simpa only [gravitySimplicityCoordinateCoefficient] using
          coefficientZeroScalar)).resolve_left volumeNonzero
    exact sq_eq_zero_iff.mp squareZero
  simpa only [generatedGravitySimplicityResidual,
    toContinuumPointField, Pi.sub_apply, sub_eq_zero] using residualZero

theorem gravitySimplicityMultiplierActionStationary_implies_simplicity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source chart configuration)
    (stationary : GravitySimplicityMultiplierActionStationary
      source chart configuration) :
    GravitySimplicityEquation configuration :=
  gravitySimplicityMultiplierWeakEquation_implies_simplicity configuration
    smooth nondegenerate
    (gravitySimplicityMultiplierActionStationary_implies_weakEquation
      source chart configuration smooth densityIntegrable stationary)

def installGravitySimplicity
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityAuxiliary := physicalIIPlusBivector field.coframe }

@[simp] theorem installGravitySimplicity_residual_zero
    (field : StageNineContinuumPointField) :
    generatedGravitySimplicityResidual (installGravitySimplicity field) = 0 := by
  simp [generatedGravitySimplicityResidual, installGravitySimplicity]

def zeroAuxiliaryIdentityCoframeFake
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with coframe := 1, gravityAuxiliary := 0 }

/-- Negative regression: the previously convenient zero-B vacuum cannot pass
the dynamical Plebanski multiplier equation on a nondegenerate identity
coframe. -/
theorem zeroAuxiliaryIdentityCoframeFake_rejected
    (field : StageNineContinuumPointField) :
    generatedGravitySimplicityResidual
      (zeroAuxiliaryIdentityCoframeFake field) ≠ 0 := by
  intro residualZero
  have componentZero := congrFun (congrFun residualZero 3) 0
  norm_num [generatedGravitySimplicityResidual,
    zeroAuxiliaryIdentityCoframeFake] at componentZero

end

end SaturationMonoid.PhysicsCore.StageNinePlebanskiMultiplierVariation
