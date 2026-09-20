import H0mework.Physics.DualVariation.MotherAction
import H0mework.Physics.Matter.ConjugateMatterVariation

/-!
# Dirac-dual form-native conjugate-matter variation

This module starts the semantic EL migration for the repaired action hash.
The primitive conjugate-matter path and its full coordinate-dual coverage are
reused, but the first coefficient is derived again from the new complete
forward vector

```text
Dirac kinetic + repaired Dirac-dual Yukawa.
```

No historical action derivative, field equation, stationarity receipt, or
supplied vector is accepted at the theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConjugateMatterVariation

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineConjugateMatterVariation
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
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterFullVariations
open MeasureTheory

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Continuity of the repaired complete forward vector -/

theorem diracDualRightChiralYukawaAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    diracDualRightChiralYukawaAction (first + second) =
      diracDualRightChiralYukawaAction first +
        diracDualRightChiralYukawaAction second := by
  apply LinearMap.ext
  intro field
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  exact LinearMap.congr_fun
    (diracExteriorYukawaInternalAction_add first second)
    (diracMatrixMatterAction
      DiracCliffordRepresentation.rightChiralityProjector field)

theorem diracDualRightChiralYukawaAction_smul
    (coefficient : ℂ)
    (scalar : ExteriorBreakingScalarCarrier) :
    diracDualRightChiralYukawaAction (coefficient • scalar) =
      coefficient • diracDualRightChiralYukawaAction scalar := by
  apply LinearMap.ext
  intro field
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  exact LinearMap.congr_fun
    (diracExteriorYukawaInternalAction_smul coefficient scalar)
    (diracMatrixMatterAction
      DiracCliffordRepresentation.rightChiralityProjector field)

/-- Coordinate bilinear map for the repaired right-chiral Yukawa operator. -/
def diracDualYukawaCoordinateBilinear :
    ScalarCoordinateCarrier →ₗ[ℂ]
      MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier where
  toFun scalar :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        rw [matterCoordinateEquiv.symm.map_add,
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)).map_add,
          matterCoordinateEquiv.map_add]
      map_smul' := by
        intro parameter matter
        rw [matterCoordinateEquiv.symm.map_smul,
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)).map_smul,
          matterCoordinateEquiv.map_smul]
        rfl }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (first + second))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm first)
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm second)
              (matterCoordinateEquiv.symm matter))
    have operatorEquality := LinearMap.congr_fun
      (diracDualRightChiralYukawaAction_add
        (scalarCoordinateEquiv.symm first)
        (scalarCoordinateEquiv.symm second))
      (matterCoordinateEquiv.symm matter)
    calc
      _ = matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm first +
              scalarCoordinateEquiv.symm second)
            (matterCoordinateEquiv.symm matter)) := by
              rw [scalarCoordinateEquiv.symm.map_add]
      _ = matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm first)
              (matterCoordinateEquiv.symm matter) +
            diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm second)
              (matterCoordinateEquiv.symm matter)) :=
            congrArg matterCoordinateEquiv operatorEquality
      _ = _ := matterCoordinateEquiv.map_add _ _
  map_smul' := by
    intro parameter scalar
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (parameter • scalar))
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm scalar)
              (matterCoordinateEquiv.symm matter))
    have operatorEquality := LinearMap.congr_fun
      (diracDualRightChiralYukawaAction_smul parameter
        (scalarCoordinateEquiv.symm scalar))
      (matterCoordinateEquiv.symm matter)
    calc
      _ = matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (parameter • scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter)) := by
              rw [scalarCoordinateEquiv.symm.map_smul]
      _ = matterCoordinateEquiv
          (parameter •
            diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm scalar)
              (matterCoordinateEquiv.symm matter)) :=
            congrArg matterCoordinateEquiv operatorEquality
      _ = _ := matterCoordinateEquiv.map_smul _ _

theorem diracDualYukawaCoordinate_apply_continuous
    (scalar : BasePoint → ScalarCoordinateCarrier)
    (matter : BasePoint → MatterCoordinateCarrier)
    (scalarContinuous : Continuous scalar)
    (matterContinuous : Continuous matter) :
    Continuous fun point =>
      diracDualYukawaCoordinateBilinear (scalar point) (matter point) := by
  exact
    (diracDualYukawaCoordinateBilinear.toContinuousBilinearMap.continuous.comp
      scalarContinuous).clm_apply matterContinuous

theorem holonomicDiracDualYukawaVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    Continuous fun point =>
      matterCoordinateEquiv
        (generatedContinuumDiracDualYukawaVector
          source 0 point
          (toContinuumPointField configuration point)) := by
  have actual := diracDualYukawaCoordinate_apply_continuous
    configuration.scalar
    (fun point => matterCoordinateEquiv (configuration.matter point))
    smooth.2.2.2.2.2.2.1.continuous
    smooth.2.2.2.2.2.2.2.1.continuous
  exact actual.congr fun point => by
    unfold generatedContinuumDiracDualYukawaVector
    simp only [toContinuumPointField,
      scalarFrameRelativeCoordinates_zeroChart,
      matterFrameRelative_zeroChart]
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem holonomicMatterKineticVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      matterCoordinateEquiv
        (generatedContinuumMatterKineticVector source 0 point
          (toContinuumPointField configuration point)) := by
  have kineticSumContinuous :=
    holonomicMatterKineticSum_coordinate_continuous source configuration smooth
      nondegenerate
  have withIContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (holonomicMatterCovariantDerivative configuration point)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticSumContinuous).congr fun _ => rfl
  unfold generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
  exact withIContinuous.congr fun point => by
    rw [map_smul]
    rfl

theorem holonomicGeneratedContinuumDiracDualMatterVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      matterCoordinateEquiv
        (generatedContinuumDiracDualMatterVector source 0 point
          (toContinuumPointField configuration point)) := by
  have kineticContinuous := holonomicMatterKineticVector_coordinate_continuous
    source configuration smooth nondegenerate
  have yukawaContinuous : Continuous fun point =>
      matterCoordinateEquiv
        (generatedContinuumDiracDualYukawaVector source 0 point
          (toContinuumPointField configuration point)) := by
    exact holonomicDiracDualYukawaVector_coordinate_continuous source
      configuration smooth
  exact (kineticContinuous.add yukawaContinuous).congr fun point => by
    change
      matterCoordinateEquiv
          (generatedContinuumMatterKineticVector source 0 point
            (toContinuumPointField configuration point)) +
        matterCoordinateEquiv
          (generatedContinuumDiracDualYukawaVector source 0 point
            (toContinuumPointField configuration point)) =
      matterCoordinateEquiv
        (generatedContinuumDiracDualMatterVector source 0 point
          (toContinuumPointField configuration point))
    rw [← map_add]
    rfl

/-! ## Repaired local affine law and analytic coefficient -/

/-- First coefficient generated by the repaired complete forward vector. -/
def diracDualConjugateMatterFirstVariationDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (matterDualOfCoordinates (variation point)
      (generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField configuration point))).re

theorem
    generatedDensitizedContinuumDiracDualMatterDensity_withConjugateMatter_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : MatterCoordinateCarrier)
    (parameter : ℝ) :
    generatedDensitizedContinuumDiracDualMatterDensity source 0 point
        (withConjugateMatter field
          (field.conjugateMatter +
            parameter • matterDualOfCoordinates variation)) =
      generatedDensitizedContinuumDiracDualMatterDensity source 0 point field +
        parameter *
          (generatedVolumeDensity field *
            (matterDualOfCoordinates variation
              (generatedContinuumDiracDualMatterVector source 0 point
                field)).re) := by
  have vectorUnchanged :
      generatedContinuumDiracDualMatterVector source 0 point
          (withConjugateMatter field
            (field.conjugateMatter +
              parameter • matterDualOfCoordinates variation)) =
        generatedContinuumDiracDualMatterVector source 0 point field :=
    rfl
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing,
    vectorUnchanged]
  simp only [withConjugateMatter, generatedVolumeDensity,
    matterDualFrameRelative_zeroChart, LinearMap.add_apply,
    LinearMap.smul_apply, Complex.add_re]
  simp [Complex.mul_re]
  ring

/-- The new local root is exactly affine along the primitive independent-dual
path, with the repaired complete vector as its coefficient. -/
theorem generatedDiracDualFormNativeUnifiedLocalDensity_withConjugateMatter_affine
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (variation : MatterCoordinateCarrier)
    (parameter : ℝ) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withConjugateMatter field
          (field.conjugateMatter +
            parameter • matterDualOfCoordinates variation)) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point field +
        parameter *
          (generatedVolumeDensity field *
            (matterDualOfCoordinates variation
              (generatedContinuumDiracDualMatterVector source 0 point
                field)).re) := by
  let variedField := withConjugateMatter field
    (field.conjugateMatter +
      parameter • matterDualOfCoordinates variation)
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
    generatedDensitizedContinuumDiracDualMatterDensity_withConjugateMatter_affine]
  ring

theorem holonomicDiracDualFormNativeLocalDensity_conjugateMatter_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (varyConjugateMatterCoordinates configuration variation parameter)
          point) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField configuration point) +
        parameter *
          diracDualConjugateMatterFirstVariationDensity source configuration
            variation point := by
  unfold sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    diracDualConjugateMatterFirstVariationDensity
  rw [toContinuumPointField_varyConjugateMatterCoordinates]
  exact
    generatedDiracDualFormNativeUnifiedLocalDensity_withConjugateMatter_affine
      source point (toContinuumPointField configuration point)
      (variation point) parameter

theorem diracDualConjugateMatterFirstVariationDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Continuous
      (diracDualConjugateMatterFirstVariationDensity source configuration
        variation) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have vectorContinuous :=
    holonomicGeneratedContinuumDiracDualMatterVector_coordinate_continuous
      source configuration smooth nondegenerate
  have variationContinuous : Continuous
      (variation : BasePoint → MatterCoordinateCarrier) :=
    variation.smooth.continuous
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (generatedContinuumDiracDualMatterVector source 0 point
              (toContinuumPointField configuration point)) index *
          variation point index := by
    apply continuous_finsetSum
    intro index _
    have vectorCoordinateContinuous : Continuous fun point =>
        matterCoordinateEquiv
          (generatedContinuumDiracDualMatterVector source 0 point
            (toContinuumPointField configuration point)) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp vectorContinuous
    have variationCoordinateContinuous : Continuous fun point =>
        variation point index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          variationContinuous
    exact vectorCoordinateContinuous.mul variationCoordinateContinuous
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold diracDualConjugateMatterFirstVariationDensity
  simp_rw [matterDualOfCoordinates_apply]
  exact volumeContinuous.mul realPairingContinuous

theorem diracDualConjugateMatterFirstVariationDensity_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (variationZero : variation point = 0) :
    diracDualConjugateMatterFirstVariationDensity source configuration
        variation point = 0 := by
  simp [diracDualConjugateMatterFirstVariationDensity, variationZero]

theorem diracDualConjugateMatterFirstVariationDensity_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    HasCompactSupport
      (diracDualConjugateMatterFirstVariationDensity source configuration
        variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have variationEventually := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationEventually
  filter_upwards [variationEventually] with point variationZero
  exact diracDualConjugateMatterFirstVariationDensity_eq_zero source
    configuration variation point variationZero

theorem diracDualConjugateMatterFirstVariationDensity_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    Integrable
      (diracDualConjugateMatterFirstVariationDensity source configuration
        variation) :=
  (diracDualConjugateMatterFirstVariationDensity_continuous source
    configuration smooth nondegenerate variation).integrable_of_hasCompactSupport
      (diracDualConjugateMatterFirstVariationDensity_compact source
        configuration variation)

/-! ## Integrated derivative and faithful zero fiber -/

theorem
    holonomicDiracDualFormNativeIntegratedUnifiedAction_conjugateMatter_affine
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier)
    (parameter : ℝ) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        (varyConjugateMatterCoordinates configuration variation parameter) =
      holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          configuration +
        parameter *
          (∫ point : BasePoint,
            diracDualConjugateMatterFirstVariationDensity source configuration
              variation point) := by
  unfold holonomicDiracDualFormNativeIntegratedUnifiedAction
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    integratedDiracDualFormNativeUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyConjugateMatterCoordinates configuration variation parameter)
          point)) =
      fun point =>
        generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        parameter *
          diracDualConjugateMatterFirstVariationDensity source configuration
            variation point := by
    funext point
    exact holonomicDiracDualFormNativeLocalDensity_conjugateMatter_affine
      source configuration variation parameter point
  rw [pointwise]
  have baseIntegrable : Integrable fun point : BasePoint =>
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField configuration point) := by
    simpa [DiracDualFormNativeHolonomicLocalDensityIntegrable,
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity] using
        densityIntegrable
  have firstIntegrable :=
    diracDualConjugateMatterFirstVariationDensity_integrable source
      configuration smooth nondegenerate variation
  rw [integral_add baseIntegrable
    (firstIntegrable.const_mul parameter), integral_const_mul]

theorem
    holonomicDiracDualFormNativeIntegratedUnifiedAction_conjugateMatter_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier) :
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyConjugateMatterCoordinates configuration variation parameter))
      (∫ point : BasePoint,
        diracDualConjugateMatterFirstVariationDensity source configuration
          variation point) 0 := by
  let firstIntegral := ∫ point : BasePoint,
    diracDualConjugateMatterFirstVariationDensity source configuration
      variation point
  have actionEquality :
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyConjugateMatterCoordinates configuration variation parameter)) =
      fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
            configuration +
          parameter * firstIntegral := by
    funext parameter
    exact
      holonomicDiracDualFormNativeIntegratedUnifiedAction_conjugateMatter_affine
        source configuration smooth nondegenerate densityIntegrable variation
        parameter
  rw [actionEquality]
  simpa using
    ((hasDerivAt_id (x := 0)).mul_const firstIntegral).const_add
      (holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
        configuration)

def DiracDualFormNativeConjugateMatterActionStationary
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier,
    HasDerivAt
      (fun parameter =>
        holonomicDiracDualFormNativeIntegratedUnifiedAction source 0
          (varyConjugateMatterCoordinates configuration variation parameter))
      0 0

def DiracDualFormNativeConjugateMatterWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation MatterCoordinateCarrier,
    (∫ point : BasePoint,
      diracDualConjugateMatterFirstVariationDensity source configuration
        variation point) = 0

theorem
    diracDualFormNativeConjugateMatterActionStationary_iff_weakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration) :
    DiracDualFormNativeConjugateMatterActionStationary source configuration ↔
      DiracDualFormNativeConjugateMatterWeakEquation source configuration := by
  constructor
  · intro stationary variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_conjugateMatter_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    exact ((stationary variation).unique actual).symm
  · intro weakEquation variation
    have actual :=
      holonomicDiracDualFormNativeIntegratedUnifiedAction_conjugateMatter_hasDerivAt
        source configuration smooth nondegenerate densityIntegrable variation
    simpa only [weakEquation variation] using actual

def diracDualConjugateMatterDirectionalCoefficient
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (point : BasePoint) : ℝ :=
  generatedVolumeDensity (toContinuumPointField configuration point) *
    (matterDualOfCoordinates direction
      (generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField configuration point))).re

theorem diracDualConjugateMatterFirstVariationDensity_scalarTimes
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ)
    (point : BasePoint) :
    diracDualConjugateMatterFirstVariationDensity source configuration
        (scalarTimesConjugateMatterVariation direction variation) point =
      variation point *
        diracDualConjugateMatterDirectionalCoefficient source configuration
          direction point := by
  unfold diracDualConjugateMatterFirstVariationDensity
    scalarTimesConjugateMatterVariation
    diracDualConjugateMatterDirectionalCoefficient
  rw [matterDualOfCoordinates_real_smul, LinearMap.smul_apply]
  change _ * (((variation point : ℂ) * _).re) = _
  simp [Complex.mul_re]
  ring

theorem diracDualConjugateMatterDirectionalCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : MatterCoordinateCarrier) :
    Continuous
      (diracDualConjugateMatterDirectionalCoefficient source configuration
        direction) := by
  have coframeContinuous := holonomicCoframe_continuous configuration smooth
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) :=
    coframeContinuous.matrix_det.abs
  have vectorContinuous :=
    holonomicGeneratedContinuumDiracDualMatterVector_coordinate_continuous
      source configuration smooth nondegenerate
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv
            (generatedContinuumDiracDualMatterVector source 0 point
              (toContinuumPointField configuration point)) index *
          direction index := by
    apply continuous_finsetSum
    intro index _
    exact ((PiLp.continuous_apply 2
      (fun _ : MatterCoordinateIndex => ℂ) index).comp vectorContinuous).mul
        continuous_const
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold diracDualConjugateMatterDirectionalCoefficient
  simp_rw [matterDualOfCoordinates_apply]
  exact volumeContinuous.mul realPairingContinuous

theorem diracDualFormNativeConjugateMatterWeakEquation_direction_integral
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (weakEquation :
      DiracDualFormNativeConjugateMatterWeakEquation source configuration)
    (direction : MatterCoordinateCarrier)
    (variation : CompactlySupportedSmoothVariation ℝ) :
    (∫ point : BasePoint,
      variation point *
        diracDualConjugateMatterDirectionalCoefficient source configuration
          direction point) = 0 := by
  have actual := weakEquation
    (scalarTimesConjugateMatterVariation direction variation)
  simpa only [diracDualConjugateMatterFirstVariationDensity_scalarTimes] using
    actual

def DiracDualFormNativeConjugateMatterPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ direction : MatterCoordinateCarrier,
    diracDualConjugateMatterDirectionalCoefficient source configuration
      direction = 0

theorem
    diracDualFormNativeConjugateMatterWeakEquation_implies_pointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (weakEquation :
      DiracDualFormNativeConjugateMatterWeakEquation source configuration) :
    DiracDualFormNativeConjugateMatterPointwiseEquation source
      configuration := by
  intro direction
  apply continuous_eq_zero_of_integral_mul_compactSmooth_eq_zero
    (diracDualConjugateMatterDirectionalCoefficient source configuration
      direction)
    (diracDualConjugateMatterDirectionalCoefficient_continuous source
      configuration smooth nondegenerate direction)
  intro variation
  exact
    diracDualFormNativeConjugateMatterWeakEquation_direction_integral source
      configuration weakEquation direction variation

/-- The repaired conjugate EL equation is the zero fiber of the complete
kinetic-plus-Dirac-dual-Yukawa forward vector. -/
def GeneratedDiracDualMatterEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point : BasePoint,
    generatedContinuumDiracDualMatterVector source 0 point
      (toContinuumPointField configuration point) = 0

theorem
    diracDualFormNativeConjugateMatterPointwiseEquation_implies_generatedEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (pointwise :
      DiracDualFormNativeConjugateMatterPointwiseEquation source
        configuration) :
    GeneratedDiracDualMatterEquation source configuration := by
  intro point
  let vector := generatedContinuumDiracDualMatterVector source 0 point
    (toContinuumPointField configuration point)
  have volumeNe :
      generatedVolumeDensity (toContinuumPointField configuration point) ≠
        0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr (nondegenerate point)
  apply matterCoordinateEquiv.injective
  apply PiLp.ext
  intro index
  let realDirection : MatterCoordinateCarrier :=
    EuclideanSpace.single index (1 : ℂ)
  let imaginaryDirection : MatterCoordinateCarrier :=
    EuclideanSpace.single index Complex.I
  have realEquation := congrFun (pointwise realDirection) point
  have imaginaryEquation := congrFun (pointwise imaginaryDirection) point
  simp only [Pi.zero_apply] at realEquation imaginaryEquation
  have realPartZero : (matterCoordinateEquiv vector index).re = 0 := by
    unfold diracDualConjugateMatterDirectionalCoefficient realDirection
      at realEquation
    rw [matterDualOfCoordinates_single_apply] at realEquation
    simp only [mul_one] at realEquation
    exact (mul_eq_zero.mp realEquation).resolve_left volumeNe
  have imaginaryPartZero : (matterCoordinateEquiv vector index).im = 0 := by
    unfold diracDualConjugateMatterDirectionalCoefficient imaginaryDirection
      at imaginaryEquation
    rw [matterDualOfCoordinates_single_apply] at imaginaryEquation
    have productReal :
        (matterCoordinateEquiv vector index * Complex.I).re =
          -(matterCoordinateEquiv vector index).im := by
      simp
    rw [productReal] at imaginaryEquation
    have negImaginaryZero :=
      (mul_eq_zero.mp imaginaryEquation).resolve_left volumeNe
    exact neg_eq_zero.mp negImaginaryZero
  have coordinateZero : matterCoordinateEquiv vector index = 0 :=
    Complex.ext realPartZero imaginaryPartZero
  simpa [vector] using coordinateZero

theorem
    generatedDiracDualMatterEquation_implies_conjugateMatterPointwiseEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (equation : GeneratedDiracDualMatterEquation source configuration) :
    DiracDualFormNativeConjugateMatterPointwiseEquation source
      configuration := by
  intro direction
  funext point
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [equation point]
  simp

/-- Faithful zero fiber of the complete real/imaginary coordinate-dual test
family. -/
theorem
    diracDualFormNativeConjugateMatterPointwiseEquation_iff_generatedEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    DiracDualFormNativeConjugateMatterPointwiseEquation source configuration ↔
      GeneratedDiracDualMatterEquation source configuration := by
  constructor
  · exact
      diracDualFormNativeConjugateMatterPointwiseEquation_implies_generatedEquation
        source configuration nondegenerate
  · exact
      generatedDiracDualMatterEquation_implies_conjugateMatterPointwiseEquation
        source configuration

theorem
    diracDualFormNativeConjugateMatterActionStationary_implies_generatedEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable :
      DiracDualFormNativeHolonomicLocalDensityIntegrable source 0
        configuration)
    (stationary :
      DiracDualFormNativeConjugateMatterActionStationary source
        configuration) :
    GeneratedDiracDualMatterEquation source configuration := by
  apply
    diracDualFormNativeConjugateMatterPointwiseEquation_implies_generatedEquation
      source configuration nondegenerate
  apply
    diracDualFormNativeConjugateMatterWeakEquation_implies_pointwiseEquation
      source configuration smooth nondegenerate
  exact
    (diracDualFormNativeConjugateMatterActionStationary_iff_weakEquation source
      configuration smooth nondegenerate densityIntegrable).1 stationary

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConjugateMatterVariation
