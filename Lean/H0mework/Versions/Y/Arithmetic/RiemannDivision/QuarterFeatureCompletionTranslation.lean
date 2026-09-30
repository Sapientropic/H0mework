import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartCompletion
import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAction

/-!
# Translation on the source-generated quarter-feature completion

The actual source dilation and quarter-energy translation generate one
isometric action on the completed feature range.  Its additive rechart is
the installed Burnol multiplicative dilation.  No spectral or boundary
premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal

noncomputable section

def quarterFeatureRangeTranslation (z : ℂ) (shift : ℝ) :
    LinearMap.range (quarterMellinL2Feature z) →ₗᵢ[ℂ]
      LinearMap.range (quarterMellinL2Feature z) where
  toLinearMap :=
    (((positiveMellinQuarterEnergyTranslationIsometry shift).toLinearEquiv.toLinearMap
      ).domRestrict (LinearMap.range (quarterMellinL2Feature z))).codRestrict
        (LinearMap.range (quarterMellinL2Feature z))
        (by
          rintro ⟨_, ⟨source, rfl⟩⟩
          refine ⟨quarterDilationTestAction z (Real.exp shift)
            (Real.exp_pos shift) source, ?_⟩
          change quarterMellinL2Feature z
              (quarterDilationTestAction z (Real.exp shift)
                (Real.exp_pos shift) source) =
            positiveMellinQuarterEnergyTranslation shift
              (quarterMellinL2Feature z source)
          have covariance := LinearMap.congr_fun
            (quarterDilationFeature_covariance z (Real.exp shift)
              (Real.exp_pos shift)) source
          change positiveMellinQuarterEnergyTranslation
              (Real.log (Real.exp shift)) (quarterMellinL2Feature z source) =
            quarterMellinL2Feature z
              (quarterDilationTestAction z (Real.exp shift)
                (Real.exp_pos shift) source) at covariance
          rw [Real.log_exp] at covariance
          exact covariance.symm)
  norm_map' value :=
    (positiveMellinQuarterEnergyTranslationIsometry shift).norm_map value.1

@[simp] theorem quarterFeatureRangeTranslation_apply
    (z : ℂ) (shift : ℝ)
    (value : LinearMap.range (quarterMellinL2Feature z)) :
    ((quarterFeatureRangeTranslation z shift value :
        LinearMap.range (quarterMellinL2Feature z)) :
      PositiveMellinQuarterEnergy) =
      positiveMellinQuarterEnergyTranslation shift value.1 := by
  rfl

def quarterFeatureRangeEmbedding (z : ℂ) :
    LinearMap.range (quarterMellinL2Feature z) →L[ℂ]
      HilbertAmbient (quarterMellinL2Feature z) :=
  (UniformSpace.Completion.toComplₗᵢ :
    LinearMap.range (quarterMellinL2Feature z) →ₗᵢ[ℂ]
      HilbertAmbient (quarterMellinL2Feature z)).toContinuousLinearMap

theorem quarterFeatureRangeEmbedding_denseRange (z : ℂ) :
    DenseRange (quarterFeatureRangeEmbedding z) :=
  UniformSpace.Completion.denseRange_coe

theorem quarterFeatureRangeEmbedding_isUniformInducing (z : ℂ) :
    IsUniformInducing (quarterFeatureRangeEmbedding z) :=
  (UniformSpace.Completion.toComplₗᵢ :
    LinearMap.range (quarterMellinL2Feature z) →ₗᵢ[ℂ]
      HilbertAmbient (quarterMellinL2Feature z)).isometry.isUniformInducing

@[simp] theorem hilbertAmbientRealization_quarterFeatureRangeEmbedding
    (z : ℂ) (value : LinearMap.range (quarterMellinL2Feature z)) :
    hilbertAmbientRealization (quarterMellinL2Feature z)
        (quarterFeatureRangeEmbedding z value) = value.1 := by
  change hilbertAmbientRealization (quarterMellinL2Feature z)
      (value : HilbertAmbient (quarterMellinL2Feature z)) = value.1
  exact hilbertAmbientRealization_range_readback
    (quarterMellinL2Feature z) value

def quarterFeatureCompletionTranslationCLM (z : ℂ) (shift : ℝ) :
    HilbertAmbient (quarterMellinL2Feature z) →L[ℂ]
      HilbertAmbient (quarterMellinL2Feature z) :=
  ((quarterFeatureRangeEmbedding z).comp
    (quarterFeatureRangeTranslation z shift).toContinuousLinearMap).extend
      (quarterFeatureRangeEmbedding z)

@[simp] theorem quarterFeatureCompletionTranslationCLM_range_readback
    (z : ℂ) (shift : ℝ)
    (value : LinearMap.range (quarterMellinL2Feature z)) :
    quarterFeatureCompletionTranslationCLM z shift
        (quarterFeatureRangeEmbedding z value) =
      quarterFeatureRangeEmbedding z
        (quarterFeatureRangeTranslation z shift value) := by
  rw [quarterFeatureCompletionTranslationCLM,
    ContinuousLinearMap.extend_eq
      ((quarterFeatureRangeEmbedding z).comp
        (quarterFeatureRangeTranslation z shift).toContinuousLinearMap)
      (quarterFeatureRangeEmbedding_denseRange z)
      (quarterFeatureRangeEmbedding_isUniformInducing z)]
  rfl

theorem quarterFeatureCompletionTranslationCLM_norm
    (z : ℂ) (shift : ℝ)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    ‖quarterFeatureCompletionTranslationCLM z shift value‖ = ‖value‖ := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (continuous_norm.comp
          (quarterFeatureCompletionTranslationCLM z shift).continuous)
        continuous_norm
  | ih rangeValue =>
      change ‖quarterFeatureCompletionTranslationCLM z shift
          (quarterFeatureRangeEmbedding z rangeValue)‖ =
        ‖quarterFeatureRangeEmbedding z rangeValue‖
      rw [quarterFeatureCompletionTranslationCLM_range_readback]
      simp [quarterFeatureRangeEmbedding]

/-- The actual source dilation extended isometrically over the entire
source-generated feature completion. -/
def quarterFeatureCompletionTranslation (z : ℂ) (shift : ℝ) :
    HilbertAmbient (quarterMellinL2Feature z) →ₗᵢ[ℂ]
      HilbertAmbient (quarterMellinL2Feature z) where
  toLinearMap := (quarterFeatureCompletionTranslationCLM z shift).toLinearMap
  norm_map' := quarterFeatureCompletionTranslationCLM_norm z shift

@[simp] theorem quarterFeatureCompletionTranslation_source
    (z : ℂ) (shift : ℝ) (source : QuarterMellinL2Test z) :
    quarterFeatureCompletionTranslation z shift
        (canonicalHilbertMap (quarterMellinL2Feature z) source) =
      canonicalHilbertMap (quarterMellinL2Feature z)
        (quarterDilationTestAction z (Real.exp shift)
          (Real.exp_pos shift) source) := by
  change quarterFeatureCompletionTranslationCLM z shift
      (quarterFeatureRangeEmbedding z
        ((quarterMellinL2Feature z).rangeRestrict source)) = _
  rw [quarterFeatureCompletionTranslationCLM_range_readback]
  change quarterFeatureRangeEmbedding z
      (quarterFeatureRangeTranslation z shift
        ((quarterMellinL2Feature z).rangeRestrict source)) =
    quarterFeatureRangeEmbedding z
      ((quarterMellinL2Feature z).rangeRestrict
        (quarterDilationTestAction z (Real.exp shift)
          (Real.exp_pos shift) source))
  congr 1
  apply Subtype.ext
  change positiveMellinQuarterEnergyTranslation shift
      (quarterMellinL2Feature z source) =
    quarterMellinL2Feature z
      (quarterDilationTestAction z (Real.exp shift)
        (Real.exp_pos shift) source)
  have covariance := LinearMap.congr_fun
    (quarterDilationFeature_covariance z (Real.exp shift)
      (Real.exp_pos shift)) source
  change positiveMellinQuarterEnergyTranslation
      (Real.log (Real.exp shift)) (quarterMellinL2Feature z source) =
    quarterMellinL2Feature z
      (quarterDilationTestAction z (Real.exp shift)
        (Real.exp_pos shift) source) at covariance
  rw [Real.log_exp] at covariance
  exact covariance

theorem quarterFeatureCompletionTranslation_realization
    (z : ℂ) (shift : ℝ)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    hilbertAmbientRealization (quarterMellinL2Feature z)
        (quarterFeatureCompletionTranslation z shift value) =
      positiveMellinQuarterEnergyTranslation shift
        (hilbertAmbientRealization (quarterMellinL2Feature z) value) := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((hilbertAmbientRealization
          (quarterMellinL2Feature z)).continuous.comp
            (quarterFeatureCompletionTranslation z shift).continuous)
        ((positiveMellinQuarterEnergyTranslationIsometry shift).continuous.comp
          (hilbertAmbientRealization (quarterMellinL2Feature z)).continuous)
  | ih rangeValue =>
      change hilbertAmbientRealization (quarterMellinL2Feature z)
          (quarterFeatureCompletionTranslationCLM z shift
            (quarterFeatureRangeEmbedding z rangeValue)) =
        positiveMellinQuarterEnergyTranslation shift
          (hilbertAmbientRealization (quarterMellinL2Feature z)
            (quarterFeatureRangeEmbedding z rangeValue))
      rw [quarterFeatureCompletionTranslationCLM_range_readback]
      rw [hilbertAmbientRealization_quarterFeatureRangeEmbedding,
        hilbertAmbientRealization_quarterFeatureRangeEmbedding]
      exact quarterFeatureRangeTranslation_apply z shift rangeValue

/-- The completion action is the installed Burnol multiplicative dilation
after the reciprocal-square additive rechart. -/
theorem quarterMellinFeatureCompletionEvenAdditive_translation
    (z : ℂ) (shift : ℝ)
    (value : HilbertAmbient (quarterMellinL2Feature z)) :
    quarterMellinFeatureCompletionEvenAdditive z
        (quarterFeatureCompletionTranslation z shift value) =
      burnolMultiplicativeDilation (-shift / 2)
        (quarterMellinFeatureCompletionEvenAdditive z value) := by
  have sourceDense : DenseRange
      (canonicalHilbertMap (quarterMellinL2Feature z)) := by
    have dense := UniformSpace.Completion.denseRange_coe.comp
      (quarterMellinL2Feature z).surjective_rangeRestrict.denseRange
      (UniformSpace.Completion.continuous_coe
        (LinearMap.range (quarterMellinL2Feature z)))
    simpa [canonicalHilbertMap, Function.comp_def] using dense
  apply DenseRange.induction_on
    (p := fun point : HilbertAmbient (quarterMellinL2Feature z) =>
      quarterMellinFeatureCompletionEvenAdditive z
          (quarterFeatureCompletionTranslation z shift point) =
        burnolMultiplicativeDilation (-shift / 2)
          (quarterMellinFeatureCompletionEvenAdditive z point))
    sourceDense value
  · exact isClosed_eq
      ((quarterMellinFeatureCompletionEvenAdditive z).continuous.comp
        (quarterFeatureCompletionTranslation z shift).continuous)
      ((burnolMultiplicativeDilation (-shift / 2)).continuous.comp
        (quarterMellinFeatureCompletionEvenAdditive z).continuous)
  · intro source
    have covariance := quarterMellinAdditiveEvenRechart_dilation z source
      (Real.exp shift) (Real.exp_pos shift)
    rw [Real.log_exp] at covariance
    calc
      quarterMellinFeatureCompletionEvenAdditive z
          (quarterFeatureCompletionTranslation z shift
            (canonicalHilbertMap (quarterMellinL2Feature z) source)) =
          (2 : ℂ) • quarterMellinAdditiveEvenRechart
            (quarterDilationTestAction z (Real.exp shift)
              (Real.exp_pos shift) source) := by
        rw [quarterFeatureCompletionTranslation_source,
          quarterMellinFeatureCompletionEvenAdditive_source]
      _ = (2 : ℂ) • burnolMultiplicativeDilation (-shift / 2)
          (quarterMellinAdditiveEvenRechart source) := by rw [covariance]
      _ = burnolMultiplicativeDilation (-shift / 2)
          ((2 : ℂ) • quarterMellinAdditiveEvenRechart source) := by
        rw [map_smul]
      _ = burnolMultiplicativeDilation (-shift / 2)
          (quarterMellinFeatureCompletionEvenAdditive z
            (canonicalHilbertMap (quarterMellinL2Feature z) source)) := by
        rw [quarterMellinFeatureCompletionEvenAdditive_source]

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
