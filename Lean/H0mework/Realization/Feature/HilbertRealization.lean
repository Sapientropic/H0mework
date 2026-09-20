import Mathlib.Topology.Algebra.LinearMapCompletion
import H0mework.Realization.Feature.HilbertCompletion

/-!
# Realization of a source-generated Hilbert completion

When an actual complex feature already lands in a complete Hilbert carrier,
the completion of its range has a canonical isometric realization back in
that carrier.  This is the missing faithful arrow from coherent completion
to the source-owned ambient; it adds no finite-dimensionality, closed-range,
surjectivity, polarization, or determinant premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedComplexFeaturePerfectification

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- The actual feature range included isometrically in its source-owned
complete target. -/
def featureRangeInclusion (feature : C →ₗ[ℂ] H) :
    LinearMap.range feature →L[ℂ] H :=
  (LinearMap.range feature).subtypeₗᵢ.toContinuousLinearMap

/-- Continuous extension of the range inclusion over its completion. -/
def hilbertAmbientRealizationCLM (feature : C →ₗ[ℂ] H) :
    HilbertAmbient feature →L[ℂ] H :=
  (featureRangeInclusion feature).fromCompletion

@[simp] theorem hilbertAmbientRealizationCLM_range_readback
    (feature : C →ₗ[ℂ] H) (value : LinearMap.range feature) :
    hilbertAmbientRealizationCLM feature value = value.1 := by
  exact ContinuousLinearMap.fromCompletion_apply_coe
    (featureRangeInclusion feature) value

theorem hilbertAmbientRealizationCLM_norm
    (feature : C →ₗ[ℂ] H) (value : HilbertAmbient feature) :
    ‖hilbertAmbientRealizationCLM feature value‖ = ‖value‖ := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (continuous_norm.comp
          (hilbertAmbientRealizationCLM feature).continuous)
        continuous_norm
  | ih rangeValue =>
      rw [hilbertAmbientRealizationCLM_range_readback]
      rw [UniformSpace.Completion.norm_coe]
      exact Submodule.norm_coe rangeValue

/-- The completed-range realization is uniquely determined by its actual
range readback. -/
theorem hilbertAmbientRealizationCLM_unique
    (feature : C →ₗ[ℂ] H)
    (other : HilbertAmbient feature →L[ℂ] H)
    (readback : ∀ value : LinearMap.range feature,
      other value = value.1) :
    other = hilbertAmbientRealizationCLM feature := by
  exact (ContinuousLinearMap.fromCompletion_unique
    (featureRangeInclusion feature) other
    (fun value => (readback value).symm)).symm

theorem hilbertAmbientRealizationCLM_universal
    (feature : C →ₗ[ℂ] H) :
    ∃! realization : HilbertAmbient feature →L[ℂ] H,
      ∀ value : LinearMap.range feature,
        realization value = value.1 := by
  refine ⟨hilbertAmbientRealizationCLM feature,
    hilbertAmbientRealizationCLM_range_readback feature, ?_⟩
  intro other readback
  exact hilbertAmbientRealizationCLM_unique feature other readback

/-- Canonical faithful realization of the completed actual feature range. -/
def hilbertAmbientRealization (feature : C →ₗ[ℂ] H) :
    HilbertAmbient feature →ₗᵢ[ℂ] H where
  toLinearMap := (hilbertAmbientRealizationCLM feature).toLinearMap
  norm_map' := hilbertAmbientRealizationCLM_norm feature

@[simp] theorem hilbertAmbientRealization_range_readback
    (feature : C →ₗ[ℂ] H) (value : LinearMap.range feature) :
    hilbertAmbientRealization feature value = value.1 :=
  hilbertAmbientRealizationCLM_range_readback feature value

@[simp] theorem hilbertAmbientRealization_source_readback
    (feature : C →ₗ[ℂ] H) (value : C) :
    hilbertAmbientRealization feature (canonicalHilbertMap feature value) =
      feature value := by
  exact hilbertAmbientRealization_range_readback feature
    (feature.rangeRestrict value)

theorem hilbertAmbientRealization_injective (feature : C →ₗ[ℂ] H) :
    Function.Injective (hilbertAmbientRealization feature) :=
  (hilbertAmbientRealization feature).injective

end

end SourceGeneratedComplexFeaturePerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
