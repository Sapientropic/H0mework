import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Subspace
import H0mework.Realization.Feature.GramPerfectification

/-!
# Source-generated Hilbert ambient for a complex feature

The feature range need not be complete.  Its uniform completion supplies the
maximal positive branch needed here: a complete complex inner-product ambient,
an exact-kernel source map, and an injective dense map from the radical
quotient.  This does not assert that the original range is closed.
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

/-- Complete inner-product ambient generated from the actual feature range. -/
abbrev HilbertAmbient (feature : C →ₗ[ℂ] H) :=
  UniformSpace.Completion (LinearMap.range feature)

/-- The source enters its generated feature range and then its completion. -/
def canonicalHilbertMap (feature : C →ₗ[ℂ] H) :
    C →ₗ[ℂ] HilbertAmbient feature :=
  (UniformSpace.Completion.toComplₗᵢ :
      LinearMap.range feature →ₗᵢ[ℂ] HilbertAmbient feature).toLinearMap.comp
    feature.rangeRestrict

/-- The radical quotient embeds into the generated complete ambient. -/
def carrierToHilbertAmbient (feature : C →ₗ[ℂ] H) :
    Carrier feature →ₗ[ℂ] HilbertAmbient feature :=
  (UniformSpace.Completion.toComplₗᵢ :
      LinearMap.range feature →ₗᵢ[ℂ] HilbertAmbient feature).toLinearMap.comp
    (carrierEquivRange feature).toLinearMap

theorem carrierToHilbertAmbient_injective
    (feature : C →ₗ[ℂ] H) :
    Function.Injective (carrierToHilbertAmbient feature) :=
  (UniformSpace.Completion.toComplₗᵢ :
    LinearMap.range feature →ₗᵢ[ℂ] HilbertAmbient feature).injective.comp
      (carrierEquivRange feature).injective

theorem carrierToHilbertAmbient_denseRange
    (feature : C →ₗ[ℂ] H) :
    DenseRange (carrierToHilbertAmbient feature) := by
  have dense := UniformSpace.Completion.denseRange_coe.comp
    (carrierEquivRange feature).surjective.denseRange
    (UniformSpace.Completion.continuous_coe (LinearMap.range feature))
  simpa [carrierToHilbertAmbient, Function.comp_def] using dense

@[simp]
theorem carrierToHilbertAmbient_comp_canonicalMap
    (feature : C →ₗ[ℂ] H) :
    (carrierToHilbertAmbient feature).comp (canonicalMap feature) =
      canonicalHilbertMap feature := by
  apply LinearMap.ext
  intro value
  rfl

/-- Completion introduces no new source kernel. -/
theorem canonicalHilbertMap_ker
    (feature : C →ₗ[ℂ] H) :
    LinearMap.ker (canonicalHilbertMap feature) = LinearMap.ker feature := by
  rw [← carrierToHilbertAmbient_comp_canonicalMap feature]
  rw [LinearMap.ker_comp_of_ker_eq_bot]
  · simp [canonicalMap, gramRadical]
  · exact LinearMap.ker_eq_bot_of_injective
      (carrierToHilbertAmbient_injective feature)

end

end SourceGeneratedComplexFeaturePerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
