import Mathlib.Analysis.InnerProductSpace.ProdL2
import H0mework.Realization.Feature.HilbertCompletion

/-!
# Source-generated functional graph feature

An actual complex feature and an actual algebraic functional generate one
feature into `H × ℂ`.  The second coordinate is therefore part of the same
source occurrence, rather than a later choice of Hilbert-dual representative.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphPerfectification

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert `L²` product used by the graph construction. -/
abbrev GraphTarget (H : Type h) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :=
  WithLp 2 (H × ℂ)

/-- The canonical graph of the source feature and source functional. -/
def graphFeature (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    C →ₗ[ℂ] GraphTarget H :=
  (WithLp.linearEquiv 2 ℂ (H × ℂ)).symm.toLinearMap.comp
    (feature.prod functional)

@[simp]
theorem graphFeature_apply
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) (value : C) :
    (graphFeature feature functional value).fst = feature value ∧
      (graphFeature feature functional value).snd = functional value :=
  ⟨rfl, rfl⟩

@[simp]
theorem graphFeature_fst
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    (WithLp.fstₗ 2 ℂ H ℂ).comp (graphFeature feature functional) = feature := by
  ext value
  rfl

@[simp]
theorem graphFeature_snd
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    (WithLp.sndₗ 2 ℂ H ℂ).comp (graphFeature feature functional) = functional := by
  ext value
  rfl

/-- The graph forgets exactly the source values invisible to both inputs. -/
theorem graphFeature_ker
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    LinearMap.ker (graphFeature feature functional) =
      LinearMap.ker feature ⊓ LinearMap.ker functional := by
  ext value
  simp [graphFeature, LinearMap.mem_ker]

theorem graphFeature_ker_le_feature
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    LinearMap.ker (graphFeature feature functional) ≤
      LinearMap.ker feature := by
  rw [graphFeature_ker]
  exact inf_le_left

theorem graphFeature_ker_le_functional
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    LinearMap.ker (graphFeature feature functional) ≤
      LinearMap.ker functional := by
  rw [graphFeature_ker]
  exact inf_le_right

/-- The source functional factors uniquely through the graph radical
quotient. -/
def quotientFunctional
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    SourceGeneratedComplexFeaturePerfectification.Carrier
      (graphFeature feature functional) →ₗ[ℂ] ℂ :=
  SourceGeneratedComplexFeaturePerfectification.canonicalFactor
    (graphFeature feature functional) functional
    (graphFeature_ker_le_functional feature functional)

@[simp]
theorem quotientFunctional_comp_canonicalMap
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    (quotientFunctional feature functional).comp
        (SourceGeneratedComplexFeaturePerfectification.canonicalMap
          (graphFeature feature functional)) = functional :=
  SourceGeneratedComplexFeaturePerfectification.canonicalFactor_comp_canonicalMap
    (graphFeature feature functional) functional
    (graphFeature_ker_le_functional feature functional)

theorem quotientFunctional_unique
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (other : SourceGeneratedComplexFeaturePerfectification.Carrier
      (graphFeature feature functional) →ₗ[ℂ] ℂ)
    (readback : other.comp
      (SourceGeneratedComplexFeaturePerfectification.canonicalMap
        (graphFeature feature functional)) = functional) :
    other = quotientFunctional feature functional :=
  SourceGeneratedComplexFeaturePerfectification.canonicalFactor_unique
    (graphFeature feature functional) functional
    (graphFeature_ker_le_functional feature functional) other readback

end

end SourceGeneratedFunctionalGraphPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
