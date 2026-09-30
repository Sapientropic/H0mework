import H0mework.Realization.Feature.HilbertRealization
import H0mework.Realization.Graph.Completion

/-!
# Realization of a functional graph completion

The graph completion is the completion of an actual range in `H × ℂ`.
When `H` is complete, the generic completed-range realization embeds it
canonically and isometrically back into that common graph target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphPerfectification

open SourceGeneratedComplexFeaturePerfectification
open Set

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- Canonical isometric realization of the completed actual graph range. -/
def graphHilbertAmbientRealization
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    GraphHilbertAmbient feature functional →ₗᵢ[ℂ] GraphTarget H :=
  hilbertAmbientRealization (graphFeature feature functional)

/-- Every completed graph point realizes in the closure of the literal
source graph.  This is the exact topological provenance of graph-completion
points; it does not claim that the literal range is already closed. -/
theorem graphHilbertAmbientRealization_mem_graphClosure
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (value : GraphHilbertAmbient feature functional) :
    graphHilbertAmbientRealization feature functional value ∈
      closure (LinearMap.range (graphFeature feature functional) :
        Set (GraphTarget H)) := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_closure.preimage
        (graphHilbertAmbientRealization feature functional).continuous
  | ih rangeValue =>
      change hilbertAmbientRealization (graphFeature feature functional)
          (rangeValue : HilbertAmbient (graphFeature feature functional)) ∈
        closure (LinearMap.range (graphFeature feature functional) :
          Set (GraphTarget H))
      rw [hilbertAmbientRealization_range_readback]
      exact subset_closure rangeValue.property

@[simp] theorem graphHilbertAmbientRealization_range_readback
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (value : LinearMap.range (graphFeature feature functional)) :
    graphHilbertAmbientRealization feature functional
        (graphRangeEmbedding feature functional value) = value.1 := by
  exact hilbertAmbientRealization_range_readback
    (graphFeature feature functional) value

@[simp] theorem graphHilbertAmbientRealization_source_readback
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (value : C) :
    graphHilbertAmbientRealization feature functional
        (canonicalHilbertMap (graphFeature feature functional) value) =
      graphFeature feature functional value := by
  exact hilbertAmbientRealization_source_readback
    (graphFeature feature functional) value

theorem graphHilbertAmbientRealization_injective
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) :
    Function.Injective (graphHilbertAmbientRealization feature functional) :=
  (graphHilbertAmbientRealization feature functional).injective

end

end SourceGeneratedFunctionalGraphPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
