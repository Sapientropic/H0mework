import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixReadback

open Filter
open scoped InnerProductSpace Topology

open private source_span from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [DecidableEq ι]

/-- The actual finite Gram effects over finite sets of separating tests converge in the source norm. -/
theorem inverse_tendsto_finset (source : ι → H)
    (separates : ∀ x : H, (∀ i : ι, inner ℂ (source i) x = 0) → x = 0) (x : H) :
    Tendsto (fun tests : Finset ι => inverse (fun i : tests => source i)
      (Projection.rhs (fun i : tests => source i) x)) atTop (𝓝 x) := by
  let span (tests : Finset ι) := Projection.sourceSpan (fun i : tests => source i)
  have grows : Monotone span := by
    intro small large included
    change Projection.sourceSpan (fun i : small => source i) ≤
      Projection.sourceSpan (fun i : large => source i)
    rw [source_span, source_span]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.val, included i.property⟩, rfl⟩
  have dense : (⨆ tests, span tests).topologicalClosure = ⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    refine le_antisymm ?_ bot_le
    intro y orthogonal
    rw [Submodule.mem_bot]
    apply separates y
    intro i
    have member : source i ∈ span {i} := by
      dsimp only [span]
      rw [source_span]
      exact Submodule.subset_span ⟨⟨i, Finset.mem_singleton_self i⟩, rfl⟩
    exact (Submodule.mem_orthogonal _ _).mp orthogonal _ (le_iSup span {i} member)
  simpa only [inverse_actual_rhs] using Submodule.starProjection_tendsto_self span grows x
    (le_of_eq dense.symm)

end SourceGeneratedFiniteGram.PrefixReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
