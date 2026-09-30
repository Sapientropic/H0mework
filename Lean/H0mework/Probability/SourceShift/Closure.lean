import H0mework.Probability.SourceShift.Mean

/-! The source certificate itself generates Hilbert approximants to the original unit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSuccessorBoundary

open SourceOwnedObservationHistory.SourceShift Filter
open scoped Topology

noncomputable section

theorem difference_certificate_mean (bound : Nat) :
    difference (readWord (certificate ℂ (meanWord bound))) = mean bound - basis 0 := by
  rw [← readWord_boundary, boundary_certificate, map_sub, map_smul, mass_meanWord,
    one_smul, readWord_unit]
  rfl

theorem unit_sub_mean_mem_source_boundary (bound : Nat) :
    basis 0 - mean bound ∈ (readWord.comp (boundary ℂ)).range := by
  refine ⟨-certificate ℂ (meanWord bound), ?_⟩
  change readWord (boundary ℂ (-certificate ℂ (meanWord bound))) = basis 0 - mean bound
  rw [readWord_boundary, map_neg, map_neg, difference_certificate_mean, neg_sub]

theorem basis_zero_mem_source_boundary_closure :
    basis 0 ∈ (readWord.comp (boundary ℂ)).range.topologicalClosure := by
  have converges : Tendsto (fun bound => basis 0 - mean bound) atTop (𝓝 (basis 0)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub mean_tendsto_zero
  exact mem_closure_of_tendsto converges
    (Eventually.of_forall unit_sub_mean_mem_source_boundary)

theorem basis_zero_mem_difference_closure : basis 0 ∈ difference.range.topologicalClosure := by
  apply Submodule.topologicalClosure_mono (t := difference.range) ?_
    basis_zero_mem_source_boundary_closure
  rintro value ⟨word, rfl⟩
  exact ⟨readWord word, (readWord_boundary word).symm⟩

end
end SourceSuccessorBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
