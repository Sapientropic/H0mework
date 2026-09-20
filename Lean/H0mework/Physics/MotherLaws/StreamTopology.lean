import H0mework.Physics.MotherLaws.StreamScalar

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws

open Set Filter UniformSpace
open scoped Topology Uniformity UniformConvergence

noncomputable section

/-- Product uniformity controls a finite output prefix; the law-space uniformity
will apply this control uniformly over each compact input set. -/
theorem stream_uniformity_basis :
    (𝓤 Stream).HasBasis (fun index : ℕ × ℝ => 0 < index.2)
      (fun index => {pair : Stream × Stream |
        ∀ i < index.1, dist (pair.1 i) (pair.2 i) < index.2}) := by
  have cover (s : Set ℕ) (finite : s.Finite) : ∃ n : ℕ, s ⊆ {i | i < n} := by
    obtain ⟨bound, upper⟩ := finite.bddAbove
    exact ⟨bound + 1, fun i hi => Nat.lt_succ_of_le (upper hi)⟩
  have directed : Directed (· ⊆ ·) (fun n : ℕ => {i | i < n}) := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · intro i hi
      exact Nat.lt_of_lt_of_le hi (Nat.le_max_left a b)
    · intro i hi
      exact Nat.lt_of_lt_of_le hi (Nat.le_max_right a b)
  have basis := UniformOnFun.hasBasis_uniformity_of_covering_of_basis {s : Set ℕ | s.Finite}
    (t := fun n : ℕ => {i | i < n}) (fun n => Set.finite_lt_nat n) directed cover
    (Metric.uniformity_basis_dist (α := ℝ))
  have same := (UniformOnFun.isUniformEmbedding_toFun_finite ℕ ℝ).comap_uniformity
  change Filter.comap id (𝓤 Stream) = _ at same
  rw [Filter.comap_id] at same
  rw [← same] at basis
  exact basis

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws
