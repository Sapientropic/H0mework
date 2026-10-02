import H0mework.Versions.R2.Physics.MotherLaws.PointwiseApproximation
import H0mework.Physics.MotherLaws.StreamTopology

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws

open Set Filter UniformSpace MotherStreamLaws
open Stage9C.Revision
open scoped Topology Uniformity UniformConvergence

noncomputable section

theorem pointwise_uniformity_basis :
    (𝓤 (Stream → Stream)).HasBasis
      (fun index : Set Stream × ℕ × ℝ => index.1.Finite ∧ 0 < index.2.2)
      (fun index => {pair : (Stream → Stream) × (Stream → Stream) |
        ∀ x ∈ index.1, ∀ i < index.2.1, dist (pair.1 x i) (pair.2 x i) < index.2.2}) := by
  have basis := UniformOnFun.hasBasis_uniformity_of_basis Stream Stream {s | s.Finite}
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => .union)
    stream_uniformity_basis
  have same := (UniformOnFun.isUniformEmbedding_toFun_finite Stream Stream).comap_uniformity
  change Filter.comap id (𝓤 (Stream → Stream)) = _ at same
  rw [Filter.comap_id] at same
  rw [← same] at basis
  exact basis

/-- No continuity assumption is imposed on the target function. -/
theorem finiteLaw_dense : DenseRange finiteLaw := by
  intro target
  rw [mem_closure_iff_nhds_basis (nhds_basis_uniformity pointwise_uniformity_basis)]
  rintro ⟨K, m, ε⟩ ⟨finite, positive⟩
  obtain ⟨code, near⟩ := finite_native_approximation K finite target m ε positive
  exact ⟨finiteLaw (SpinPair.visit (10 + code)), ⟨SpinPair.visit (10 + code), rfl⟩, near⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws
