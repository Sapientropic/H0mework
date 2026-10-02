import H0mework.Versions.R2.Physics.MotherDeclarationsPhysical.LawsApproximation
import H0mework.Physics.MotherLaws.StreamTopology

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws

open Set Filter UniformSpace MotherStreamLaws
open scoped Topology Uniformity UniformConvergence

noncomputable section

theorem pointwise_uniformity_basis :
    (𝓤 (Input → Stream)).HasBasis
      (fun index : Set Input × ℕ × ℝ => index.1.Finite ∧ 0 < index.2.2)
      (fun index => {pair : (Input → Stream) × (Input → Stream) |
        ∀ input ∈ index.1, ∀ i < index.2.1, dist (pair.1 input i) (pair.2 input i) < index.2.2}) := by
  have basis := UniformOnFun.hasBasis_uniformity_of_basis Input Stream {s | s.Finite}
    ⟨∅, Set.finite_empty⟩ (directedOn_of_sup_mem fun _ _ => .union) stream_uniformity_basis
  have same := (UniformOnFun.isUniformEmbedding_toFun_finite Input Stream).comap_uniformity
  change Filter.comap id (𝓤 (Input → Stream)) = _ at same
  rw [Filter.comap_id] at same
  rw [← same] at basis
  exact basis

theorem finiteLaw_dense : DenseRange finiteLaw := by
  intro target
  rw [mem_closure_iff_nhds_basis (nhds_basis_uniformity pointwise_uniformity_basis)]
  rintro ⟨K, m, ε⟩ ⟨finite, positive⟩
  obtain ⟨programme, near⟩ := finite_native_approximation K finite target m ε positive
  exact ⟨finiteLaw programme, ⟨programme, rfl⟩, near⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws
