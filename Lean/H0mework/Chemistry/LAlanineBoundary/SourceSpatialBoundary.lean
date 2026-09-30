import H0mework.Chemistry.LAlanineBoundary.SourceFaceBoundary
import H0mework.Chemistry.LAlanineBoundary.TopologyActualBoundary

/-! The same six source faces cover the actual spatial frontier. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition WholeCellSpatial Set
noncomputable section

theorem actual_boundary_eq_six_faces : frontier fullPatch = ⋃ face : Face, spatialFace face := by
  rw [Topology.actual_boundary_image, parameter_frontier_eq_six_faces, image_iUnion]
  rfl

theorem spatialFace_subset_boundary (face : Face) : spatialFace face ⊆ frontier fullPatch := by
  rw [actual_boundary_eq_six_faces]
  exact subset_iUnion spatialFace face

theorem every_actual_face_is_nonempty : ∀ face : Face, ∃ p ∈ spatialFace face, p ∈ frontier fullPatch := by
  intro face
  obtain ⟨p, inside⟩ := spatialFace_nonempty face
  exact ⟨p, inside, spatialFace_subset_boundary face inside⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
