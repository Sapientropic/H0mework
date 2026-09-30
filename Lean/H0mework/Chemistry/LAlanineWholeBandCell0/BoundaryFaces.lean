import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryLocalCharts
import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryTangents
import H0mework.Chemistry.LAlanineTrueFlowBoundary.TopologyLocalExtensions

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary

open SourceGaussianModel WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Spatial WholeCellBoundary Set
noncomputable section

def cell0_trueSpatialFace (face : Face) : Set Point := cell0_trueFaceMap face '' cell0_faceDomain face.1

theorem cell0_true_boundary_image :
    frontier cell0_truePatch = cell0ParameterMap '' frontier (cellDomain 0) :=
  WholeCellBoundaryTopology.frontier_image_of_local_extensions
    cell0ParameterMap (cellDomain 0) cell0_domain_compact cell0ParameterMap_continuousOn cell0ParameterMap_injOn
    (fun p inside => cell0_actual_local_extension ⟨p, inside⟩)

theorem cell0_true_boundary_eq_six_faces : frontier cell0_truePatch = ⋃ face : Face, cell0_trueSpatialFace face := by
  rw [cell0_true_boundary_image, cell0_parameter_frontier_eq_six_faces, image_iUnion]
  apply iUnion_congr
  intro face
  rw [cell0_parameterFace, image_image]
  rfl

theorem cell0_trueSpatialFace_nonempty (face : Face) : (cell0_trueSpatialFace face).Nonempty :=
  (cell0_faceDomain_nonempty face.1).image (cell0_trueFaceMap face)

theorem cell0_trueSpatialFace_subset_boundary (face : Face) : cell0_trueSpatialFace face ⊆ frontier cell0_truePatch := by
  rw [cell0_true_boundary_eq_six_faces]
  exact subset_iUnion (fun face => cell0_trueSpatialFace face) face

theorem cell0_trueFaceMap_mem_boundary (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) : cell0_trueFaceMap face p ∈ frontier cell0_truePatch :=
  cell0_trueSpatialFace_subset_boundary face ⟨p, inside, rfl⟩

theorem cell0_source_corner_on_boundary : cell0ParameterMap cell0Lower ∈ frontier cell0_truePatch := by
  rw [cell0_true_boundary_image]
  apply mem_image_of_mem
  apply (cell0_mem_frontier_iff cell0Lower).mpr
  exact ⟨cell0_domain_eq_Icc.symm.subset ⟨le_rfl, fun i => (cell0_axis_strict i).le⟩, 0, Or.inl rfl⟩

theorem cell0_true_side_boundary_flux (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (side : face.1 ≠ 2) :
    cell0_trueFaceMap face p ∈ frontier cell0_truePatch ∧ cell0_trueFaceFlux face p inside = 0 :=
  ⟨cell0_trueFaceMap_mem_boundary face p inside, cell0_trueSideFlux_zero face p inside side⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
