import H0mework.Chemistry.LAlanineTrueFlowBoundary.SourceLocalCharts
import H0mework.Chemistry.LAlanineTrueFlowBoundary.TopologyLocalExtensions
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SpatialImage
import H0mework.Chemistry.LAlanineBoundary.SourceFaceBoundary
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceSideFlux

/-!
The actual local extensions carry the original six parameter faces onto the full frontier
of the true-flow image. Their maps and pointwise side fluxes are the original actual ones.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundary

open SourceGaussianModel TrueFlowDifferential TrueFlowGeometry TrueTubeWholeActual
open WholeCellBoundary WholeCellPartition Set
noncomputable section

/-- The spatial face uses the already generated actual face map on its original domain. -/
def trueSpatialFace (face : Face) : Set Point := trueFaceMap face '' faceDomain face.1

theorem true_boundary_image : frontier truePatch = trueParameterMap '' frontier fullDomain :=
  WholeCellBoundaryTopology.frontier_image_of_local_extensions
    trueParameterMap fullDomain full_compact trueParameterMap_continuousOn trueParameterMap_injOn
    (fun p inside => actual_local_extension ⟨p, inside⟩)

/-- All six original source restrictions, including both time caps, cover the actual frontier. -/
theorem true_boundary_eq_six_faces : frontier truePatch = ⋃ face : Face, trueSpatialFace face := by
  rw [true_boundary_image, parameter_frontier_eq_six_faces, image_iUnion]
  apply iUnion_congr
  intro face
  rw [parameterFace, image_image]
  rfl

theorem trueSpatialFace_nonempty (face : Face) : (trueSpatialFace face).Nonempty :=
  (faceDomain_nonempty face.1).image (trueFaceMap face)

theorem trueSpatialFace_subset_boundary (face : Face) : trueSpatialFace face ⊆ frontier truePatch := by
  rw [true_boundary_eq_six_faces]
  exact subset_iUnion (fun face => trueSpatialFace face) face

theorem trueFaceMap_mem_boundary (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) : trueFaceMap face p ∈ frontier truePatch :=
  trueSpatialFace_subset_boundary face ⟨p, inside, rfl⟩

theorem true_source_corner_on_boundary : trueParameterMap fullLower ∈ frontier truePatch := by
  rw [true_boundary_image]
  apply mem_image_of_mem
  apply (mem_full_frontier_iff fullLower).mpr
  exact ⟨⟨le_rfl, fun i => Rat.cast_le.mpr (full_ordered i).le⟩, 0, Or.inl rfl⟩

/-- The original four side-flux identities now refer to points on the exact actual frontier. -/
theorem true_side_boundary_flux (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) :
    trueFaceMap face p ∈ frontier truePatch ∧ trueFaceFlux face p inside = 0 :=
  ⟨trueFaceMap_mem_boundary face p inside, trueSideFlux_zero face p inside side⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
