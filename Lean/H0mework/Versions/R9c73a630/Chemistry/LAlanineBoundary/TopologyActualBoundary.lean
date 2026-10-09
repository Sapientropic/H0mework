import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.TopologyLocalChart
import H0mework.Chemistry.LAlanineBoundary.TopologyCompactBoundary
import Mathlib.Topology.Constructions

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Topology

open SourceGaussianModel ContinuousParameterMap WholeCellPartition WholeCellSpatial Set
noncomputable section

/-- The actual spatial frontier is the image of the same source parameter frontier. -/
theorem actual_boundary_image :
    frontier fullPatch = parameterMap 0 4 '' frontier fullDomain :=
  WholeCellBoundaryTopology.frontier_image_of_local_homeomorph
    (parameterMap 0 4) fullDomain full_compact (parameterMap_contDiff 0 4 0).continuous
    sourceGeneratedWholeCellClosure.chart actual_local_homeomorph

theorem source_lower_is_boundary : fullLower ∈ frontier fullDomain := by
  have interior_description : interior fullDomain = Set.pi Set.univ
      (fun axis => Set.Ioo (fullLower axis) (fullUpper axis)) := by
    unfold fullDomain
    rw [← pi_univ_Icc, interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
    simp only [interior_Icc]
  have source_closed : IsClosed fullDomain := isClosed_Icc
  rw [frontier, source_closed.closure_eq]
  refine ⟨⟨le_rfl, fun axis => Rat.cast_le.mpr (full_ordered axis).le⟩, ?_⟩
  intro interior_member
  rw [interior_description] at interior_member
  exact (lt_irrefl (fullLower 0)) (interior_member 0 (mem_univ 0)).1

theorem actual_source_corner_on_boundary : parameterMap 0 4 fullLower ∈ frontier fullPatch := by
  rw [actual_boundary_image]
  exact mem_image_of_mem _ source_lower_is_boundary

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Topology
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
