import H0mework.Chemistry.LAlanineBandContinuation.ConservationLocalCharts
import H0mework.Chemistry.LAlanineWholeBandAdjacent.ConservationTangents
import H0mework.Chemistry.LAlanineTrueFlowBoundary.TopologyLocalExtensions

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open SourceGaussianModel WholeBandGeometry WholeBandContinuation WholeBandContinuationParameter
open WholeBandCell1Actual WholeBandConservation WholeCellBoundary AdjacentFlow Set
noncomputable section

theorem actual_local_extension (p : Point) (inside : p ∈ jointDomain) :
    ∃ e : OpenPartialHomeomorph Point Point,p ∈ e.source ∧ EqOn e jointMap (jointDomain ∩ e.source) := by
  have allowed (q : Point) (hq : q ∈ jointDomain) : |2 * q 2| ≤ 1 := by
    have time := ((joint_membership q).mp hq).2.2
    exact abs_le.mpr ⟨by linarith [time.1],by linarith [time.2]⟩
  have slab : ∃ e : OpenPartialHomeomorph Point Point,p ∈ e.source ∧
      EqOn e jointMap ({q : Point | |2 * q 2| ≤ 1} ∩ e.source) := by
    rcases inside with left | right
    · exact actual_local_extension_on_time_slab 0 cell0_source_fields WholeBandCell0Differential.cell0_analytic_bounds
        cell0_positive_reports p left
    · exact actual_local_extension_on_time_slab 1 cell1_source_fields WholeBandCell1Differential.cell1_analytic_bounds
        cell1_positive_reports p right
  obtain ⟨e,atSource,agrees⟩ := slab
  exact ⟨e,atSource,fun q hq => agrees ⟨allowed q hq.1,hq.2⟩⟩

theorem domain_interior : interior jointDomain = Set.pi Set.univ (fun i => Ioo (lower i) (upper i)) := by
  rw [joint_domain_eq_Icc,← pi_univ_Icc,interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]
  rfl

theorem mem_frontier_iff (p : Point) : p ∈ frontier jointDomain ↔
    p ∈ jointDomain ∧ ∃ i : Fin 3,p i = lower i ∨ p i = upper i := by
  rw [frontier,joint_domain_compact.isClosed.closure_eq,domain_interior]
  constructor
  · rintro ⟨inside,notInterior⟩
    have bounds : p ∈ Icc lower upper := joint_domain_eq_Icc ▸ inside
    have failed : ¬∀ i : Fin 3,lower i < p i ∧ p i < upper i := by
      intro all
      exact notInterior (fun i _ => all i)
    push Not at failed
    obtain ⟨i,lowerBound⟩ := failed
    refine ⟨inside,i,?_⟩
    by_cases h : lower i < p i
    · exact Or.inr (le_antisymm (bounds.2 i) (lowerBound h))
    · exact Or.inl (le_antisymm (le_of_not_gt h) (bounds.1 i))
  · rintro ⟨inside,i,boundary⟩
    refine ⟨inside,?_⟩
    intro interior
    have strict := interior i (mem_univ i)
    rcases boundary with atLower | atUpper
    · exact lt_irrefl _ (atLower ▸ strict.1)
    · exact lt_irrefl _ (atUpper ▸ strict.2)

theorem parameter_frontier_eq_six_faces : frontier jointDomain = ⋃ face : Face,parameterFace face := by
  ext p
  rw [mem_frontier_iff,mem_iUnion]
  constructor
  · rintro ⟨inside,i,lo | hi⟩
    · exact ⟨(i,false),(parameterFace_mem_iff _ p).mpr ⟨inside,lo⟩⟩
    · exact ⟨(i,true),(parameterFace_mem_iff _ p).mpr ⟨inside,hi⟩⟩
  · rintro ⟨⟨i,upper⟩,onFace⟩
    obtain ⟨inside,value⟩ := (parameterFace_mem_iff _ p).mp onFace
    refine ⟨inside,i,?_⟩
    cases upper
    · exact Or.inl value
    · exact Or.inr value

def actualSpatialFace (face : Face) : Set Point := actualFaceMap face '' faceDomain face.1

theorem actual_boundary_image : frontier jointImage = jointMap '' frontier jointDomain :=
  WholeCellBoundaryTopology.frontier_image_of_local_extensions jointMap jointDomain joint_domain_compact
    jointMap_continuousOn jointMap_injOn actual_local_extension

theorem actual_boundary_eq_six_faces : frontier jointImage = ⋃ face : Face,actualSpatialFace face := by
  rw [actual_boundary_image,parameter_frontier_eq_six_faces,image_iUnion]
  apply iUnion_congr
  intro face
  rw [parameterFace,image_image]
  rfl

theorem actualSpatialFace_nonempty (face : Face) : (actualSpatialFace face).Nonempty :=
  (faceDomain_nonempty face.1).image (actualFaceMap face)

theorem actualFaceMap_mem_boundary (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    actualFaceMap face p ∈ frontier jointImage := by
  rw [actual_boundary_eq_six_faces]
  exact mem_iUnion.mpr ⟨face,p,inside,rfl⟩

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
