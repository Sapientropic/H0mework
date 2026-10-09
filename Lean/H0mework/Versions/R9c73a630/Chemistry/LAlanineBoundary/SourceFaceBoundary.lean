import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceFaces

/-! The six source restrictions exactly cover the parameter boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary

open SourceGaussianModel WholeCellPartition Set
noncomputable section

theorem faceCoordinate_bounds (face : Face) :
    fullLower face.1 ≤ faceCoordinate face ∧ faceCoordinate face ≤ fullUpper face.1 := by
  have ordered : fullLower face.1 ≤ fullUpper face.1 := Rat.cast_le.mpr (full_ordered face.1).le
  cases face with
  | mk axis upper => cases upper <;> exact ⟨by first | exact le_rfl | exact ordered,
      by first | exact le_rfl | exact ordered⟩

theorem faceParameter_mem (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    faceParameter face p ∈ fullDomain :=
  ⟨Fin.le_insertNth_iff.mpr ⟨(faceCoordinate_bounds face).1, inside.1⟩,
    Fin.insertNth_le_iff.mpr ⟨(faceCoordinate_bounds face).2, inside.2⟩⟩

theorem faceParameter_axis (face : Face) (p : FacePoint) :
    faceParameter face p face.1 = faceCoordinate face := Fin.insertNth_apply_same _ _ _

theorem parameterFace_mem_iff (face : Face) (p : Point) :
    p ∈ parameterFace face ↔ p ∈ fullDomain ∧ p face.1 = faceCoordinate face := by
  constructor
  · rintro ⟨y, inside, rfl⟩
    exact ⟨faceParameter_mem face y inside, faceParameter_axis face y⟩
  · rintro ⟨inside, onFace⟩
    refine ⟨Fin.removeNth face.1 p, ⟨fun j => inside.1 (face.1.succAbove j),
      fun j => inside.2 (face.1.succAbove j)⟩, ?_⟩
    rw [faceParameter, ← onFace]
    exact Fin.insertNth_self_removeNth face.1 p

theorem fullDomain_interior : interior fullDomain =
    Set.pi Set.univ (fun i => Ioo (fullLower i) (fullUpper i)) := by
  unfold fullDomain
  rw [← pi_univ_Icc, interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]

theorem mem_full_frontier_iff (p : Point) : p ∈ frontier fullDomain ↔
    p ∈ fullDomain ∧ ∃ i : Fin 3, p i = fullLower i ∨ p i = fullUpper i := by
  rw [frontier, show closure fullDomain = fullDomain from isClosed_Icc.closure_eq, fullDomain_interior]
  constructor
  · rintro ⟨inside, notInterior⟩
    have failed : ¬∀ i : Fin 3, fullLower i < p i ∧ p i < fullUpper i := by
      intro all
      exact notInterior (fun i _ => all i)
    push Not at failed
    obtain ⟨i, lower⟩ := failed
    refine ⟨inside, i, ?_⟩
    by_cases h : fullLower i < p i
    · exact Or.inr (le_antisymm (inside.2 i) (lower h))
    · exact Or.inl (le_antisymm (le_of_not_gt h) (inside.1 i))
  · rintro ⟨inside, i, boundary⟩
    refine ⟨inside, ?_⟩
    intro interior
    have strict := interior i (mem_univ i)
    rcases boundary with atLower | atUpper
    · exact lt_irrefl _ (atLower ▸ strict.1)
    · exact lt_irrefl _ (atUpper ▸ strict.2)

theorem parameter_frontier_eq_six_faces : frontier fullDomain = ⋃ face : Face, parameterFace face := by
  ext p
  rw [mem_full_frontier_iff, mem_iUnion]
  constructor
  · rintro ⟨inside, i, lower | upper⟩
    · exact ⟨(i,false), (parameterFace_mem_iff _ p).mpr ⟨inside, lower⟩⟩
    · exact ⟨(i,true), (parameterFace_mem_iff _ p).mpr ⟨inside, upper⟩⟩
  · rintro ⟨⟨i, upper⟩, onFace⟩
    obtain ⟨inside, value⟩ := (parameterFace_mem_iff _ p).mp onFace
    refine ⟨inside, i, ?_⟩
    cases upper
    · exact Or.inl value
    · exact Or.inr value

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
