import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.SpatialImage
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.GeometryTangents

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary

open SourceGaussianModel WholeBandGeometry WholeBandCell0Differential WholeBandCell0Spatial
open WholeCellBoundary WholeCellBoundary.Geometry Set
noncomputable section

def cell0_faceDomain (axis : Fin 3) : Set FacePoint :=
  Icc (cell0Lower ∘ axis.succAbove) (cell0Upper ∘ axis.succAbove)
def cell0_faceCoordinate (face : Face) : ℝ := if face.2 then cell0Upper face.1 else cell0Lower face.1
def cell0_faceParameter (face : Face) (p : FacePoint) : Point := face.1.insertNth (cell0_faceCoordinate face) p
def cell0_parameterFace (face : Face) : Set Point := cell0_faceParameter face '' cell0_faceDomain face.1

theorem cell0_faceDomain_nonempty (axis : Fin 3) : (cell0_faceDomain axis).Nonempty :=
  ⟨cell0Lower ∘ axis.succAbove, le_rfl, fun j => (cell0_axis_strict (axis.succAbove j)).le⟩

theorem cell0_faceCoordinate_bounds (face : Face) :
    cell0Lower face.1 ≤ cell0_faceCoordinate face ∧ cell0_faceCoordinate face ≤ cell0Upper face.1 := by
  have ordered := (cell0_axis_strict face.1).le
  cases face with
  | mk axis upper => cases upper <;> exact ⟨by first | exact le_rfl | exact ordered,
      by first | exact le_rfl | exact ordered⟩

theorem cell0_faceParameter_mem (face : Face) (p : FacePoint) (inside : p ∈ cell0_faceDomain face.1) :
    cell0_faceParameter face p ∈ cellDomain 0 :=
  cell0_domain_eq_Icc.symm.subset
    ⟨Fin.le_insertNth_iff.mpr ⟨(cell0_faceCoordinate_bounds face).1, inside.1⟩,
      Fin.insertNth_le_iff.mpr ⟨(cell0_faceCoordinate_bounds face).2, inside.2⟩⟩

theorem cell0_faceParameter_axis (face : Face) (p : FacePoint) :
    cell0_faceParameter face p face.1 = cell0_faceCoordinate face := Fin.insertNth_apply_same _ _ _

theorem cell0_parameterFace_mem_iff (face : Face) (p : Point) :
    p ∈ cell0_parameterFace face ↔ p ∈ cellDomain 0 ∧ p face.1 = cell0_faceCoordinate face := by
  constructor
  · rintro ⟨y, inside, rfl⟩
    exact ⟨cell0_faceParameter_mem face y inside, cell0_faceParameter_axis face y⟩
  · rintro ⟨inside, onFace⟩
    have bounds : p ∈ Icc cell0Lower cell0Upper := cell0_domain_eq_Icc ▸ inside
    refine ⟨Fin.removeNth face.1 p, ⟨fun j => bounds.1 (face.1.succAbove j),
      fun j => bounds.2 (face.1.succAbove j)⟩, ?_⟩
    rw [cell0_faceParameter, ← onFace]
    exact Fin.insertNth_self_removeNth face.1 p

theorem cell0_domain_interior : interior (cellDomain 0) =
    Set.pi Set.univ (fun i => Ioo (cell0Lower i) (cell0Upper i)) := by
  rw [cell0_domain_eq_Icc, ← pi_univ_Icc,
    interior_pi_set (finite_univ : (univ : Set (Fin 3)).Finite)]
  simp only [interior_Icc]

theorem cell0_mem_frontier_iff (p : Point) : p ∈ frontier (cellDomain 0) ↔
    p ∈ cellDomain 0 ∧ ∃ i : Fin 3, p i = cell0Lower i ∨ p i = cell0Upper i := by
  rw [frontier, cell0_domain_compact.isClosed.closure_eq, cell0_domain_interior]
  constructor
  · rintro ⟨inside, notInterior⟩
    have bounds : p ∈ Icc cell0Lower cell0Upper := cell0_domain_eq_Icc ▸ inside
    have failed : ¬∀ i : Fin 3, cell0Lower i < p i ∧ p i < cell0Upper i := by
      intro all
      exact notInterior (fun i _ => all i)
    push Not at failed
    obtain ⟨i, lower⟩ := failed
    refine ⟨inside, i, ?_⟩
    by_cases h : cell0Lower i < p i
    · exact Or.inr (le_antisymm (bounds.2 i) (lower h))
    · exact Or.inl (le_antisymm (le_of_not_gt h) (bounds.1 i))
  · rintro ⟨inside, i, boundary⟩
    refine ⟨inside, ?_⟩
    intro interior
    have strict := interior i (mem_univ i)
    rcases boundary with atLower | atUpper
    · exact lt_irrefl _ (atLower ▸ strict.1)
    · exact lt_irrefl _ (atUpper ▸ strict.2)

theorem cell0_parameter_frontier_eq_six_faces :
    frontier (cellDomain 0) = ⋃ face : Face, cell0_parameterFace face := by
  ext p
  rw [cell0_mem_frontier_iff, mem_iUnion]
  constructor
  · rintro ⟨inside, i, lower | upper⟩
    · exact ⟨(i,false), (cell0_parameterFace_mem_iff _ p).mpr ⟨inside, lower⟩⟩
    · exact ⟨(i,true), (cell0_parameterFace_mem_iff _ p).mpr ⟨inside, upper⟩⟩
  · rintro ⟨⟨i, upper⟩, onFace⟩
    obtain ⟨inside, value⟩ := (cell0_parameterFace_mem_iff _ p).mp onFace
    refine ⟨inside, i, ?_⟩
    cases upper
    · exact Or.inl value
    · exact Or.inr value

theorem cell0_faceParameter_hasFDerivAt (face : Face) (p : FacePoint) :
    HasFDerivAt (cell0_faceParameter face) (faceInclusion face.1) p := by
  have identity : cell0_faceParameter face =
      fun y => Pi.single face.1 (cell0_faceCoordinate face) + faceInclusion face.1 y :=
    funext (fun y => insertNth_eq_affine face.1 (cell0_faceCoordinate face) y)
  rw [identity]
  convert! (hasFDerivAt_const (Pi.single face.1 (cell0_faceCoordinate face)) p).add
    (faceInclusion face.1).hasFDerivAt using 1
  simp only [zero_add]

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
