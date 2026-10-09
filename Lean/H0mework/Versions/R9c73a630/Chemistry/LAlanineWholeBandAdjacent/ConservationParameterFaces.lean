import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationDynamics
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.GeometryTangents

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuationParameter
open WholeBandAdjacentGeometry WholeCellBoundary WholeCellBoundary.Geometry AdjacentFlow Set
noncomputable section

def lower : Point := cellLower 0
def upper : Point := cellUpper 1

theorem axis_strict (i : Fin 3) : lower i < upper i := by
  fin_cases i
  · change (0 : ℝ) < 1; norm_num
  · change (cellV 0 0 : ℝ) < cellV 1 1
    have left : (cellV 0 0 : ℝ) < cellV 0 1 := Rat.cast_lt.mpr (source_cells_in_segments 0).2.1
    have right : (cellV 1 0 : ℝ) < cellV 1 1 := Rat.cast_lt.mpr (source_cells_in_segments 1).2.1
    rw [← cell0_cell1_literal_seam] at right
    exact left.trans right
  · change (-(1/2) : ℝ) < 1/2; norm_num

def faceDomain (axis : Fin 3) : Set FacePoint := Icc (lower ∘ axis.succAbove) (upper ∘ axis.succAbove)
def faceCoordinate (face : Face) : ℝ := if face.2 then upper face.1 else lower face.1
def faceParameter (face : Face) (p : FacePoint) : Point := face.1.insertNth (faceCoordinate face) p
def parameterFace (face : Face) : Set Point := faceParameter face '' faceDomain face.1

theorem faceDomain_nonempty (axis : Fin 3) : (faceDomain axis).Nonempty :=
  ⟨lower ∘ axis.succAbove,le_rfl,fun j => (axis_strict (axis.succAbove j)).le⟩

theorem faceCoordinate_bounds (face : Face) : lower face.1 ≤ faceCoordinate face ∧ faceCoordinate face ≤ upper face.1 := by
  have ordered := (axis_strict face.1).le
  cases face with
  | mk axis upper => cases upper <;> exact ⟨by first | exact le_rfl | exact ordered,
      by first | exact le_rfl | exact ordered⟩

theorem faceParameter_mem (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    faceParameter face p ∈ jointDomain :=
  joint_domain_eq_Icc.symm.subset
    ⟨Fin.le_insertNth_iff.mpr ⟨(faceCoordinate_bounds face).1,inside.1⟩,
      Fin.insertNth_le_iff.mpr ⟨(faceCoordinate_bounds face).2,inside.2⟩⟩

theorem faceParameter_axis (face : Face) (p : FacePoint) :
    faceParameter face p face.1 = faceCoordinate face := Fin.insertNth_apply_same _ _ _

theorem parameterFace_mem_iff (face : Face) (p : Point) :
    p ∈ parameterFace face ↔ p ∈ jointDomain ∧ p face.1 = faceCoordinate face := by
  constructor
  · rintro ⟨y,inside,rfl⟩
    exact ⟨faceParameter_mem face y inside,faceParameter_axis face y⟩
  · rintro ⟨inside,onFace⟩
    have bounds : p ∈ Icc lower upper := joint_domain_eq_Icc ▸ inside
    refine ⟨Fin.removeNth face.1 p,⟨fun j => bounds.1 (face.1.succAbove j),fun j => bounds.2 (face.1.succAbove j)⟩,?_⟩
    rw [faceParameter,← onFace]
    exact Fin.insertNth_self_removeNth face.1 p

theorem faceParameter_hasFDerivAt (face : Face) (p : FacePoint) :
    HasFDerivAt (faceParameter face) (faceInclusion face.1) p := by
  have identity : faceParameter face = fun y => Pi.single face.1 (faceCoordinate face) + faceInclusion face.1 y :=
    funext (fun y => insertNth_eq_affine face.1 (faceCoordinate face) y)
  rw [identity]
  convert! (hasFDerivAt_const (Pi.single face.1 (faceCoordinate face)) p).add (faceInclusion face.1).hasFDerivAt using 1
  simp only [zero_add]

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
