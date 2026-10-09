import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasImages
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.GeometryTangents

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuationParameter
open WholeCellBoundary WholeCellBoundary.Geometry Set
noncomputable section

def domain (c : FullBandCell) (axis : Fin 3) : Set FacePoint :=
  Icc (cellLower c ∘ axis.succAbove) (cellUpper c ∘ axis.succAbove)
def coordinate (c : FullBandCell) (face : Face) : ℝ := if face.2 then cellUpper c face.1 else cellLower c face.1
def parameter (c : FullBandCell) (face : Face) (u : FacePoint) : Point := face.1.insertNth (coordinate c face) u

theorem domain_nonempty (c : FullBandCell) (axis : Fin 3) : (domain c axis).Nonempty :=
  ⟨cellLower c ∘ axis.succAbove,le_rfl,fun j => (axis_strict c (axis.succAbove j)).le⟩

theorem coordinate_bounds (c : FullBandCell) (face : Face) :
    cellLower c face.1 ≤ coordinate c face ∧ coordinate c face ≤ cellUpper c face.1 := by
  have ordered := (axis_strict c face.1).le
  cases face with
  | mk axis above => cases above <;> exact ⟨by first | exact le_rfl | exact ordered,
      by first | exact le_rfl | exact ordered⟩

theorem parameter_mem (c : FullBandCell) (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) :
    parameter c face u ∈ cellDomain c :=
  (domain_eq_Icc c).symm.subset
    ⟨Fin.le_insertNth_iff.mpr ⟨(coordinate_bounds c face).1,inside.1⟩,
      Fin.insertNth_le_iff.mpr ⟨(coordinate_bounds c face).2,inside.2⟩⟩

theorem parameter_hasFDerivAt (c : FullBandCell) (face : Face) (u : FacePoint) :
    HasFDerivAt (parameter c face) (faceInclusion face.1) u := by
  have identity : parameter c face = fun v => Pi.single face.1 (coordinate c face) + faceInclusion face.1 v :=
    funext (fun v => insertNth_eq_affine face.1 (coordinate c face) v)
  rw [identity]
  convert! (hasFDerivAt_const (Pi.single face.1 (coordinate c face)) u).add (faceInclusion face.1).hasFDerivAt using 1
  simp only [zero_add]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
