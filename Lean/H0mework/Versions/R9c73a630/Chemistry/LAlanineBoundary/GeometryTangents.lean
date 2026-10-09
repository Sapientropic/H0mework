import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.SourceFaceBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Geometry

open SourceGaussianModel ContinuousParameterMap
open scoped BigOperators
noncomputable section

def faceInclusion (axis : Fin 3) : FacePoint →L[ℝ] Point :=
  ∑ k : Fin 2, (ContinuousLinearMap.proj k).smulRight (Pi.single (axis.succAbove k) 1)

theorem insertNth_eq_affine (axis : Fin 3) (constant : ℝ) (p : FacePoint) :
    axis.insertNth constant p = Pi.single axis constant + faceInclusion axis p := by
  funext i
  fin_cases axis <;> fin_cases i <;>
    simp [faceInclusion, Fin.sum_univ_two, Fin.insertNth, Fin.succAbove] <;> rfl

theorem faceInclusion_single (axis : Fin 3) (k : Fin 2) :
    faceInclusion axis (Pi.single k 1) = Pi.single (axis.succAbove k) 1 := by
  funext i
  fin_cases axis <;> fin_cases k <;> fin_cases i <;>
    simp [faceInclusion, Fin.sum_univ_two, Fin.succAbove]

theorem faceParameter_hasFDerivAt (face : Face) (p : FacePoint) :
    HasFDerivAt (faceParameter face) (faceInclusion face.1) p := by
  have identity : faceParameter face =
      fun y => Pi.single face.1 (faceCoordinate face) + faceInclusion face.1 y :=
    funext (fun y => insertNth_eq_affine face.1 (faceCoordinate face) y)
  rw [identity]
  convert!
    (hasFDerivAt_const (Pi.single face.1 (faceCoordinate face)) p).add
      (faceInclusion face.1).hasFDerivAt using 1
  simp only [zero_add]

def faceMap (face : Face) : FacePoint → Point := fun p => chart (faceParameter face p)
def faceDerivative (face : Face) (p : FacePoint) : FacePoint →L[ℝ] Point :=
  (parameterJacobian 0 4 (faceParameter face p)).comp (faceInclusion face.1)
def faceTangent (face : Face) (p : FacePoint) (k : Fin 2) : Point :=
  faceDerivative face p (Pi.single k 1)

theorem faceMap_hasFDerivAt (face : Face) (p : FacePoint) :
    HasFDerivAt (faceMap face) (faceDerivative face p) p :=
  (chart_hasFDerivAt (faceParameter face p)).comp p (faceParameter_hasFDerivAt face p)

theorem faceTangent_is_actual_derivative (face : Face) (p : FacePoint) (k : Fin 2) :
    faceTangent face p k = fderiv ℝ (faceMap face) p (Pi.single k 1) := by
  rw [(faceMap_hasFDerivAt face p).fderiv]
  rfl

theorem faceTangent_eq_column (face : Face) (p : FacePoint) (k : Fin 2) (i : Fin 3) :
    faceTangent face p k i = chartJacobian (faceParameter face p) i (face.1.succAbove k) := by
  simp only [faceTangent, faceDerivative, ContinuousLinearMap.comp_apply, faceInclusion_single]
  rw [chartJacobian_eq_derivative, (chart_hasFDerivAt (faceParameter face p)).fderiv]

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Geometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
