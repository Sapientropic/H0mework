import H0mework.Chemistry.LAlanineBoundary.GeometryTangents
import H0mework.Chemistry.LAlanineBoundary.GeometryAreaAlgebra
import H0mework.Chemistry.LAlanineWholeCell.SpatialProducer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellBoundary.Geometry

open SourceGaussianModel ContinuousGradient WholeCellSpatial WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

def sideOrientation (face : Face) : ℝ := if face.2 then 1 else -1
def orientedAreaVector (face : Face) (p : FacePoint) (j : Fin 3) : ℝ :=
  sideOrientation face * (chartJacobian (faceParameter face p)).adjugate face.1 j

theorem sideOrientation_nonzero (face : Face) : sideOrientation face ≠ 0 := by
  cases face with
  | mk axis upper => cases upper <;> norm_num [sideOrientation]

theorem orientedAreaVector_eq_row (face : Face) (p : FacePoint) :
    orientedAreaVector face p = sideOrientation face • (chartJacobian (faceParameter face p)).adjugate face.1 := rfl

/-- The missing-axis parity is essential for the increasing-order Fin.succAbove chart. -/
theorem orientedAreaVector_eq_cross (face : Face) (p : FacePoint) :
    orientedAreaVector face p = (sideOrientation face * axisOrientation face.1) •
      (faceTangent face p 0 ⨯₃ faceTangent face p 1) := by
  have first : (chartJacobian (faceParameter face p)).col (face.1.succAbove 0) = faceTangent face p 0 :=
    funext (fun i => (faceTangent_eq_column face p 0 i).symm)
  have second : (chartJacobian (faceParameter face p)).col (face.1.succAbove 1) = faceTangent face p 1 :=
    funext (fun i => (faceTangent_eq_column face p 1 i).symm)
  rw [orientedAreaVector_eq_row, adjugate_row_cross, first, second, smul_smul]

theorem first_tangent_perpendicular (face : Face) (p : FacePoint) :
    faceTangent face p 0 ⬝ᵥ orientedAreaVector face p = 0 := by
  rw [orientedAreaVector_eq_cross, dotProduct_smul, dot_self_cross, smul_zero]

theorem second_tangent_perpendicular (face : Face) (p : FacePoint) :
    faceTangent face p 1 ⬝ᵥ orientedAreaVector face p = 0 := by
  rw [orientedAreaVector_eq_cross, dotProduct_smul, dot_cross_self, smul_zero]

theorem transverse_dot_area (face : Face) (p : FacePoint) :
    (chartJacobian (faceParameter face p)).col face.1 ⬝ᵥ orientedAreaVector face p =
      sideOrientation face * (chartJacobian (faceParameter face p)).det := by
  rw [orientedAreaVector_eq_row, dotProduct_smul, transverse_dot_adjugate]
  rfl

theorem faceFlux_eq_gradient_dot_area (face : Face) (p : FacePoint) :
    faceFlux face p = sourceGradient (chart (faceParameter face p)) ⬝ᵥ orientedAreaVector face p := by
  rw [orientedAreaVector_eq_row, dotProduct_smul, dotProduct_comm]
  cases face with
  | mk axis upper => cases upper <;> simp [faceFlux, sideOrientation, pulledFlux, mulVec]

theorem orientedAreaVector_nonzero (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    orientedAreaVector face p ≠ 0 := by
  have positive : 0 < (chartJacobian (faceParameter face p)).det :=
    sourceGeneratedWholeCellClosure.jacobianPositive _ (faceParameter_mem face p inside)
  intro zero
  have scale := transverse_dot_area face p
  rw [zero, dotProduct_zero] at scale
  exact (mul_ne_zero (sideOrientation_nonzero face) (ne_of_gt positive)) scale.symm

theorem middle_face_unsigned_cross_rejected (p : FacePoint) (inside : p ∈ faceDomain 1) :
    orientedAreaVector (1, true) p ≠ faceTangent (1, true) p 0 ⨯₃ faceTangent (1, true) p 1 := by
  have reversed : orientedAreaVector (1, true) p =
      -(faceTangent (1, true) p 0 ⨯₃ faceTangent (1, true) p 1) := by
    simpa [sideOrientation, axisOrientation] using orientedAreaVector_eq_cross (1, true) p
  intro wrong
  apply orientedAreaVector_nonzero (1, true) p inside
  funext j
  have first := congrFun reversed j
  have second := congrFun wrong j
  change orientedAreaVector (1, true) p j =
    -((faceTangent (1, true) p 0 ⨯₃ faceTangent (1, true) p 1) j) at first
  change orientedAreaVector (1, true) p j = 0
  linarith only [first, second]

end
end LAlanine40K2025.BasinRefinement.WholeCellBoundary.Geometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
