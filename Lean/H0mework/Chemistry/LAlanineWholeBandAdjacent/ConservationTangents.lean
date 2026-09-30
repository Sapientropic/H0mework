import H0mework.Chemistry.LAlanineWholeBandAdjacent.ConservationParameterFaces
import H0mework.Chemistry.LAlanineBoundary.GeometryAreaAlgebra

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open SourceGaussianModel ContinuousGradient WholeCellBoundary WholeCellBoundary.Geometry
open WholeCellBoundaryArea AdjacentFlow Matrix Set
open scoped Matrix
noncomputable section

def actualFaceMap (face : Face) : FacePoint → Point := jointMap ∘ faceParameter face
def actualFaceDerivative (face : Face) (p : FacePoint) : FacePoint →L[ℝ] Point :=
  (jointJacobian (faceParameter face p)).comp (faceInclusion face.1)

theorem actualFaceMap_hasFDerivWithinAt (face : Face) (p : FacePoint) :
    HasFDerivWithinAt (actualFaceMap face) (actualFaceDerivative face p) (faceDomain face.1) p :=
  (jointMap_hasFDerivWithinAt (faceParameter face p)).comp p
    (faceParameter_hasFDerivAt face p).hasFDerivWithinAt (faceParameter_mem face)

def actualFaceTangent (face : Face) (p : FacePoint) (k : Fin 2) : Point :=
  actualFaceDerivative face p (Pi.single k 1)

theorem actualFaceTangent_eq_column (face : Face) (p : FacePoint) (k : Fin 2) :
    actualFaceTangent face p k = jointJacobian (faceParameter face p) (Pi.single (face.1.succAbove k) 1) := by
  simp only [actualFaceTangent,actualFaceDerivative,ContinuousLinearMap.comp_apply,faceInclusion_single]

def actualOrientedArea (face : Face) (p : FacePoint) : Point :=
  ((if face.2 then 1 else -1 : ℝ) * axisOrientation face.1) •
    (actualFaceTangent face p 0 ⨯₃ actualFaceTangent face p 1)

def actualFaceFlux (face : Face) (p : FacePoint) : ℝ :=
  sourceGradient (actualFaceMap face p) ⬝ᵥ actualOrientedArea face p

theorem actualSideTangent_is_gradient (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) :
    actualFaceTangent face p 1 = sourceGradient (actualFaceMap face p) := by
  have timeAxis : face.1.succAbove (1 : Fin 2) = 2 := by
    rcases face with ⟨axis,upper⟩
    fin_cases axis
    · rfl
    · rfl
    · exact False.elim (side rfl)
  rw [actualFaceTangent_eq_column,timeAxis]
  exact jointJacobian_time_column _ (faceParameter_mem face p inside)

theorem actualSideFlux_zero (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) : actualFaceFlux face p = 0 := by
  rw [actualFaceFlux,actualOrientedArea,← actualSideTangent_is_gradient face p inside side,
    dotProduct_smul,dot_cross_self,smul_zero]

theorem actualOrientedArea_eq_adjugate (face : Face) (p : FacePoint) :
    actualOrientedArea face p = (if face.2 then 1 else -1 : ℝ) •
      (LinearMap.toMatrix' (jointJacobian (faceParameter face p)).toLinearMap).adjugate face.1 := by
  let m := LinearMap.toMatrix' (jointJacobian (faceParameter face p)).toLinearMap
  have first : m.col (face.1.succAbove 0) = actualFaceTangent face p 0 := by rw [actualFaceTangent_eq_column]; rfl
  have second : m.col (face.1.succAbove 1) = actualFaceTangent face p 1 := by rw [actualFaceTangent_eq_column]; rfl
  change actualOrientedArea face p = (if face.2 then 1 else -1 : ℝ) • m.adjugate face.1
  rw [adjugate_row_cross,first,second,smul_smul]
  rfl

theorem actualCapFlux_eq_oriented_det (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (cap : face.1 = 2) :
    actualFaceFlux face p = (if face.2 then 1 else -1 : ℝ) * (jointJacobian (faceParameter face p)).det := by
  let m := LinearMap.toMatrix' (jointJacobian (faceParameter face p)).toLinearMap
  have gradient : sourceGradient (actualFaceMap face p) = m.col face.1 := by
    rw [cap]
    exact (jointJacobian_time_column _ (faceParameter_mem face p inside)).symm
  rw [actualFaceFlux,actualOrientedArea_eq_adjugate,gradient]
  change m.col face.1 ⬝ᵥ ((if face.2 then 1 else -1 : ℝ) • m.adjugate face.1) = _
  rw [dotProduct_smul,transverse_dot_adjugate]
  exact congrArg (fun r : ℝ => (if face.2 then 1 else -1 : ℝ) * r)
    (LinearMap.det_toMatrix' (jointJacobian (faceParameter face p)).toLinearMap)

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
