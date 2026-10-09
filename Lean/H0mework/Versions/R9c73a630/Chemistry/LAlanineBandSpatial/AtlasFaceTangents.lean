import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasFaceParameter
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ParameterColumns
import H0mework.Chemistry.LAlanineBoundary.GeometryAreaAlgebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
open SourceGaussianModel WholeBandSource WholeBandContinuation WholeBandContinuationParameter
open ContinuousGradient WholeCellBoundary WholeCellBoundary.Geometry WholeCellBoundaryArea Matrix Set
noncomputable section

def actualMap (c : FullBandCell) (face : Face) : FacePoint → Point := sourceParameterMap c ∘ parameter c face
def derivative (c : FullBandCell) (face : Face) (u : FacePoint) : FacePoint →L[ℝ] Point :=
  (trueJacobian c (parameter c face u)).comp (faceInclusion face.1)
def tangent (c : FullBandCell) (face : Face) (u : FacePoint) (k : Fin 2) : Point := derivative c face u (Pi.single k 1)

theorem actualMap_hasFDerivWithinAt (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) :
    HasFDerivWithinAt (actualMap c face) (derivative c face u) (domain c face.1) u :=
  (WholeBandContinuationParameter.actualMap_hasFDerivWithinAt c (fields c) (bounds c) _ (parameter_mem c face u inside)).comp u
    (parameter_hasFDerivAt c face u).hasFDerivWithinAt (parameter_mem c face)

theorem tangent_eq_column (c : FullBandCell) (face : Face) (u : FacePoint) (k : Fin 2) :
    tangent c face u k = trueJacobian c (parameter c face u) (Pi.single (face.1.succAbove k) 1) := by
  simp only [tangent,derivative,ContinuousLinearMap.comp_apply,faceInclusion_single]

def orientedArea (c : FullBandCell) (face : Face) (u : FacePoint) : Point :=
  ((if face.2 then 1 else -1 : ℝ) * axisOrientation face.1) • (tangent c face u 0 ⨯₃ tangent c face u 1)
def flux (c : FullBandCell) (face : Face) (u : FacePoint) : ℝ :=
  sourceGradient (actualMap c face u) ⬝ᵥ orientedArea c face u

theorem side_tangent_is_gradient (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) (side : face.1 ≠ 2) :
    tangent c face u 1 = sourceGradient (actualMap c face u) := by
  have timeAxis : face.1.succAbove (1 : Fin 2) = 2 := by
    rcases face with ⟨axis,above⟩
    fin_cases axis
    · rfl
    · rfl
    · exact False.elim (side rfl)
  rw [tangent_eq_column,timeAxis]
  exact trueJacobian_time_column c (fields c) (bounds c) _ (parameter_mem c face u inside)

theorem side_flux_zero (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) (side : face.1 ≠ 2) : flux c face u = 0 := by
  rw [flux,orientedArea,← side_tangent_is_gradient fields bounds c face u inside side,
    dotProduct_smul,dot_cross_self,smul_zero]

theorem area_eq_adjugate (c : FullBandCell) (face : Face) (u : FacePoint) :
    orientedArea c face u = (if face.2 then 1 else -1 : ℝ) •
      (LinearMap.toMatrix' (trueJacobian c (parameter c face u)).toLinearMap).adjugate face.1 := by
  let m := LinearMap.toMatrix' (trueJacobian c (parameter c face u)).toLinearMap
  have first : m.col (face.1.succAbove 0) = tangent c face u 0 := by rw [tangent_eq_column]; rfl
  have second : m.col (face.1.succAbove 1) = tangent c face u 1 := by rw [tangent_eq_column]; rfl
  change orientedArea c face u = (if face.2 then 1 else -1 : ℝ) • m.adjugate face.1
  rw [adjugate_row_cross,first,second,smul_smul]
  rfl

theorem cap_flux_eq_oriented_det (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) (cap : face.1 = 2) :
    flux c face u = (if face.2 then 1 else -1 : ℝ) * (trueJacobian c (parameter c face u)).det := by
  let m := LinearMap.toMatrix' (trueJacobian c (parameter c face u)).toLinearMap
  have gradient : sourceGradient (actualMap c face u) = m.col face.1 := by
    rw [cap]
    exact (trueJacobian_time_column c (fields c) (bounds c) _ (parameter_mem c face u inside)).symm
  rw [flux,area_eq_adjugate,gradient]
  change m.col face.1 ⬝ᵥ ((if face.2 then 1 else -1 : ℝ) • m.adjugate face.1) = _
  rw [dotProduct_smul,transverse_dot_adjugate]
  exact congrArg (fun r : ℝ => (if face.2 then 1 else -1 : ℝ)*r)
    (LinearMap.det_toMatrix' (trueJacobian c (parameter c face u)).toLinearMap)

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
