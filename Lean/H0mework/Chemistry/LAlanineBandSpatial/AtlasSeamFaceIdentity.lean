import H0mework.Chemistry.LAlanineBandSpatial.AtlasSeamArea
import H0mework.Chemistry.LAlanineBandSpatial.AtlasFaceTangents

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
open SourceGaussianModel WholeBandContinuationParameter WholeCellBoundary WholeCellBoundaryArea
noncomputable section

theorem left_face_domain (s : Seam) : Faces.domain (leftCell s) 1 = domain := by
  unfold Faces.domain domain
  congr 1 <;> funext i <;> fin_cases i <;> rfl
theorem right_face_domain (s : Seam) : Faces.domain (rightCell s) 1 = domain := by
  unfold Faces.domain domain
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem left_face_parameter (s : Seam) (u : FacePoint) : Faces.parameter (leftCell s) (1,true) u = parameter s u := rfl
theorem right_face_parameter (s : Seam) (u : FacePoint) : Faces.parameter (rightCell s) (1,false) u = parameter s u := by
  change ((1 : Fin 3).insertNth (WholeBandSource.cellV (rightCell s) 0 : ℝ) u : Point) = _
  rw [← original_coordinate]
  rfl

theorem left_face_derivative (s : Seam) (u : FacePoint) : Faces.derivative (leftCell s) (1,true) u = leftDerivative s u := rfl
theorem right_face_derivative (s : Seam) (u : FacePoint) : Faces.derivative (rightCell s) (1,false) u = rightDerivative s u := by
  rw [Faces.derivative,right_face_parameter]
  rfl

theorem left_face_area (s : Seam) (u : FacePoint) : Faces.orientedArea (leftCell s) (1,true) u = leftArea s u := by
  simp only [Faces.orientedArea,Faces.tangent,left_face_derivative]
  norm_num [axisOrientation,leftArea]

theorem right_face_area (s : Seam) (u : FacePoint) : Faces.orientedArea (rightCell s) (1,false) u = rightArea s u := by
  simp only [Faces.orientedArea,Faces.tangent,right_face_derivative]
  norm_num [axisOrientation,rightArea]

theorem actual_face_area_cancellation (fields : Fields) (bounds : Bounds) (s : Seam)
    (u : FacePoint) (inside : u ∈ domain) :
    Faces.orientedArea (leftCell s) (1,true) u + Faces.orientedArea (rightCell s) (1,false) u = 0 := by
  rw [left_face_area,right_face_area]
  exact actual_area_cancellation fields bounds s u inside

theorem actual_face_flux_cancellation (fields : Fields) (bounds : Bounds) (s : Seam)
    (u : FacePoint) (inside : u ∈ domain) :
    Faces.flux (leftCell s) (1,true) u + Faces.flux (rightCell s) (1,false) u = 0 := by
  have left : Faces.flux (leftCell s) (1,true) u = leftFlux s u := by
    rw [Faces.flux,Faces.actualMap,Function.comp_apply,left_face_parameter,left_face_area]
    rfl
  have right : Faces.flux (rightCell s) (1,false) u = rightFlux s u := by
    rw [Faces.flux,Faces.actualMap,Function.comp_apply,right_face_parameter,right_face_area]
    rfl
  rw [left,right]
  exact actual_flux_cancellation fields bounds s u inside

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
