import H0mework.Chemistry.LAlanineBandSpatial.AtlasFaceTangents
import H0mework.Chemistry.LAlanineBandContinuation.ConservationOrientation
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
open SourceGaussianModel WholeBandSource WholeBandContinuationParameter WholeBandConservation
open WholeCellBoundary WholeCellBoundary.Geometry WholeCellBoundaryArea Matrix
noncomputable section

theorem inclusion_injective (axis : Fin 3) : Function.Injective (faceInclusion axis) := by
  intro u v same
  have inserted : (axis.insertNth (0 : ℝ) u : Point) = axis.insertNth (0 : ℝ) v := by
    rw [insertNth_eq_affine,insertNth_eq_affine,same]
  exact (Fin.insertNth_inj.mp inserted).2

theorem derivative_injective (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) :
    Function.Injective (derivative c face u) :=
  (trueJacobian_injective c (fields c) (bounds c) (positive c) _ (parameter_mem c face u inside)).comp
    (inclusion_injective face.1)

theorem derivative_rank_two (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) :
    Module.finrank ℝ (LinearMap.range (derivative c face u).toLinearMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj (derivative_injective fields bounds positive c face u inside)]
  simp [FacePoint]

theorem tangents_independent (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) :
    LinearIndependent ℝ (tangent c face u) := by
  change LinearIndependent ℝ (fun k : Fin 2 => derivative c face u (Pi.single k 1))
  have mapped := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map_injOn
    (derivative c face u).toLinearMap (derivative_injective fields bounds positive c face u inside).injOn
  simpa only [tangent,Function.comp_def,Pi.basisFun_apply,ContinuousLinearMap.coe_coe] using mapped

theorem area_ne_zero (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (face : Face) (u : FacePoint) (inside : u ∈ domain c face.1) : orientedArea c face u ≠ 0 := by
  have cross : tangent c face u 0 ⨯₃ tangent c face u 1 ≠ 0 := by
    apply crossProduct_ne_zero_iff_linearIndependent.mpr
    have pair : ![tangent c face u 0,tangent c face u 1] = tangent c face u := by
      funext k
      fin_cases k <;> rfl
    rw [pair]
    exact tangents_independent fields bounds positive c face u inside
  apply smul_ne_zero _ cross
  apply mul_ne_zero _ (axisOrientation_nonzero face.1)
  cases face.2 <;> norm_num

theorem upper_cap_positive (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (u : FacePoint) (inside : u ∈ domain c 2) : 0 < flux c (2,true) u := by
  rw [cap_flux_eq_oriented_det fields bounds c _ _ inside rfl]
  simpa using actualJacobian_det_pos c (fields c) (bounds c) (positive c) _ (parameter_mem c (2,true) u inside)

theorem lower_cap_negative (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (u : FacePoint) (inside : u ∈ domain c 2) : flux c (2,false) u < 0 := by
  rw [cap_flux_eq_oriented_det fields bounds c _ _ inside rfl]
  simpa using neg_neg_of_pos (actualJacobian_det_pos c (fields c) (bounds c) (positive c) _ (parameter_mem c (2,false) u inside))

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
