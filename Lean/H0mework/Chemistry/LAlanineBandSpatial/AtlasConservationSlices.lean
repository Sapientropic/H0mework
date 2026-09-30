import H0mework.Chemistry.LAlanineBandSpatial.AtlasConservationIntegrability
import H0mework.Chemistry.LAlanineBandSpatial.AtlasFaceTangents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter WholeBandConservation WholeCellBoundary Set MeasureTheory
noncomputable section

private theorem retime_map (c : FullBandCell) (p : Point) (s : Time) :
    sourceParameterMap c (retime p s) = TrueFlowDifferential.rawFlow (cellSeed c p) s := by
  change TrueFlowDifferential.rawFlow (cellSeed c (retime p s)) _ = _
  rw [retime_seed]
  rfl

private theorem retime_lower_cap (c : FullBandCell) (p : FacePoint) (s : Time) :
    retime (parameter c (2,false) p) s = (2 : Fin 3).insertNth s p := by
  ext i
  fin_cases i <;> rfl

theorem pullback_slice (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (p : FacePoint) (inside : p ∈ domain c 2) (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    laplacianPullback c ((2 : Fin 3).insertNth t p) = signedVolumeRate c (parameter c (2,false) p) t := by
  let s : Time := ⟨t,time⟩
  rw [← retime_lower_cap c p s,laplacianPullback]
  change LinearMap.det (trueJacobian c (retime (parameter c (2,false) p) s)).toLinearMap * _ = _
  rw [← LinearMap.det_toMatrix',← evolvingJacobian_eq_retimed c (fields c) (bounds c) _
    (parameter_mem c (2,false) p inside) s,retime_map]
  exact mul_comm _ _

theorem cap_flux_eq_evolving (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (p : FacePoint) (inside : p ∈ domain c 2) (above : Bool) :
    flux c (2,above) p = (if above then 1 else -1 : ℝ) *
      (evolvingJacobian c (parameter c (2,false) p) (if above then (1/2) else -(1/2))).det := by
  let s : Time := ⟨if above then (1/2) else -(1/2),by cases above <;> constructor <;> norm_num⟩
  have point : retime (parameter c (2,false) p) s = parameter c (2,above) p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · cases above <;> rfl
  rw [cap_flux_eq_oriented_det fields bounds c _ _ inside rfl]
  rw [show (if above then (1/2 : ℝ) else -(1/2)) = s from rfl,
    evolvingJacobian_eq_retimed c (fields c) (bounds c) _ (parameter_mem c (2,false) p inside) s,
    LinearMap.det_toMatrix',point]

theorem actual_slice_integral_eq_caps (fields : Fields) (bounds : Bounds) (c : FullBandCell)
    (p : FacePoint) (inside : p ∈ domain c 2) :
    (∫ t in Icc (-(1/2 : ℝ)) (1/2),laplacianPullback c ((2 : Fin 3).insertNth t p)) =
      flux c (2,true) p + flux c (2,false) p := by
  calc
    _ = ∫ t in (-(1/2 : ℝ))..(1/2),signedVolumeRate c (parameter c (2,false) p) t := by
      rw [intervalIntegral.integral_of_le (by norm_num),← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (pullback_slice fields bounds c p inside)
    _ = _ := by
      rw [actual_time_integral_eq_det_difference c (fields c) (bounds c) _ (parameter_mem c (2,false) p inside),
        cap_flux_eq_evolving fields bounds c p inside,cap_flux_eq_evolving fields bounds c p inside]
      simp only [Bool.false_eq_true,↓reduceIte,one_mul,neg_mul,sub_eq_add_neg]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
