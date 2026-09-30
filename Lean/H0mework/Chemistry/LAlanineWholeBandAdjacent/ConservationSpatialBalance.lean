import H0mework.Chemistry.LAlanineWholeBandAdjacent.ConservationTangents
import H0mework.Chemistry.LAlanineTrueFlowConservation.CalculusBoxFubini

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData WholeBandGeometry WholeBandConservation
open WholeCellBoundary AdjacentFlow Set MeasureTheory
noncomputable section

def laplacianPullback (p : Point) : ℝ :=
  (jointJacobian p).det * laplacian sourceTerms densityMatrix (jointMap p)

theorem laplacianPullback_integrable : IntegrableOn laplacianPullback jointDomain := by
  apply ((joint_spatial_integrable_iff _).mp joint_laplacian_integrable).congr_fun _ joint_domain_measurable
  intro p inside
  simp only [laplacianPullback,abs_of_pos (jointJacobian_det_pos p inside),smul_eq_mul]

private theorem retime_map (p : Point) (s : Time) :
    jointMap (retime p s) = TrueFlowDifferential.rawFlow (cellSeed 0 p) s := by
  change TrueFlowDifferential.rawFlow (cellSeed 0 (retime p s)) _ = _
  rw [retime_seed]
  rfl

private theorem retime_lower_cap (p : FacePoint) (s : Time) :
    retime (faceParameter (2,false) p) s = (2 : Fin 3).insertNth s p := by
  ext i
  fin_cases i <;> rfl

private theorem pullback_slice (p : FacePoint) (inside : p ∈ faceDomain 2)
    (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    laplacianPullback ((2 : Fin 3).insertNth t p) = signedVolumeRate 0 (faceParameter (2,false) p) t := by
  let s : Time := ⟨t,time⟩
  rw [← retime_lower_cap p s,laplacianPullback]
  change LinearMap.det (jointJacobian (retime (faceParameter (2,false) p) s)).toLinearMap * _ = _
  rw [← LinearMap.det_toMatrix',← joint_evolvingJacobian_eq_retimed _ (faceParameter_mem (2,false) p inside) s,
    retime_map]
  exact mul_comm _ _

private theorem cap_flux_eq_evolving (p : FacePoint) (inside : p ∈ faceDomain 2) (above : Bool) :
    actualFaceFlux (2,above) p = (if above then 1 else -1 : ℝ) *
      (evolvingJacobian 0 (faceParameter (2,false) p) (if above then (1/2) else -(1/2))).det := by
  let s : Time := ⟨if above then (1/2) else -(1/2),by cases above <;> constructor <;> norm_num⟩
  have point : retime (faceParameter (2,false) p) s = faceParameter (2,above) p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · cases above <;> rfl
  rw [actualCapFlux_eq_oriented_det _ _ inside rfl]
  rw [show (if above then (1/2 : ℝ) else -(1/2)) = s from rfl,
    joint_evolvingJacobian_eq_retimed _ (faceParameter_mem (2,false) p inside) s,LinearMap.det_toMatrix',point]

theorem actual_slice_integral_eq_caps (p : FacePoint) (inside : p ∈ faceDomain 2) :
    (∫ t in Icc (-(1/2 : ℝ)) (1/2),laplacianPullback ((2 : Fin 3).insertNth t p)) =
      actualFaceFlux (2,true) p + actualFaceFlux (2,false) p := by
  calc
    _ = ∫ t in (-(1/2 : ℝ))..(1/2),signedVolumeRate 0 (faceParameter (2,false) p) t := by
      rw [intervalIntegral.integral_of_le (by norm_num),← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (pullback_slice p inside)
    _ = _ := by
      rw [joint_actual_time_integral _ (faceParameter_mem (2,false) p inside),
        cap_flux_eq_evolving p inside,cap_flux_eq_evolving p inside]
      simp only [Bool.false_eq_true,↓reduceIte,one_mul,neg_mul,sub_eq_add_neg]

theorem actualCapFlux_sum_integrable :
    IntegrableOn (fun p => actualFaceFlux (2,true) p + actualFaceFlux (2,false) p) (faceDomain 2) := by
  have inner := _root_.LAlanineTrueFlowConservation.integrable_box_time lower upper laplacianPullback
    (joint_domain_eq_Icc ▸ laplacianPullback_integrable)
  change IntegrableOn (fun p => ∫ t in Icc (-(1/2 : ℝ)) (1/2),laplacianPullback ((2 : Fin 3).insertNth t p)) (faceDomain 2) at inner
  exact inner.congr_fun actual_slice_integral_eq_caps measurableSet_Icc

theorem actual_spatial_laplacian_eq_cap_flux :
    (∫ x in jointImage,laplacian sourceTerms densityMatrix x) =
      ∫ p in faceDomain 2,actualFaceFlux (2,true) p + actualFaceFlux (2,false) p := by
  rw [joint_spatial_integral_commutes]
  have orientation : (∫ p in jointDomain,|(jointJacobian p).det| • laplacian sourceTerms densityMatrix (jointMap p)) =
      ∫ p in jointDomain,laplacianPullback p :=
    setIntegral_congr_fun joint_domain_measurable fun p inside => by
      simp only [laplacianPullback,abs_of_pos (jointJacobian_det_pos p inside),smul_eq_mul]
  rw [orientation,joint_domain_eq_Icc]
  change (∫ p in Icc lower upper,laplacianPullback p) = _
  rw [_root_.LAlanineTrueFlowConservation.integral_box_time lower upper laplacianPullback
    (joint_domain_eq_Icc ▸ laplacianPullback_integrable)]
  exact setIntegral_congr_fun measurableSet_Icc actual_slice_integral_eq_caps

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
