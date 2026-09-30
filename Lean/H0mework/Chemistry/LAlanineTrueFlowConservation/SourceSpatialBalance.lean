import H0mework.Chemistry.LAlanineTrueFlowConservation.CalculusBoxFubini
import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceOrientedIntegral

/-! The actual spatial Laplacian integral is the sum of its original two oriented cap fluxes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient TrueFlowDifferential
open TrueFlowGeometry TrueFlowBoundary TrueTubeWholeActual WholeCellBoundary WholeCellPartition
open Set MeasureTheory
noncomputable section

/-- The canonical derivative gives a total density; on the original face it is its actual flux. -/
def actualCapFlux (upper : Bool) (p : FacePoint) : ℝ :=
  (if upper then 1 else -1 : ℝ) * (actualDerivative (faceParameter (2, upper) p)).det

theorem actualCapFlux_eq_trueFaceFlux (upper : Bool) (p : FacePoint)
    (inside : p ∈ faceDomain 2) : actualCapFlux upper p = trueFaceFlux (2, upper) p inside := by
  rw [trueCapFlux_eq_oriented_det _ _ _ rfl]
  unfold actualCapFlux
  have derivative := actualDerivative_eq_trueJacobian (trueFaceParameter (2, upper) p inside)
  simp only [trueFaceParameter] at derivative
  rw [derivative]
  rfl

def actualLaplacianPullback (p : Point) : ℝ :=
  (actualDerivative p).det * laplacian sourceTerms densityMatrix (trueParameterMap p)

theorem actualLaplacianPullback_integrable : IntegrableOn actualLaplacianPullback fullDomain := by
  have spatial : IntegrableOn (laplacian sourceTerms densityMatrix) truePatch :=
    (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn.integrableOn_compact
      truePatch_compact
  apply ((true_spatial_integrable_iff _).mp spatial).congr_fun _ full_measurable
  intro p inside
  simp only [actualLaplacianPullback, abs_of_pos (actualDerivative_det_pos p inside), smul_eq_mul]

private theorem trueParameterMap_retime (p : BandPoint) (s : Time) :
    trueParameterMap (retime p s).val = fullFlow p s := by
  change rawFlow (ContinuousParameterMap.initialMap 0 4 (retime p s).val) _ = _
  rw [retime_seed]
  rfl

private theorem capBase_lower (p : FacePoint) (inside : p ∈ faceDomain 2) :
    capBase (trueFaceParameter (2, false) p inside) = p := by
  funext i
  fin_cases i <;> rfl

private theorem pullback_slice (p : FacePoint) (inside : p ∈ faceDomain 2)
    (t : ℝ) (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    actualLaplacianPullback ((2 : Fin 3).insertNth t p) =
      signedVolumeRate (trueFaceParameter (2, false) p inside) t := by
  let base := trueFaceParameter (2, false) p inside
  let s : Time := ⟨t, time⟩
  have point : (retime base s).val = (2 : Fin 3).insertNth t p := by
    ext i
    fin_cases i <;> rfl
  rw [← point, actualLaplacianPullback, actualDerivative_eq_trueJacobian (retime base s)]
  change LinearMap.det (trueJacobian (retime base s)).toLinearMap *
    laplacian sourceTerms densityMatrix (trueParameterMap (retime base s).val) = _
  rw [← LinearMap.det_toMatrix', ← evolvingJacobian_eq_retimed, trueParameterMap_retime]
  exact mul_comm _ _

private theorem fullLower_time : fullLower 2 = (-(1 / 2) : ℝ) := by
  norm_num [fullLower, fullLowerQ, halfFlow_exact]

private theorem fullUpper_time : fullUpper 2 = (1 / 2 : ℝ) := by
  norm_num [fullUpper, fullUpperQ, halfFlow_exact]

theorem actual_slice_integral_eq_caps (p : FacePoint) (inside : p ∈ faceDomain 2) :
    (∫ t in Icc (-(1 / 2) : ℝ) (1 / 2),
      actualLaplacianPullback ((2 : Fin 3).insertNth t p)) =
      actualCapFlux true p + actualCapFlux false p := by
  calc
    _ = ∫ t in (-(1 / 2) : ℝ)..(1 / 2),
        signedVolumeRate (trueFaceParameter (2, false) p inside) t := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (pullback_slice p inside)
    _ = _ := by
      rw [actual_time_integral_eq_cap_flux, ← actualCapFlux_eq_trueFaceFlux,
        ← actualCapFlux_eq_trueFaceFlux, capBase_lower]

theorem actualCapFlux_sum_integrable :
    IntegrableOn (fun p => actualCapFlux true p + actualCapFlux false p) (faceDomain 2) := by
  have inner := _root_.LAlanineTrueFlowConservation.integrable_box_time
    fullLower fullUpper actualLaplacianPullback actualLaplacianPullback_integrable
  change IntegrableOn (fun p => ∫ t in Icc (fullLower 2) (fullUpper 2),
    actualLaplacianPullback ((2 : Fin 3).insertNth t p)) (faceDomain 2) at inner
  rw [fullLower_time, fullUpper_time] at inner
  exact inner.congr_fun actual_slice_integral_eq_caps measurableSet_Icc

/-- The original source Laplacian on the true image equals its two actual oriented time-cap fluxes. -/
theorem true_spatial_laplacian_eq_cap_flux :
    (∫ x in truePatch, laplacian sourceTerms densityMatrix x) =
      ∫ p in faceDomain 2, actualCapFlux true p + actualCapFlux false p := by
  rw [true_spatial_integral_oriented]
  change (∫ p in Icc fullLower fullUpper, actualLaplacianPullback p) = _
  rw [_root_.LAlanineTrueFlowConservation.integral_box_time
    fullLower fullUpper actualLaplacianPullback actualLaplacianPullback_integrable]
  rw [fullLower_time, fullUpper_time]
  exact setIntegral_congr_fun measurableSet_Icc actual_slice_integral_eq_caps

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
