import H0mework.Chemistry.LAlanineTrueFlowConservation.CalculusBoxFubini
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ConservationOrientedIntegral

/-! The actual spatial Laplacian integral is the sum of its original two oriented cap fluxes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData ContinuousGradient ContinuousSeed TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation WholeBandActual WholeBandGeometry WholeBandCell0Geometry WholeBandCell0Differential
open WholeBandCell0Continuation WholeBandCell0Spatial WholeBandCell0Boundary WholeCellBoundary
open Matrix Set MeasureTheory
noncomputable section

/-- The canonical derivative gives a total density; on the original face it is its actual flux. -/
def cell0_actualCapFlux (upper : Bool) (p : FacePoint) : ℝ :=
  (if upper then 1 else -1 : ℝ) * (cell0_actualDerivative (cell0_faceParameter (2, upper) p)).det

theorem cell0_actualCapFlux_eq_trueFaceFlux (upper : Bool) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain 2) : cell0_actualCapFlux upper p = cell0_trueFaceFlux (2, upper) p inside := by
  rw [cell0_trueCapFlux_eq_oriented_det _ _ _ rfl]
  unfold cell0_actualCapFlux
  have derivative := cell0_actualDerivative_eq_trueJacobian (cell0_trueFaceParameter (2, upper) p inside)
  simp only [cell0_trueFaceParameter] at derivative
  rw [derivative]
  rfl

def cell0_actualLaplacianPullback (p : Point) : ℝ :=
  (cell0_actualDerivative p).det * laplacian sourceTerms densityMatrix (cell0ParameterMap p)

theorem cell0_actualLaplacianPullback_integrable : IntegrableOn cell0_actualLaplacianPullback (cellDomain 0) := by
  have spatial : IntegrableOn (laplacian sourceTerms densityMatrix) cell0_truePatch :=
    (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn.integrableOn_compact
      cell0_truePatch_compact
  apply ((cell0_true_spatial_integrable_iff _).mp spatial).congr_fun _ cell0_domain_measurable
  intro p inside
  simp only [cell0_actualLaplacianPullback, abs_of_pos (cell0_actualDerivative_det_pos p inside), smul_eq_mul]

private theorem cell0_trueParameterMap_retime (p : Cell0Point) (s : Time) :
    cell0ParameterMap (cell0_retime p s).val = rawFlow (cellSeed 0 p.val) s := by
  change rawFlow (cellSeed 0 (cell0_retime p s).val) _ = _
  rw [cell0_retime_seed]
  rfl

private theorem cell0_capBase_lower (p : FacePoint) (inside : p ∈ cell0_faceDomain 2) :
    cell0_capBase (cell0_trueFaceParameter (2, false) p inside) = p := by
  funext i
  fin_cases i <;> rfl

private theorem cell0_pullback_slice (p : FacePoint) (inside : p ∈ cell0_faceDomain 2)
    (t : ℝ) (time : t ∈ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    cell0_actualLaplacianPullback ((2 : Fin 3).insertNth t p) =
      cell0_signedVolumeRate (cell0_trueFaceParameter (2, false) p inside) t := by
  let base := cell0_trueFaceParameter (2, false) p inside
  let s : Time := ⟨t, time⟩
  have point : (cell0_retime base s).val = (2 : Fin 3).insertNth t p := by
    ext i
    fin_cases i <;> rfl
  rw [← point, cell0_actualLaplacianPullback, cell0_actualDerivative_eq_trueJacobian (cell0_retime base s)]
  change LinearMap.det (cell0_trueJacobian (cell0_retime base s)).toLinearMap *
    laplacian sourceTerms densityMatrix (cell0ParameterMap (cell0_retime base s).val) = _
  rw [← LinearMap.det_toMatrix', ← cell0_evolvingJacobian_eq_retimed, cell0_trueParameterMap_retime]
  exact mul_comm _ _

private theorem cell0_fullLower_time : cell0Lower 2 = (-(1 / 2) : ℝ) := by
  rfl

private theorem cell0_fullUpper_time : cell0Upper 2 = (1 / 2 : ℝ) := by
  rfl

theorem cell0_actual_slice_integral_eq_caps (p : FacePoint) (inside : p ∈ cell0_faceDomain 2) :
    (∫ t in Icc (-(1 / 2) : ℝ) (1 / 2),
      cell0_actualLaplacianPullback ((2 : Fin 3).insertNth t p)) =
      cell0_actualCapFlux true p + cell0_actualCapFlux false p := by
  calc
    _ = ∫ t in (-(1 / 2) : ℝ)..(1 / 2),
        cell0_signedVolumeRate (cell0_trueFaceParameter (2, false) p inside) t := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Icc (cell0_pullback_slice p inside)
    _ = _ := by
      rw [cell0_actual_time_integral_eq_cap_flux, ← cell0_actualCapFlux_eq_trueFaceFlux,
        ← cell0_actualCapFlux_eq_trueFaceFlux, cell0_capBase_lower]

theorem cell0_actualCapFlux_sum_integrable :
    IntegrableOn (fun p => cell0_actualCapFlux true p + cell0_actualCapFlux false p) (cell0_faceDomain 2) := by
  have inner := _root_.LAlanineTrueFlowConservation.integrable_box_time
    cell0Lower cell0Upper cell0_actualLaplacianPullback
      (cell0_domain_eq_Icc ▸ cell0_actualLaplacianPullback_integrable)
  change IntegrableOn (fun p => ∫ t in Icc (cell0Lower 2) (cell0Upper 2),
    cell0_actualLaplacianPullback ((2 : Fin 3).insertNth t p)) (cell0_faceDomain 2) at inner
  rw [cell0_fullLower_time, cell0_fullUpper_time] at inner
  exact inner.congr_fun cell0_actual_slice_integral_eq_caps measurableSet_Icc

/-- The original source Laplacian on the true image equals its two actual oriented time-cap fluxes. -/
theorem cell0_true_spatial_laplacian_eq_cap_flux :
    (∫ x in cell0_truePatch, laplacian sourceTerms densityMatrix x) =
      ∫ p in cell0_faceDomain 2, cell0_actualCapFlux true p + cell0_actualCapFlux false p := by
  rw [cell0_true_spatial_integral_oriented]
  change (∫ p in cellDomain 0, cell0_actualLaplacianPullback p) = _
  rw [cell0_domain_eq_Icc]
  rw [_root_.LAlanineTrueFlowConservation.integral_box_time
    cell0Lower cell0Upper cell0_actualLaplacianPullback
      (cell0_domain_eq_Icc ▸ cell0_actualLaplacianPullback_integrable)]
  rw [cell0_fullLower_time, cell0_fullUpper_time]
  exact setIntegral_congr_fun measurableSet_Icc cell0_actual_slice_integral_eq_caps

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Conservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
