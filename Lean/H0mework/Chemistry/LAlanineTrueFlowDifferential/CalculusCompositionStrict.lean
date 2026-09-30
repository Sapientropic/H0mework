import H0mework.Chemistry.LAlanineTrueFlowDifferential.CalculusPath
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace LAlanineTrueFlowDifferential

noncomputable section

def pathComp (g : Space → Space) (hg : ContDiff ℝ 1 g) (u : Path) : Path :=
  ⟨fun t => g (u t), hg.continuous.comp u.continuous⟩

def pathCompDerivField (g : Space → Space) (hg : ContDiff ℝ 1 g) (γ : Path) :
    C(Time, Space →L[ℝ] Space) :=
  ⟨fun t => fderiv ℝ g (γ t), (hg.continuous_fderiv (by norm_num)).comp γ.continuous⟩

def pathCompDerivLinear (g : Space → Space) (hg : ContDiff ℝ 1 g) (γ : Path) :
    Path →ₗ[ℝ] Path where
  toFun η := ⟨fun t => fderiv ℝ g (γ t) (η t),
    (pathCompDerivField g hg γ).continuous.clm_apply η.continuous⟩
  map_add' η ζ := by
    apply ContinuousMap.ext
    intro t
    exact (fderiv ℝ g (γ t)).map_add (η t) (ζ t)
  map_smul' a η := by
    apply ContinuousMap.ext
    intro t
    exact (fderiv ℝ g (γ t)).map_smul a (η t)

def pathCompDeriv (g : Space → Space) (hg : ContDiff ℝ 1 g) (γ : Path) :
    Path →L[ℝ] Path :=
  (pathCompDerivLinear g hg γ).mkContinuous ‖pathCompDerivField g hg γ‖ (by
    intro η
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    exact (fderiv ℝ g (γ t)).le_opNorm_of_le (η.norm_coe_le_norm t) |>.trans
      (mul_le_mul_of_nonneg_right
        ((pathCompDerivField g hg γ).norm_coe_le_norm t) (norm_nonneg η)))

@[simp] theorem pathCompDeriv_apply (g : Space → Space) (hg : ContDiff ℝ 1 g)
    (γ η : Path) (t : Time) :
    pathCompDeriv g hg γ η t = fderiv ℝ g (γ t) (η t) := rfl

theorem hasStrictFDerivAt_pathComp (g : Space → Space) (hg : ContDiff ℝ 1 g) (γ : Path) :
    HasStrictFDerivAt (pathComp g hg) (pathCompDeriv g hg γ) γ := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcompact : IsCompact (range γ) := isCompact_range γ.continuous
  have hu := hcompact.uniformContinuousAt_of_continuousAt (fderiv ℝ g)
    (fun _ _ => (hg.continuous_fderiv (by norm_num)).continuousAt)
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hbound⟩ := Metric.mem_uniformity_dist.mp hu
  refine Metric.eventually_nhds_iff_ball.mpr ⟨δ, hδ, ?_⟩
  rintro ⟨u, v⟩ huv
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at huv
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  change ‖g (u t) - g (v t) - fderiv ℝ g (γ t) (u t - v t)‖ ≤ ε * ‖u - v‖
  have hut : u t ∈ ball (γ t) δ := by
    exact (show ‖(u - γ) t‖ ≤ ‖u - γ‖ from (u - γ).norm_coe_le_norm t).trans_lt
      (by simpa [mem_ball, dist_eq_norm] using huv.1)
  have hvt : v t ∈ ball (γ t) δ := by
    exact (show ‖(v - γ) t‖ ≤ ‖v - γ‖ from (v - γ).norm_coe_le_norm t).trans_lt
      (by simpa [mem_ball, dist_eq_norm] using huv.2)
  have hrem := (convex_ball (γ t) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := g) (f' := fderiv ℝ g) (φ := fderiv ℝ g (γ t))
    (fun z _ => (hg.differentiable (by norm_num) z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => by
      have h := hbound (show dist (γ t) z < δ by simpa [dist_comm] using hz)
        (mem_range_self t)
      change dist (fderiv ℝ g (γ t)) (fderiv ℝ g z) < ε at h
      simpa [dist_eq_norm, norm_sub_rev] using h.le)
    hvt hut
  exact hrem.trans (mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm t) hε.le)

end

end LAlanineTrueFlowDifferential
