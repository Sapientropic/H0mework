import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Generator
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Strongly differentiable isometries act differentiably on genuine differentiable vectors. -/
set_option autoImplicit false
open Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem strong_isometry_product (U : ℝ → E ≃ₗᵢ[ℂ] E)
    (continuousU : ∀ v, Continuous (fun t => U t v)) (x : ℝ → E) (v d : E) (time : ℝ)
    (fixed : HasDerivAt (fun t => U t (x time)) d time) (curve : HasDerivAt x v time) :
    HasDerivAt (fun t => U t (x t)) (U time v+d) time := by
  have joint : Continuous (fun tv : ℝ × E => U tv.1 tv.2) :=
    continuous_prod_of_continuous_lipschitzWith' _ 1 (fun t => (U t).isometry.lipschitz) continuousU
  have pair : Tendsto (fun t => (t,slope x time t)) (𝓝[≠] time) (𝓝 (time,v)) := by
    rw [nhds_prod_eq]
    exact ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 time) (𝓝 time)).mono_left nhdsWithin_le_nhds).prodMk curve.tendsto_slope
  have moving : Tendsto (fun t => U t (slope x time t)) (𝓝[≠] time) (𝓝 (U time v)) := by
    have composed := (joint.tendsto (time,v)).comp pair
    simpa only [Function.comp_def] using! composed
  have decomposition (t : ℝ) :
      slope (fun s => U s (x s)) time t=U t (slope x time t)+slope (fun s => U s (x time)) time t := by
    simp only [slope_def_module,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,map_sub]
    module
  apply hasDerivAt_iff_tendsto_slope.mpr
  exact (moving.add fixed.tendsto_slope).congr (fun t => (decomposition t).symm)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
