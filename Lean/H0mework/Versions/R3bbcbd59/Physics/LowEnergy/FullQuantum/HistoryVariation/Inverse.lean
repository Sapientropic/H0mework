import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.IntegralOperator

/-! A genuine strong inverse derivative uses joint continuity, with no operator-norm derivative assumption. -/
set_option autoImplicit false
open Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem strong_inverse_derivative (U V : ℝ → E →L[ℂ] E)
    (left : ∀ t x, V t (U t x)=x) (right : ∀ t x, U t (V t x)=x)
    (joint : Continuous (fun tx : ℝ × E => V tx.1 tx.2))
    (time : ℝ) (v d : E) (fixed : HasDerivAt (fun t => U t (V time v)) d time) :
    HasDerivAt (fun t => V t v) (-V time d) time := by
  have pair : Tendsto (fun t => (t,slope (fun s => U s (V time v)) time t))
      (𝓝[≠] time) (𝓝 (time,d)) := by
    rw [nhds_prod_eq]
    exact ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 time) (𝓝 time)).mono_left nhdsWithin_le_nhds).prodMk
      fixed.tendsto_slope
  have limit : Tendsto (fun t => -V t (slope (fun s => U s (V time v)) time t))
      (𝓝[≠] time) (𝓝 (-V time d)) := by
    have composed := ((joint.tendsto (time,d)).comp pair).neg
    simpa only [Function.comp_def] using! composed
  have decomposition (t : ℝ) : slope (fun s => V s v) time t=
      -V t (slope (fun s => U s (V time v)) time t) := by
    simp only [slope_def_module,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,map_sub,left,right]
    module
  apply hasDerivAt_iff_tendsto_slope.mpr
  exact limit.congr (fun t => (decomposition t).symm)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
