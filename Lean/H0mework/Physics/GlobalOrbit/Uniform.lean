import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! A direct Banach-space splice to Mathlib's existing uniform-time global
continuation consumer. No new ODE iteration or patching engine is defined. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open Set Metric Manifold
open scoped Topology Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem compactField_global (field : E → E) (smooth : ContDiff ℝ 1 field)
    (compact : HasCompactSupport field) (initial : E) :
    ∃ curve : ℝ → E, curve 0 = initial ∧ ∀ time, HasDerivAt curve (field (curve time)) time := by
  obtain ⟨K, lipschitz⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact smooth (by decide)
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuous smooth.continuous
  let L : NNReal := ⟨max bound 0, le_max_right _ _⟩
  let duration : ℝ := 1/((L : ℝ)+1)
  have positive : 0 < duration := by dsimp [duration]; positivity
  have uniform (start : E) : ∃ curve : ℝ → E, curve 0 = start ∧
      ∀ time ∈ Ioo (-duration) duration, HasDerivAt curve (field (curve time)) time := by
    have picard : IsPicardLindelof (fun _ => field) (tmin := -duration) (tmax := duration)
        ⟨0, by constructor <;> linarith⟩ start 1 0 L K := {
      lipschitzOnWith := fun _ _ => lipschitz.lipschitzOnWith
      continuousOn := fun _ _ => continuous_const.continuousOn
      norm_le := fun _ _ point _ => (bounded point).trans (le_max_left _ _)
      mul_max_le := by
        simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_zero, NNReal.coe_one]
        dsimp [duration]
        rw [mul_one_div]
        exact (div_le_one (by positivity)).mpr (by linarith) }
    obtain ⟨curve, starts, evolves⟩ := picard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨curve, starts, fun time inside => (evolves time (Ioo_subset_Icc_self inside)).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)⟩
  have manifoldSmooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 1
      (fun point => (⟨point, field point⟩ : TangentBundle (𝓘(ℝ, E)) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr smooth
  obtain ⟨curve, starts, evolves⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn
    (I := 𝓘(ℝ, E)) manifoldSmooth positive (fun start => by
      obtain ⟨curve, starts, evolves⟩ := uniform start
      refine ⟨curve, starts, fun time inside => ?_⟩
      exact (evolves time inside).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt) initial
  refine ⟨curve, starts, fun time => ?_⟩
  exact (evolves time).hasFDerivAt

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global
