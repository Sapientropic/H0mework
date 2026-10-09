import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.FlowRetention

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient Set Metric Filter
open scoped NNReal Topology
noncomputable section

def attractionRate (alpha : ℝ) (k : ℝ≥0) : ℝ := (1 - (k : ℝ)) / alpha

theorem attractionRate_positive (alpha : ℝ) (k : ℝ≥0) (alphaPositive : 0 < alpha) (contractive : k < 1) :
    0 < attractionRate alpha k := by
  apply div_pos _ alphaPositive
  have hk : (k : ℝ) < 1 := by exact_mod_cast contractive
  linarith

theorem flow_exponential_bound (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (alphaPositive : 0 < alpha) (contractive : k < 1)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (q : ℝ) (qPositive : 0 < q)
    (fits : q + dist zero.point centre ≤ radius)
    (initial : Point) (initialInside : dist initial zero.point ≤ q) (t : ℝ) (nonnegative : 0 ≤ t) :
    dist (GlobalSource.flow initial t) zero.point ≤
      dist initial zero.point * Real.exp (-attractionRate alpha k * t) := by
  have growth := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := weightedFlow zero.point initial alpha) (f' := weightedDerivative zero.point initial alpha)
    (δ := dist initial zero.point) (K := (k : ℝ) / alpha) (ε := 0) (a := 0) (b := t)
    (weighted_continuous zero.point initial alpha alphaPositive).continuousOn
    (fun s _ => (weighted_hasDerivAt zero.point initial alpha alphaPositive s).hasDerivWithinAt)
    (by simp [weighted_norm, GlobalSource.flow_starts, weight])
    (fun s hs => by
      simpa only [add_zero] using weightedDerivative_norm_bound centre radius alpha k alphaPositive
        derivativeBound zero initial s
        (flow_retained_in_source centre radius alpha k alphaPositive contractive derivativeBound
          zero q qPositive fits initial initialInside s hs.1))
    t ⟨nonnegative,le_rfl⟩
  rw [gronwallBound_ε0, sub_zero, weighted_norm] at growth
  calc
    dist (GlobalSource.flow initial t) zero.point ≤
        (dist initial zero.point * Real.exp ((k : ℝ) / alpha * t)) / weight alpha t := by
      apply (le_div_iff₀ (weight_positive alpha t)).mpr
      simpa only [mul_comm] using growth
    _ = _ := by
      rw [weight, mul_div_assoc, ← Real.exp_sub]
      congr 2
      unfold attractionRate
      ring

theorem flow_converges (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (alphaPositive : 0 < alpha) (contractive : k < 1)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (q : ℝ) (qPositive : 0 < q)
    (fits : q + dist zero.point centre ≤ radius)
    (initial : Point) (initialInside : dist initial zero.point ≤ q) :
    Tendsto (GlobalSource.flow initial) atTop (𝓝 zero.point) := by
  have exponential : Tendsto (fun t : ℝ => Real.exp (-attractionRate alpha k * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (attractionRate_positive alpha k alphaPositive contractive)))
  have tail : Tendsto (fun t : ℝ => dist initial zero.point * Real.exp (-attractionRate alpha k * t))
      atTop (𝓝 0) := by simpa only [mul_zero] using exponential.const_mul (dist initial zero.point)
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have small := tail.eventually (Iio_mem_nhds positive)
  filter_upwards [eventually_ge_atTop (0 : ℝ),small] with t ht hsmall
  exact (flow_exponential_bound centre radius alpha k alphaPositive contractive derivativeBound
    zero q qPositive fits initial initialInside t ht).trans_lt hsmall

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
