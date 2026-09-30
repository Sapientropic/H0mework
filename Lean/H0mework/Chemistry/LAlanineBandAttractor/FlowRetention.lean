import H0mework.Chemistry.LAlanineBandAttractor.FlowWeighted

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient Set Metric Filter
open scoped NNReal Topology
noncomputable section

/-- Fencing the original differentiable curve pays forward retention before any Gronwall use. -/
theorem flow_retained (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (alphaPositive : 0 < alpha) (contractive : k < 1)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (q : ℝ) (qPositive : 0 < q)
    (fits : q + dist zero.point centre ≤ radius)
    (initial : Point) (initialInside : dist initial zero.point ≤ q) (t : ℝ) (nonnegative : 0 ≤ t) :
    dist (GlobalSource.flow initial t) zero.point ≤ q := by
  have barrier (s : ℝ) : HasDerivAt (fun u => q * weight alpha u) (q * weight alpha s / alpha) s := by
    convert! (weight_hasDerivAt alpha s).const_mul q using 1
    ring
  have fence := image_le_of_liminf_slope_right_lt_deriv_boundary
    (f := fun s => ‖weightedFlow zero.point initial alpha s‖)
    (f' := fun s => ‖weightedDerivative zero.point initial alpha s‖)
    (a := 0) (b := t)
    (continuous_norm.comp_continuousOn (weighted_continuous zero.point initial alpha alphaPositive).continuousOn)
    (fun s _ r hr => ((weighted_hasDerivAt zero.point initial alpha alphaPositive s).hasDerivWithinAt
      (s := Ici s)).liminf_right_slope_norm_le hr)
    (B := fun s => q * weight alpha s) (B' := fun s => q * weight alpha s / alpha)
    (by
      rw [weighted_norm, GlobalSource.flow_starts]
      simpa only [mul_comm q] using mul_le_mul_of_nonneg_left initialInside (weight_positive alpha 0).le)
    barrier
    (fun s _ contact => ?_)
  · have bound := fence (show t ∈ Icc (0 : ℝ) t from ⟨nonnegative,le_rfl⟩)
    rw [weighted_norm] at bound
    apply (mul_le_mul_iff_right₀ (weight_positive alpha t)).mp
    simpa only [mul_comm q] using bound
  have onSphere : dist (GlobalSource.flow initial s) zero.point = q := by
    rw [weighted_norm] at contact
    apply mul_left_cancel₀ (weight_positive alpha s).ne'
    simpa only [mul_comm q] using contact
  have inside : GlobalSource.flow initial s ∈ closedBall centre radius := by
    apply mem_closedBall.mpr
    exact (dist_triangle _ zero.point centre).trans (by rw [onSphere]; exact fits)
  calc
    ‖weightedDerivative zero.point initial alpha s‖ ≤
        ((k : ℝ) / alpha) * ‖weightedFlow zero.point initial alpha s‖ :=
      weightedDerivative_norm_bound centre radius alpha k alphaPositive derivativeBound zero initial s inside
    _ = ((k : ℝ) / alpha) * (q * weight alpha s) := by rw [contact]
    _ < q * weight alpha s / alpha := by
      have hk : (k : ℝ) < 1 := by exact_mod_cast contractive
      have h := mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hk alphaPositive)
        (mul_pos qPositive (weight_positive alpha s))
      convert! h using 1
      ring

theorem flow_retained_in_source (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (alphaPositive : 0 < alpha) (contractive : k < 1)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (q : ℝ) (qPositive : 0 < q)
    (fits : q + dist zero.point centre ≤ radius)
    (initial : Point) (initialInside : dist initial zero.point ≤ q) (t : ℝ) (nonnegative : 0 ≤ t) :
    GlobalSource.flow initial t ∈ closedBall centre radius := by
  apply mem_closedBall.mpr
  exact (dist_triangle _ zero.point centre).trans
    ((add_le_add (flow_retained centre radius alpha k alphaPositive contractive derivativeBound
      zero q qPositive fits initial initialInside t nonnegative) le_rfl).trans fits)

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
