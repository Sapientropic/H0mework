import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandAttractor.Equilibrium
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient Set Metric
open scoped NNReal
noncomputable section

def weight (alpha t : ℝ) : ℝ := Real.exp (t / alpha)

theorem weight_positive (alpha t : ℝ) : 0 < weight alpha t := Real.exp_pos _

theorem weight_hasDerivAt (alpha t : ℝ) :
    HasDerivAt (weight alpha) (weight alpha t / alpha) t := by
  convert! ((hasDerivAt_id t).div_const alpha).exp using 1
  simp only [weight, id]
  ring

def weightedFlow (point initial : Point) (alpha t : ℝ) : Point :=
  weight alpha t • (GlobalSource.flow initial t - point)

def weightedDerivative (point initial : Point) (alpha t : ℝ) : Point :=
  (weight alpha t / alpha) • (step alpha (GlobalSource.flow initial t) - point)

theorem weighted_hasDerivAt (point initial : Point) (alpha : ℝ) (positive : 0 < alpha) (t : ℝ) :
    HasDerivAt (weightedFlow point initial alpha) (weightedDerivative point initial alpha t) t := by
  have raw := (weight_hasDerivAt alpha t).smul ((GlobalSource.flow_hasDerivAt initial t).sub_const point)
  convert! raw using 1
  ext axis
  simp only [weightedDerivative, step, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  field_simp [positive.ne']
  ring

theorem weighted_norm (point initial : Point) (alpha t : ℝ) :
    ‖weightedFlow point initial alpha t‖ = weight alpha t * dist (GlobalSource.flow initial t) point := by
  rw [weightedFlow, norm_smul, Real.norm_eq_abs, abs_of_pos (weight_positive alpha t), dist_eq_norm]

theorem weighted_continuous (point initial : Point) (alpha : ℝ) (positive : 0 < alpha) :
    Continuous (weightedFlow point initial alpha) :=
  continuous_iff_continuousAt.mpr (fun t => (weighted_hasDerivAt point initial alpha positive t).continuousAt)

theorem weightedDerivative_norm_bound (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (alphaPositive : 0 < alpha)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (initial : Point) (t : ℝ)
    (inside : GlobalSource.flow initial t ∈ closedBall centre radius) :
    ‖weightedDerivative zero.point initial alpha t‖ ≤
      ((k : ℝ) / alpha) * ‖weightedFlow zero.point initial alpha t‖ := by
  have bound := (step_lipschitzOn centre radius alpha k derivativeBound).dist_le_mul
    (GlobalSource.flow initial t) inside zero.point zero.inside
  rw [(step_fixed_iff alpha alphaPositive zero.point).mpr zero.zero, dist_eq_norm] at bound
  rw [weightedDerivative, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (weight_positive alpha t) alphaPositive), weighted_norm]
  calc
    (weight alpha t / alpha) * ‖step alpha (GlobalSource.flow initial t) - zero.point‖ ≤
        (weight alpha t / alpha) * ((k : ℝ) * dist (GlobalSource.flow initial t) zero.point) :=
      mul_le_mul_of_nonneg_left bound (div_pos (weight_positive alpha t) alphaPositive).le
    _ = _ := by ring

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
