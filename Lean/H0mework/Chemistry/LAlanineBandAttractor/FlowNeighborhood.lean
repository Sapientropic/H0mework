import H0mework.Chemistry.LAlanineBandAttractor.FlowExponential

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient Set Metric Filter
open scoped NNReal Topology
noncomputable section

def neighborhoodRadius {centre : Point} {radius : ℝ} (zero : ZeroInBall centre radius) : ℝ :=
  (radius - dist zero.point centre) / 2

def neighborhood {centre : Point} {radius : ℝ} (zero : ZeroInBall centre radius) : Set Point :=
  ball zero.point (neighborhoodRadius zero)

theorem neighborhood_geometry {centre : Point} {radius : ℝ} (zero : ZeroInBall centre radius)
    (interior : zero.point ∈ ball centre radius) :
    0 < neighborhoodRadius zero ∧ neighborhoodRadius zero + dist zero.point centre ≤ radius := by
  have h := mem_ball.mp interior
  unfold neighborhoodRadius
  constructor <;> linarith

theorem neighborhood_open {centre : Point} {radius : ℝ} (zero : ZeroInBall centre radius) :
    IsOpen (neighborhood zero) := isOpen_ball

theorem neighborhood_nonempty (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusNonnegative : 0 ≤ radius) (alphaPositive : 0 < alpha) (contractive : k < 1)
    (strictBudget : alpha * ‖sourceGradient centre‖ + (k : ℝ) * radius < radius)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) : (neighborhood zero).Nonempty := by
  have geometry := neighborhood_geometry zero (zero_interior centre radius alpha k radiusNonnegative
    alphaPositive contractive strictBudget derivativeBound zero)
  exact ⟨zero.point,mem_ball_self geometry.1⟩

theorem neighborhood_retained (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusNonnegative : 0 ≤ radius) (alphaPositive : 0 < alpha) (contractive : k < 1)
    (strictBudget : alpha * ‖sourceGradient centre‖ + (k : ℝ) * radius < radius)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (initial : Point) (inside : initial ∈ neighborhood zero)
    (t : ℝ) (nonnegative : 0 ≤ t) : GlobalSource.flow initial t ∈ neighborhood zero := by
  have geometry := neighborhood_geometry zero (zero_interior centre radius alpha k radiusNonnegative
    alphaPositive contractive strictBudget derivativeBound zero)
  have start : dist initial zero.point < neighborhoodRadius zero := inside
  have bound := flow_exponential_bound centre radius alpha k alphaPositive contractive derivativeBound
    zero (neighborhoodRadius zero) geometry.1 geometry.2 initial start.le t nonnegative
  have rate := attractionRate_positive alpha k alphaPositive contractive
  have exponential : Real.exp (-attractionRate alpha k * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) nonnegative)
  apply mem_ball.mpr
  apply bound.trans_lt
  exact ((mul_le_mul_of_nonneg_left exponential dist_nonneg).trans_eq (mul_one _)).trans_lt start

theorem neighborhood_converges (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusNonnegative : 0 ≤ radius) (alphaPositive : 0 < alpha) (contractive : k < 1)
    (strictBudget : alpha * ‖sourceGradient centre‖ + (k : ℝ) * radius < radius)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) (initial : Point) (inside : initial ∈ neighborhood zero) :
    Tendsto (GlobalSource.flow initial) atTop (𝓝 zero.point) := by
  have geometry := neighborhood_geometry zero (zero_interior centre radius alpha k radiusNonnegative
    alphaPositive contractive strictBudget derivativeBound zero)
  exact flow_converges centre radius alpha k alphaPositive contractive derivativeBound
    zero (neighborhoodRadius zero) geometry.1 geometry.2 initial (mem_ball.mp inside).le

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
