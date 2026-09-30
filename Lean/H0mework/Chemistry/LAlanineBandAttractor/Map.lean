import H0mework.Chemistry.LAlanineGradient.Model
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient Set Metric
open scoped NNReal
noncomputable section

def step (alpha : ℝ) (x : Point) : Point := x + alpha • sourceGradient x

def stepDerivative (alpha : ℝ) (x : Point) : Point →L[ℝ] Point :=
  ContinuousLinearMap.id ℝ Point + alpha • sourceHessianLinear x

theorem step_hasFDerivAt (alpha : ℝ) (x : Point) :
    HasFDerivAt (step alpha) (stepDerivative alpha x) x :=
  (hasFDerivAt_id x).add ((sourceGradient_hasFDerivAt x).const_smul alpha)

theorem step_lipschitzOn (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ)) :
    LipschitzOnWith k (step alpha) (closedBall centre radius) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x _ => (step_hasFDerivAt alpha x).hasFDerivWithinAt) _ (convex_closedBall centre radius)
  intro x hx
  exact_mod_cast derivativeBound x hx

theorem step_centre_distance (centre : Point) (alpha : ℝ) (positive : 0 < alpha) :
    dist (step alpha centre) centre = alpha * ‖sourceGradient centre‖ := by
  simp [step, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos positive]

theorem step_maps_closedBall (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusNonnegative : 0 ≤ radius) (alphaPositive : 0 < alpha)
    (budget : alpha * ‖sourceGradient centre‖ + (k : ℝ) * radius ≤ radius)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ)) :
    MapsTo (step alpha) (closedBall centre radius) (closedBall centre radius) := by
  intro x inside
  apply mem_closedBall.mpr
  calc
    dist (step alpha x) centre ≤ dist (step alpha x) (step alpha centre) + dist (step alpha centre) centre :=
      dist_triangle _ _ _
    _ ≤ (k : ℝ) * dist x centre + alpha * ‖sourceGradient centre‖ := by
      rw [step_centre_distance centre alpha alphaPositive]
      exact add_le_add ((step_lipschitzOn centre radius alpha k derivativeBound).dist_le_mul
        x inside centre (mem_closedBall_self radiusNonnegative)) le_rfl
    _ ≤ (k : ℝ) * radius + alpha * ‖sourceGradient centre‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (mem_closedBall.mp inside) k.coe_nonneg) le_rfl
    _ ≤ radius := by linarith

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
