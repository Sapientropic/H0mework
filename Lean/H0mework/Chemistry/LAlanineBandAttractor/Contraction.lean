import H0mework.Chemistry.LAlanineBandAttractor.Map
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Attractor

open SourceGaussianModel ContinuousGradient Set Metric
open scoped NNReal
noncomputable section

structure ZeroInBall (centre : Point) (radius : ℝ) where
  point : Point
  inside : point ∈ closedBall centre radius
  zero : sourceGradient point = 0
  unique : ∀ x ∈ closedBall centre radius, sourceGradient x = 0 → x = point

theorem step_fixed_iff (alpha : ℝ) (positive : 0 < alpha) (x : Point) :
    step alpha x = x ↔ sourceGradient x = 0 := by
  constructor
  · intro same
    have scalar : alpha • sourceGradient x = 0 := by
      apply add_left_cancel (a := x)
      simpa only [step, add_zero] using same
    exact (smul_eq_zero.mp scalar).resolve_left positive.ne'
  · intro zero
    simp [step, zero]

/-- Raw centre and Hessian bounds generate a unique zero of the original field. -/
def produceZero (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusPositive : 0 < radius) (alphaPositive : 0 < alpha) (contractive : k < 1)
    (budget : alpha * ‖sourceGradient centre‖ + (k : ℝ) * radius ≤ radius)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ)) :
    ZeroInBall centre radius := by
  letI : Nonempty (closedBall centre radius) := ⟨⟨centre,mem_closedBall_self radiusPositive.le⟩⟩
  letI : CompleteSpace (closedBall centre radius) := isClosed_closedBall.completeSpace_coe
  let selfMap := step_maps_closedBall centre radius alpha k radiusPositive.le alphaPositive budget derivativeBound
  let F : closedBall centre radius → closedBall centre radius :=
    fun x => ⟨step alpha x.val,selfMap x.property⟩
  have contraction : ContractingWith k F := by
    refine ⟨contractive,LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    exact (step_lipschitzOn centre radius alpha k derivativeBound).dist_le_mul x x.property y y.property
  let p := contraction.fixedPoint F
  have fixed : step alpha p.val = p.val :=
    congrArg Subtype.val contraction.fixedPoint_isFixedPt
  refine ⟨p.val,p.property,(step_fixed_iff alpha alphaPositive p.val).mp fixed,?_⟩
  intro x inside zero
  have fixedX : Function.IsFixedPt F ⟨x,inside⟩ := by
    apply Subtype.ext
    exact (step_fixed_iff alpha alphaPositive x).mpr zero
  exact congrArg Subtype.val (contraction.fixedPoint_unique fixedX)

theorem zero_distance_le (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusNonnegative : 0 ≤ radius) (alphaPositive : 0 < alpha) (contractive : k < 1)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (x : Point) (inside : x ∈ closedBall centre radius) (zero : sourceGradient x = 0) :
    dist x centre ≤ alpha * ‖sourceGradient centre‖ / (1 - (k : ℝ)) := by
  have fixed := (step_fixed_iff alpha alphaPositive x).mpr zero
  have bound : dist x centre ≤ (k : ℝ) * dist x centre + alpha * ‖sourceGradient centre‖ := by
    calc
      dist x centre = dist (step alpha x) centre := by rw [fixed]
      _ ≤ dist (step alpha x) (step alpha centre) + dist (step alpha centre) centre := dist_triangle _ _ _
      _ ≤ (k : ℝ) * dist x centre + alpha * ‖sourceGradient centre‖ := by
        rw [step_centre_distance centre alpha alphaPositive]
        exact add_le_add ((step_lipschitzOn centre radius alpha k derivativeBound).dist_le_mul
          x inside centre (mem_closedBall_self radiusNonnegative)) le_rfl
  have positive : 0 < 1 - (k : ℝ) := by
    have hk : (k : ℝ) < 1 := by exact_mod_cast contractive
    linarith
  apply (le_div_iff₀ positive).mpr
  nlinarith

theorem zero_interior (centre : Point) (radius alpha : ℝ) (k : ℝ≥0)
    (radiusNonnegative : 0 ≤ radius) (alphaPositive : 0 < alpha) (contractive : k < 1)
    (strictBudget : alpha * ‖sourceGradient centre‖ + (k : ℝ) * radius < radius)
    (derivativeBound : ∀ x ∈ closedBall centre radius, ‖stepDerivative alpha x‖ ≤ (k : ℝ))
    (zero : ZeroInBall centre radius) : zero.point ∈ ball centre radius := by
  apply mem_ball.mpr
  apply (zero_distance_le centre radius alpha k radiusNonnegative alphaPositive contractive derivativeBound
    zero.point zero.inside zero.zero).trans_lt
  have positive : 0 < 1 - (k : ℝ) := by
    have hk : (k : ℝ) < 1 := by exact_mod_cast contractive
    linarith
  apply (div_lt_iff₀ positive).mpr
  nlinarith

end
end LAlanine40K2025.BasinRefinement.Attractor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
