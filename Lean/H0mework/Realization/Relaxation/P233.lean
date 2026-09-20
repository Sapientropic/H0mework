import H0mework.Realization.Relaxation.P232

/-!
# Proposition 233: complex normed-vector carrier for affine relaxation

P231 proves that the target-general relaxation law

`x ↦ x + σ • (target - x)`

is algebraically stable over arbitrary module carriers.  P232 adds the real
normed-vector contraction law.  This file adds the corresponding complex
normed-vector distance law: same-target relaxation scales distances by
`‖1 - σ‖`.

Boundary: this is a complex carrier theorem, not a unitary quantum theorem.
When `‖1 - σ‖ = 1` the map is distance-preserving, but Schrödinger evolution,
phase holonomy, and gauge transport still require separate structure.
-/

namespace SaturationMonoid
namespace AffineRelaxation

theorem dist_relaxModule_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) (x y : E) :
    dist (relaxModule target sigma x) (relaxModule target sigma y) =
      ‖(1 : ℂ) - sigma‖ * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, relaxModule_sub_relaxModule]
  rw [norm_smul]

theorem dist_relaxModule_target_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) (x : E) :
    dist (relaxModule target sigma x) target =
      ‖(1 : ℂ) - sigma‖ * dist x target := by
  calc
    dist (relaxModule target sigma x) target =
        dist (relaxModule target sigma x)
          (relaxModule target sigma target) := by
            rw [relaxModule_target_absorbing]
    _ = ‖(1 : ℂ) - sigma‖ * dist x target := by
          exact dist_relaxModule_complex target sigma x target

theorem lipschitzWith_relaxModule_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) :
    LipschitzWith (Real.toNNReal ‖(1 : ℂ) - sigma‖)
      (fun x : E => relaxModule target sigma x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_relaxModule_complex]
  have hnorm_nonneg : 0 <= ‖(1 : ℂ) - sigma‖ := norm_nonneg _
  simp [Real.toNNReal_of_nonneg hnorm_nonneg]

theorem continuous_relaxModule_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (target : E) (sigma : ℂ) :
    Continuous (fun x : E => relaxModule target sigma x) :=
  (lipschitzWith_relaxModule_complex target sigma).continuous


end AffineRelaxation
end SaturationMonoid
