import H0mework.Realization.Relaxation.P231

/-!
# Proposition 232: normed-vector contraction for the unified equation

P231 lifted the unified affine relaxation law to arbitrary modules:

`x -> x + sigma • (target - x)`.

This file proves the metric layer for real normed vector spaces.  Over any
`NormedSpace ℝ E`, same-target relaxation scales distances by `|1 - sigma|`.
For rates in `[0, 1]`, this gives the expected contraction constant
`1 - sigma`.

Boundary: this is still real normed-vector contraction.  Complex phase/unitary
evolution, tensor geometry, and gauge/target transport remain separate proof
obligations.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Algebraic difference lemmas -/

/-- Same-target module relaxation scales pairwise differences by `1 - sigma`. -/
lemma relaxModule_sub_relaxModule
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x y : E) (sigma : K) :
    relaxModule target sigma x - relaxModule target sigma y =
      (1 - sigma) • (x - y) := by
  unfold relaxModule
  module

/-- The output residual from the target is also scaled by `1 - sigma`. -/
lemma relaxModule_sub_target
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma : K) :
    relaxModule target sigma x - target =
      (1 - sigma) • (x - target) := by
  unfold relaxModule
  module

/-! ## Real normed-vector metric facts -/

/-- In a real normed vector space, target-general relaxation scales pairwise
distances by `|1 - sigma|`. -/
theorem dist_relaxModule_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) (x y : E) :
    dist (relaxModule target sigma x) (relaxModule target sigma y) =
      |1 - sigma| * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, relaxModule_sub_relaxModule]
  rw [norm_smul, Real.norm_eq_abs]

/-- Distance to the target is scaled by `|1 - sigma|`. -/
theorem dist_relaxModule_target_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) (x : E) :
    dist (relaxModule target sigma x) target =
      |1 - sigma| * dist x target := by
  calc
    dist (relaxModule target sigma x) target =
        dist (relaxModule target sigma x)
          (relaxModule target sigma target) := by
            rw [relaxModule_target_absorbing]
    _ = |1 - sigma| * dist x target := by
          exact dist_relaxModule_real target sigma x target

/-- For arbitrary real rates, the module relaxation map is Lipschitz with
constant `|1 - sigma|`. -/
theorem lipschitzWith_relaxModule_real_abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) :
    LipschitzWith (Real.toNNReal |1 - sigma|)
      (fun x : E => relaxModule target sigma x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_relaxModule_real]
  have habs_nonneg : 0 <= |1 - sigma| := abs_nonneg _
  simp [Real.toNNReal_of_nonneg habs_nonneg]

/-- For rates `sigma <= 1`, the Lipschitz constant can be written as
`1 - sigma`. -/
theorem lipschitzWith_relaxModule_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) (hs1 : sigma <= 1) :
    LipschitzWith (Real.toNNReal (1 - sigma))
      (fun x : E => relaxModule target sigma x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_relaxModule_real]
  have hres_nonneg : 0 <= 1 - sigma := by linarith
  rw [abs_of_nonneg hres_nonneg]
  simp [Real.toNNReal_of_nonneg hres_nonneg]

/-- The real normed-vector relaxation map is continuous. -/
theorem continuous_relaxModule_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (sigma : ℝ) :
    Continuous (fun x : E => relaxModule target sigma x) :=
  (lipschitzWith_relaxModule_real_abs target sigma).continuous

/-!
  Summary:
  - P231 gives the module algebra.
  - P232 proves that, in real normed vector spaces, the same formula scales
    distances by `|1 - sigma|`.
  - With rates in `[0, 1]`, the contraction constant is `1 - sigma`.

  Boundary:
  - This does not prove complex/unitary evolution or tensor/gauge transport.
-/


end AffineRelaxation
end SaturationMonoid
