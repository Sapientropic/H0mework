import H0mework.Realization.Relaxation.P233

/-!
# Proposition 234: phase-isometry slice of affine relaxation

P233 proves the complex normed-vector distance law for the affine relaxation

`x ↦ x + σ • (target - x)`.

This file isolates the zero-target phase slice.  If `σ = 1 - u`, then
relaxation toward zero is exactly scalar multiplication by the residual `u`.
When `‖u‖ = 1`, that map is an isometry.

Boundary: this proves a phase/isometry slice inside the unified formula.  It is
not yet Schrödinger evolution, a one-parameter unitary group, a Hamiltonian
generator theorem, or gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

lemma relaxModule_zero_target_eq_residual_smul
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (u : K) (x : E) :
    relaxModule (0 : E) (1 - u) x = u • x := by
  unfold relaxModule
  module

theorem dist_relaxModule_zero_target_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) (x y : E) :
    dist (relaxModule (0 : E) (1 - u) x)
      (relaxModule (0 : E) (1 - u) y) =
      ‖u‖ * dist x y := by
  rw [relaxModule_zero_target_eq_residual_smul,
    relaxModule_zero_target_eq_residual_smul]
  rw [dist_eq_norm, dist_eq_norm]
  rw [← smul_sub, norm_smul]

theorem dist_relaxModule_zero_target_complex_of_norm_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) (hu : ‖u‖ = 1) (x y : E) :
    dist (relaxModule (0 : E) (1 - u) x)
      (relaxModule (0 : E) (1 - u) y) =
      dist x y := by
  rw [dist_relaxModule_zero_target_complex]
  simp [hu]

theorem lipschitzWith_phase_relaxModule_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) :
    LipschitzWith (Real.toNNReal ‖u‖)
      (fun x : E => relaxModule (0 : E) (1 - u) x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_relaxModule_zero_target_complex]
  have hnorm_nonneg : 0 <= ‖u‖ := norm_nonneg _
  simp [Real.toNNReal_of_nonneg hnorm_nonneg]

theorem continuous_phase_relaxModule_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) :
    Continuous (fun x : E => relaxModule (0 : E) (1 - u) x) :=
  (lipschitzWith_phase_relaxModule_complex u).continuous


end AffineRelaxation
end SaturationMonoid
