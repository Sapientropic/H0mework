import H0mework.Realization.Relaxation.P234

/-!
# Proposition 235: phase-slice group law

P234 isolates the zero-target complex phase slice of the unified relaxation:

`relaxModule 0 (1 - u) x = u • x`.

This file proves that those phase slices compose by multiplication of residual
phases, have an identity and inverse when the phase is nonzero, and preserve
the unit-norm isometry condition under composition.

Boundary: this is the algebraic/unit-circle spine of phase evolution.  It is
not yet a one-parameter unitary group `t ↦ U t`, a Hamiltonian generator, a
Schrödinger equation, tensor geometry, or gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Phase-slice composition -/

/-- Applying residual phase `u` and then residual phase `v` is the same as
applying residual phase `v * u`. -/
theorem phase_relaxModule_compose
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u v : ℂ) (x : E) :
    relaxModule (0 : E) (1 - v)
        (relaxModule (0 : E) (1 - u) x) =
      relaxModule (0 : E) (1 - (v * u)) x := by
  rw [relaxModule_zero_target_eq_residual_smul,
    relaxModule_zero_target_eq_residual_smul,
    relaxModule_zero_target_eq_residual_smul]
  rw [smul_smul]

/-- Residual phase `1` is the identity phase slice. -/
theorem phase_relaxModule_one
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (x : E) :
    relaxModule (0 : E) (1 - (1 : ℂ)) x = x := by
  rw [relaxModule_zero_target_eq_residual_smul]
  simp

/-- A nonzero residual phase has a left inverse phase slice. -/
theorem phase_relaxModule_left_inverse
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : ℂ) (hu : u ≠ 0) (x : E) :
    relaxModule (0 : E) (1 - u⁻¹)
        (relaxModule (0 : E) (1 - u) x) = x := by
  rw [phase_relaxModule_compose]
  rw [inv_mul_cancel₀ hu]
  exact phase_relaxModule_one x

/-- A nonzero residual phase has a right inverse phase slice. -/
theorem phase_relaxModule_right_inverse
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : ℂ) (hu : u ≠ 0) (x : E) :
    relaxModule (0 : E) (1 - u)
        (relaxModule (0 : E) (1 - u⁻¹) x) = x := by
  rw [phase_relaxModule_compose]
  rw [mul_inv_cancel₀ hu]
  exact phase_relaxModule_one x

/-! ## Unit-norm phase closure -/

/-- Unit-norm residual phases are closed under composition. -/
theorem norm_phase_mul_of_norm_one
    (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖v * u‖ = 1 := by
  rw [norm_mul, hv, hu, one_mul]

/-- A composition of two unit-norm phase slices is still distance-preserving. -/
theorem dist_phase_relaxModule_compose_of_norm_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (x y : E) :
    dist
        (relaxModule (0 : E) (1 - v)
          (relaxModule (0 : E) (1 - u) x))
        (relaxModule (0 : E) (1 - v)
          (relaxModule (0 : E) (1 - u) y)) =
      dist x y := by
  rw [phase_relaxModule_compose, phase_relaxModule_compose]
  exact dist_relaxModule_zero_target_complex_of_norm_one
    (v * u) (norm_phase_mul_of_norm_one u v hu hv) x y


end AffineRelaxation
end SaturationMonoid
