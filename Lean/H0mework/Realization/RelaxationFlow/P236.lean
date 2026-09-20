import H0mework.Realization.RelaxationAlgebra.P235
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Proposition 236: scalar one-parameter phase flow

P235 proves the group law for zero-target phase slices:

`relaxModule 0 (1 - u) x = u • x`.

This file supplies a concrete one-parameter scalar phase family

`u(t) = exp(i t)`.

It proves that this family has unit norm, maps time addition to phase
multiplication, and therefore gives a time-additive flow for the zero-target
phase slice.

Boundary: this is only the scalar complex phase flow.  It does not prove a
Hamiltonian generator theorem, a general unitary group on Hilbert space,
Schrödinger evolution, tensor products, or gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## The scalar phase family `exp(i t)` -/

/-- The concrete unit complex phase used by the scalar one-parameter slice. -/
noncomputable def unitComplexPhase (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ))

/-- `exp(i t)` has unit norm. -/
theorem unitComplexPhase_norm (t : ℝ) :
    ‖unitComplexPhase t‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal t

/-- `exp(i * 0) = 1`. -/
theorem unitComplexPhase_zero :
    unitComplexPhase 0 = 1 := by
  simp [unitComplexPhase]

/-- The scalar phase family maps addition of times to multiplication of
phases. -/
theorem unitComplexPhase_add (t s : ℝ) :
    unitComplexPhase (t + s) = unitComplexPhase t * unitComplexPhase s := by
  unfold unitComplexPhase
  calc
    Complex.exp (Complex.I * ((t + s : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (t : ℂ) + Complex.I * (s : ℂ)) := by
          congr 1
          rw [Complex.ofReal_add]
          ring
    _ = Complex.exp (Complex.I * (t : ℂ)) *
        Complex.exp (Complex.I * (s : ℂ)) := by
          rw [Complex.exp_add]

/-! ## Transporting the phase family through `relaxModule` -/

/-- The `exp(i t)` phase slice is distance-preserving for every time. -/
theorem dist_unitComplexPhase_relaxModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (x y : E) :
    dist (relaxModule (0 : E) (1 - unitComplexPhase t) x)
      (relaxModule (0 : E) (1 - unitComplexPhase t) y) =
      dist x y := by
  exact dist_relaxModule_zero_target_complex_of_norm_one
    (unitComplexPhase t) (unitComplexPhase_norm t) x y

/-- Applying time `t` and then time `s` is the same phase slice as applying
time `t+s`. -/
theorem phase_relaxModule_time_add
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (t s : ℝ) (x : E) :
    relaxModule (0 : E) (1 - unitComplexPhase s)
        (relaxModule (0 : E) (1 - unitComplexPhase t) x) =
      relaxModule (0 : E) (1 - unitComplexPhase (t + s)) x := by
  rw [phase_relaxModule_compose]
  have hphase :
      unitComplexPhase s * unitComplexPhase t =
        unitComplexPhase (t + s) := by
    rw [unitComplexPhase_add]
    ring
  rw [hphase]

/-- Composing two `exp(i t)` phase slices is still distance-preserving. -/
theorem dist_phase_relaxModule_time_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t s : ℝ) (x y : E) :
    dist
        (relaxModule (0 : E) (1 - unitComplexPhase s)
          (relaxModule (0 : E) (1 - unitComplexPhase t) x))
        (relaxModule (0 : E) (1 - unitComplexPhase s)
          (relaxModule (0 : E) (1 - unitComplexPhase t) y)) =
      dist x y := by
  rw [phase_relaxModule_time_add, phase_relaxModule_time_add]
  exact dist_unitComplexPhase_relaxModule (t + s) x y


end AffineRelaxation
end SaturationMonoid
