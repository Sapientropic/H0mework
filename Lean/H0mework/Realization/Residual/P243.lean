import H0mework.Realization.Descent.P242

/-!
# Proposition 243: iterated same-target relaxation has geometric residual

P242 bundles the one-step affine relaxation spine.  This file proves the
corresponding finite-iteration law for a fixed target and fixed rate:

`target - T^[n](x) = (1 - sigma)^n • (target - x)`.

Equivalently, `n` repeated same-target steps collapse to one step whose rate is
`1 - (1 - sigma)^n`.

Boundary: this is a discrete finite-iterate theorem.  It does not yet prove a
continuous-time differential equation, a Hamiltonian generator, or an empirical
time-scale fit.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Finite iterates of same-target relaxation -/

/-- The residual after `n` fixed-rate same-target module relaxations is exactly
the initial residual scaled by `(1 - sigma)^n`. -/
theorem target_sub_relaxModule_iterate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) (n : Nat) :
    target - (fun y : E => relaxModule target sigma y)^[n] x =
      ((1 - sigma) ^ n) • (target - x) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [target_sub_relaxModule]
      rw [ih]
      rw [smul_smul]
      congr 1
      ring

/-- Closed form for the state after `n` same-target relaxation steps. -/
theorem relaxModule_iterate_eq_closed
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) (n : Nat) :
    (fun y : E => relaxModule target sigma y)^[n] x =
      target - ((1 - sigma) ^ n) • (target - x) := by
  calc
    (fun y : E => relaxModule target sigma y)^[n] x =
        target - (target -
          (fun y : E => relaxModule target sigma y)^[n] x) := by
          abel
    _ = target - ((1 - sigma) ^ n) • (target - x) := by
          rw [target_sub_relaxModule_iterate]

/-- Repeating a fixed-rate same-target relaxation `n` times is the same as one
relaxation with rate `1 - (1 - sigma)^n`. -/
theorem relaxModule_iterate_eq_single_pow_rate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (x : E) (n : Nat) :
    (fun y : E => relaxModule target sigma y)^[n] x =
      relaxModule target (1 - (1 - sigma) ^ n) x := by
  have hiter := target_sub_relaxModule_iterate target sigma x n
  have hsingle :
      target - relaxModule target (1 - (1 - sigma) ^ n) x =
        ((1 - sigma) ^ n) • (target - x) := by
    rw [target_sub_relaxModule]
    congr 1
    ring
  calc
    (fun y : E => relaxModule target sigma y)^[n] x =
        target - (target -
          (fun y : E => relaxModule target sigma y)^[n] x) := by
          abel
    _ = target -
        (target - relaxModule target (1 - (1 - sigma) ^ n) x) := by
          rw [hiter, hsingle]
    _ = relaxModule target (1 - (1 - sigma) ^ n) x := by
          abel


end AffineRelaxation
end SaturationMonoid
