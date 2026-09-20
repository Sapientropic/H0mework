/-
  Proposition 139: two-phase retention switching algebra.

  Igarashi et al. (2022) fit collective memory decay with

      S(t) = C₁ exp(-β t) + C₂ t^(-α)

  and define the switching point as the first time when the slow power-law
  component exceeds the fast exponential component.  This file formalizes the
  small algebraic bridge that makes that definition canonical for the present
  memory-language track: in any two-channel additive retention model, "the slow
  component exceeds the fast component" is exactly "the slow component accounts
  for more than half of the total signal".

  Boundary: this is not an analytic formalization of exp/log/real powers, and
  it does not prove the gamma-mixture/Laplace-transform theorem.  It is the
  ordered-field switching-point algebra that the empirical two-phase model and
  the H¹ residual/attenuation story both consume.
-/

import H0mework.Realization.QueryPlans.P138

namespace TwoPhaseRetention

/-! ## Additive two-channel retention -/

/-- A two-channel retention signal as an additive decomposition into a fast
channel and a slow channel. -/
def signal {α : Type*} [Add α] (fast slow : α) : α :=
  fast + slow

/-- A discrete exponential/geometric fast channel.  In an analytic real model
this corresponds to `C₁ exp(-β t)` after discretization; here we keep the
algebraic keep-rate form already used by P127/P128. -/
def geometricFast {α : Type*} [Monoid α] (amplitude keep : α) (n : Nat) : α :=
  amplitude * keep ^ n

/-- A slow channel with an externally supplied tail shape.  A power-law tail is
one instance, but the analytic real-power function is intentionally outside
this algebraic lemma. -/
def shapedSlow {α : Type*} [Mul α] (amplitude : α) (tail : Nat -> α)
    (n : Nat) : α :=
  amplitude * tail n

/-- The discrete two-phase skeleton: a geometric fast channel plus an arbitrary
slow tail. -/
def discreteTwoPhase {α : Type*} [Semiring α]
    (fastAmplitude fastKeep slowAmplitude : α)
    (slowTail : Nat -> α) (n : Nat) : α :=
  geometricFast fastAmplitude fastKeep n +
    shapedSlow slowAmplitude slowTail n

/-- THEOREM 1: the discrete two-phase skeleton is exactly the additive
fast-channel plus slow-channel decomposition. -/
theorem discreteTwoPhase_eq_signal
    {α : Type*} [Semiring α]
    (fastAmplitude fastKeep slowAmplitude : α)
    (slowTail : Nat -> α) (n : Nat) :
    discreteTwoPhase fastAmplitude fastKeep slowAmplitude slowTail n =
      signal
        (geometricFast fastAmplitude fastKeep n)
        (shapedSlow slowAmplitude slowTail n) := by
  rfl

/-! ## Switching point algebra -/

/-- THEOREM 2: the slow component dominates the fast component exactly when it
accounts for more than half of the additive total.  This is written without
division, as `fast + slow < 2 * slow`. -/
theorem slow_dominates_iff_majority
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {fast slow : α} :
    fast < slow <-> signal fast slow < (2 : α) * slow := by
  unfold signal
  constructor <;> intro h <;> linarith

/-- THEOREM 3: the fast component dominates the slow component exactly when it
accounts for more than half of the additive total. -/
theorem fast_dominates_iff_majority
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {fast slow : α} :
    slow < fast <-> signal fast slow < (2 : α) * fast := by
  unfold signal
  constructor <;> intro h <;> linarith

/-- THEOREM 4: at equality of the two channels, each channel accounts for
exactly half of the total, again written without division. -/
theorem equal_channels_half_total
    {α : Type*} [CommRing α]
    {fast slow : α}
    (h : fast = slow) :
    signal fast slow = (2 : α) * slow := by
  unfold signal
  rw [h]
  ring_nf

/-- THEOREM 5: if the slow component dominates at a time point, then the
two-phase signal is not fast-majority at that same point. -/
theorem slow_dominates_not_fast_majority
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {fast slow : α}
    (h : fast < slow) :
    ¬ signal fast slow < (2 : α) * fast := by
  intro hfast
  have hfastDom : slow < fast :=
    (fast_dominates_iff_majority (fast := fast) (slow := slow)).mpr hfast
  exact (not_lt_of_ge (le_of_lt h)) hfastDom

/-- THEOREM 6: if the fast component dominates at a time point, then the
two-phase signal is not slow-majority at that same point. -/
theorem fast_dominates_not_slow_majority
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {fast slow : α}
    (h : slow < fast) :
    ¬ signal fast slow < (2 : α) * slow := by
  intro hslow
  have hslowDom : fast < slow :=
    (slow_dominates_iff_majority (fast := fast) (slow := slow)).mpr hslow
  exact (not_lt_of_ge (le_of_lt h)) hslowDom

/-!
  Summary:
  - The empirical two-phase formula is represented algebraically as a fast
    geometric channel plus an externally supplied slow tail.
  - Igarashi-style switching, "slow component exceeds fast component", is
    exactly the majority-share condition for the slow channel.
  - This gives the H¹/attenuation track a clean ordered-field interface to the
    empirical switching-point notion without pretending to have formalized
    analytic exp/power fitting.
-/


end TwoPhaseRetention
