/-
  Proposition 26: power-step contraction bridge for spectral-radius certificates.

  The general theorem `ρ(J) < 1 => exists an equivalent norm with ‖J‖ < 1`
  is not currently wired into this Lean project.  Mathlib does expose Gelfand-
  style spectral-radius facts that are more naturally used to obtain a power
  certificate such as `‖J^N‖ < 1`.

  This module proves the bridge that such a certificate should feed: if an
  `N`-step reducer is a contraction, then the existing Lemma 3 observable
  agreement theorem applies to that powered reducer.  Thus a future
  spectral-radius proof only has to produce the power-step contraction
  certificate; the observation/fading-memory side is already closed.
-/

import H0mework.Realization.QuerySupport.P25

/-! ## Power-step contraction -/

/-- The powered reducer that runs `T` for `N` steps at a time. -/
def PowerStep {X : Type*} (T : X → X) (N : Nat) : X → X :=
  T^[N]

/-- A contraction certificate for the powered reducer. -/
def PowerStepContraction {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (N : Nat) (q : ℝ) : Prop :=
  ∀ x y : X, dist (PowerStep T N x) (PowerStep T N y) ≤ q * dist x y

/-- THEOREM 1: a power-step contraction is exactly a contraction for the
    powered reducer `PowerStep T N`. -/
theorem powerStepContraction_as_contraction
    {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (N : Nat) (q : ℝ)
    (h : PowerStepContraction T N q) :
    ∀ x y : X, dist (PowerStep T N x) (PowerStep T N y) ≤ q * dist x y := h

/-- THEOREM 2: if a fixed point of `T` is supplied, it is also a fixed point of
    the powered reducer. -/
theorem powerStep_fixed_of_fixed
    {X : Type*} (T : X → X) (N : Nat) {z : X}
    (hz : T z = z) :
    PowerStep T N z = z := by
  unfold PowerStep
  induction N with
  | zero =>
      rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      exact hz

/-- THEOREM 3: power-step contraction gives the same geometric fading-memory
    bound as Lemma 3, but sampled at powered-reducer steps. -/
theorem dist_powerStep_iterate_fixed_le_geometric
    {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (N : Nat) {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hcontract : PowerStepContraction T N q)
    {z : X} (hz : T z = z) :
    ∀ k x,
      dist ((PowerStep T N)^[k] x) z ≤ q ^ k * dist x z := by
  exact dist_iterate_fixed_le_geometric
    (PowerStep T N) hq_nonneg
    (powerStepContraction_as_contraction T N q hcontract)
    (powerStep_fixed_of_fixed T N hz)

/-- THEOREM 4: if a power-step contraction eventually places two trajectories
    inside one observation-safe margin ball, their powered observations
    eventually agree. -/
theorem eventual_obs_eq_of_powerStep_margin
    {X Y : Type*} [PseudoMetricSpace X]
    {T : X → X} {N : Nat} {q ε : ℝ} {z x y : X} {obs : X → Y}
    (hq_nonneg : 0 ≤ q)
    (hcontract : PowerStepContraction T N q)
    (hz : T z = z)
    (hobs_margin : ∀ a : X, dist a z < ε → obs a = obs z)
    (hxtail : ∃ Nx, ∀ k, Nx ≤ k → q ^ k * dist x z < ε)
    (hytail : ∃ Ny, ∀ k, Ny ≤ k → q ^ k * dist y z < ε) :
    ∃ K, ∀ k, K ≤ k →
      obs (((PowerStep T N)^[k]) x) =
        obs (((PowerStep T N)^[k]) y) := by
  exact eventual_obs_eq_of_fixed_point_margin
    (T := PowerStep T N)
    hq_nonneg
    (powerStepContraction_as_contraction T N q hcontract)
    (powerStep_fixed_of_fixed T N hz)
    hobs_margin
    hxtail
    hytail

/-!
  Summary:
  - A spectral-radius/Gelfand route may produce an `N`-step contraction rather
    than a one-step contraction.
  - Once that power-step certificate is supplied, Lemma 3's observable
    agreement theorem applies directly to the powered reducer.

  Boundary:
  - This does not prove `ρ(J) < 1`.  It proves the bridge from a supplied
    power-step contraction certificate into the existing observable-bisimulation
    skeleton.
-/
