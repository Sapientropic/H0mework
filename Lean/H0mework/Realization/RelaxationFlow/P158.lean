/-
  Proposition 158: power-step contraction with finite remainder phases.

  P26 bridges a future spectral-radius certificate into Lemma 3 by accepting a
  supplied `N`-step contraction certificate.  Its strongest theorem only
  sampled observations at the powered times `0, N, 2N, ...`.

  Real recall/update streams may observe after a bounded remainder phase inside
  each block: `N*k + r`.  This file closes that extra finite-phase bridge.  If
  a power-step contraction brings the block state into an observation-safe
  margin, and every listed finite remainder map preserves the same local
  observation cell, then all those finite-phase observations eventually agree.

  Boundary: this is still certificate-relative.  It does not prove the general
  spectral-radius theorem `ρ(J) < 1`; it proves that once a power-step
  contraction certificate exists, finite phase/remainder observations are not a
  separate dynamical gap.
-/

import H0mework.Realization.RelaxationFlow.P26
import H0mework.Computation.SelfReduction.P157

/-! ## One finite remainder phase -/

/-- THEOREM 1: power-step contraction plus a local observation margin after a
finite remainder phase gives eventual agreement for that phase. -/
theorem eventual_obs_eq_of_powerStep_margin_after_remainder
    {X Y : Type*} [PseudoMetricSpace X]
    {T : X -> X} {N r : Nat} {q ε : ℝ} {z x y : X} {obs : X -> Y}
    (hq_nonneg : 0 ≤ q)
    (hcontract : PowerStepContraction T N q)
    (hz : T z = z)
    (hobs_margin :
      ∀ a : X, dist a z < ε -> obs ((T^[r]) a) = obs z)
    (hxtail : ∃ Nx, ∀ k, Nx ≤ k -> q ^ k * dist x z < ε)
    (hytail : ∃ Ny, ∀ k, Ny ≤ k -> q ^ k * dist y z < ε) :
    ∃ K, ∀ k, K ≤ k ->
      obs ((T^[r]) (((PowerStep T N)^[k]) x)) =
        obs ((T^[r]) (((PowerStep T N)^[k]) y)) := by
  rcases hxtail with ⟨Nx, hx_tail⟩
  rcases hytail with ⟨Ny, hy_tail⟩
  refine ⟨max Nx Ny, ?_⟩
  intro k hk
  have hx_bound :=
    dist_powerStep_iterate_fixed_le_geometric
      T N hq_nonneg hcontract hz k x
  have hy_bound :=
    dist_powerStep_iterate_fixed_le_geometric
      T N hq_nonneg hcontract hz k y
  have hx_close : dist (((PowerStep T N)^[k]) x) z < ε :=
    lt_of_le_of_lt hx_bound
      (hx_tail k (le_trans (le_max_left Nx Ny) hk))
  have hy_close : dist (((PowerStep T N)^[k]) y) z < ε :=
    lt_of_le_of_lt hy_bound
      (hy_tail k (le_trans (le_max_right Nx Ny) hk))
  calc
    obs ((T^[r]) (((PowerStep T N)^[k]) x)) = obs z :=
      hobs_margin (((PowerStep T N)^[k]) x) hx_close
    _ = obs ((T^[r]) (((PowerStep T N)^[k]) y)) :=
      (hobs_margin (((PowerStep T N)^[k]) y) hy_close).symm

/-! ## A finite set of remainder phases -/

/-- THEOREM 2: the same power-step contraction and tail bound works for every
remainder in a finite whitelist, provided each remainder preserves the local
observation cell around the attractor. -/
theorem eventual_obs_eq_of_powerStep_margin_finite_remainders
    {X Y : Type*} [PseudoMetricSpace X]
    {T : X -> X} {N : Nat} {q ε : ℝ} {z x y : X} {obs : X -> Y}
    (remainders : Finset Nat)
    (hq_nonneg : 0 ≤ q)
    (hcontract : PowerStepContraction T N q)
    (hz : T z = z)
    (hobs_margin :
      ∀ r, r ∈ remainders ->
        ∀ a : X, dist a z < ε -> obs ((T^[r]) a) = obs z)
    (hxtail : ∃ Nx, ∀ k, Nx ≤ k -> q ^ k * dist x z < ε)
    (hytail : ∃ Ny, ∀ k, Ny ≤ k -> q ^ k * dist y z < ε) :
    ∃ K, ∀ k, K ≤ k ->
      ∀ r, r ∈ remainders ->
        obs ((T^[r]) (((PowerStep T N)^[k]) x)) =
          obs ((T^[r]) (((PowerStep T N)^[k]) y)) := by
  rcases hxtail with ⟨Nx, hx_tail⟩
  rcases hytail with ⟨Ny, hy_tail⟩
  refine ⟨max Nx Ny, ?_⟩
  intro k hk r hr
  have hx_bound :=
    dist_powerStep_iterate_fixed_le_geometric
      T N hq_nonneg hcontract hz k x
  have hy_bound :=
    dist_powerStep_iterate_fixed_le_geometric
      T N hq_nonneg hcontract hz k y
  have hx_close : dist (((PowerStep T N)^[k]) x) z < ε :=
    lt_of_le_of_lt hx_bound
      (hx_tail k (le_trans (le_max_left Nx Ny) hk))
  have hy_close : dist (((PowerStep T N)^[k]) y) z < ε :=
    lt_of_le_of_lt hy_bound
      (hy_tail k (le_trans (le_max_right Nx Ny) hk))
  calc
    obs ((T^[r]) (((PowerStep T N)^[k]) x)) = obs z :=
      hobs_margin r hr (((PowerStep T N)^[k]) x) hx_close
    _ = obs ((T^[r]) (((PowerStep T N)^[k]) y)) :=
      (hobs_margin r hr (((PowerStep T N)^[k]) y) hy_close).symm

/-!
  Summary:
  - P26 no longer only covers observations sampled exactly at powered times.
    Any finite set of bounded remainder phases can share the same contraction
    tail certificate.
  - This narrows the general-ρ gap: the remaining missing theorem is certificate
    generation from `ρ(J) < 1`, not propagation from the generated certificate
    through finite observation phases.
-/
