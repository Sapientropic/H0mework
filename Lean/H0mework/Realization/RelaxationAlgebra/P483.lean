/-
  Proposition 483: finite forward/inverse saturation blocks cancel.

  P482 proves one-step operator cancellation between a non-absorbing saturation
  rate and its noisy-OR inverse.  This file lifts that cancellation from a
  single step to an arbitrary finite block:

      inverse^N (forward^N h) = h
      forward^N (inverse^N h) = h

  The sampled continuous-rate versions follow because P482 proves
  `realDecayRate lambda step ≠ 1`.

  Boundary: this is still finite scalar-carrier operator algebra.  It does not
  assert that an interpreted physical or cognitive process can freely realize
  the inverse block without an additional producer certificate.
-/

import H0mework.Realization.RelaxationFlow.P482

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Finite block cancellation for any non-absorbing rate -/

/-- THEOREM 1: `N` forward bumps followed by `N` inverse bumps cancel. -/
theorem bumpSatField_iterate_rate_then_inv_cancel
    {sigma : ℝ} (hσ : sigma ≠ 1) (h : ℝ) :
    ∀ N : ℕ,
      (fun z : ℝ =>
        bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma))^[N]
          ((fun z : ℝ => bumpSatField z sigma)^[N] h) =
        h
  | 0 => by
      simp
  | Nat.succ N => by
      let f : ℝ → ℝ := fun z => bumpSatField z sigma
      let g : ℝ → ℝ :=
        fun z => bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma)
      change g^[Nat.succ N] (f^[Nat.succ N] h) = h
      rw [Function.iterate_succ_apply' f N h]
      rw [Function.iterate_succ_apply g N (f (f^[N] h))]
      have hcancel : g (f (f^[N] h)) = f^[N] h := by
        exact bumpSatField_rate_then_inv_cancel hσ (f^[N] h)
      rw [hcancel]
      exact bumpSatField_iterate_rate_then_inv_cancel hσ h N

/-- THEOREM 2: `N` inverse bumps followed by `N` forward bumps cancel. -/
theorem bumpSatField_iterate_inv_then_rate_cancel
    {sigma : ℝ} (hσ : sigma ≠ 1) (h : ℝ) :
    ∀ N : ℕ,
      (fun z : ℝ => bumpSatField z sigma)^[N]
          ((fun z : ℝ =>
            bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma))^[N] h) =
        h
  | 0 => by
      simp
  | Nat.succ N => by
      let f : ℝ → ℝ := fun z => bumpSatField z sigma
      let g : ℝ → ℝ :=
        fun z => bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma)
      change f^[Nat.succ N] (g^[Nat.succ N] h) = h
      rw [Function.iterate_succ_apply' g N h]
      rw [Function.iterate_succ_apply f N (g (g^[N] h))]
      have hcancel : f (g (g^[N] h)) = g^[N] h := by
        exact bumpSatField_inv_then_rate_cancel hσ (g^[N] h)
      rw [hcancel]
      exact bumpSatField_iterate_inv_then_rate_cancel hσ h N

/-! ## Sampled finite block cancellation -/

/-- THEOREM 3: `N` sampled forward bumps followed by `N` sampled inverse bumps
cancel exactly. -/
theorem bumpSatField_iterate_sampled_rate_then_inv_cancel
    (h lambda step : ℝ) (N : ℕ) :
    (fun z : ℝ =>
      bumpSatField z
        (SatOrFieldAlgebra.satOrFieldInv
          (realDecayRate lambda step)))^[N]
        ((fun z : ℝ =>
          bumpSatField z (realDecayRate lambda step))^[N] h) =
      h :=
  bumpSatField_iterate_rate_then_inv_cancel
    (realDecayRate_ne_one lambda step) h N

/-- THEOREM 4: `N` sampled inverse bumps followed by `N` sampled forward bumps
cancel exactly. -/
theorem bumpSatField_iterate_sampled_inv_then_rate_cancel
    (h lambda step : ℝ) (N : ℕ) :
    (fun z : ℝ =>
      bumpSatField z (realDecayRate lambda step))^[N]
        ((fun z : ℝ =>
          bumpSatField z
            (SatOrFieldAlgebra.satOrFieldInv
              (realDecayRate lambda step)))^[N] h) =
      h :=
  bumpSatField_iterate_inv_then_rate_cancel
    (realDecayRate_ne_one lambda step) h N

/-! ## Bundled receipt -/

/-- A compact receipt that finite sampled forward/inverse saturation episodes
are exact scalar-carrier cancellations. -/
structure FiniteSampledInverseBlockCancellationReceipt : Prop where
  rate_then_inverse_block :
    ∀ h lambda step : ℝ, ∀ N : ℕ,
      (fun z : ℝ =>
        bumpSatField z
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)))^[N]
          ((fun z : ℝ =>
            bumpSatField z (realDecayRate lambda step))^[N] h) =
        h
  inverse_then_rate_block :
    ∀ h lambda step : ℝ, ∀ N : ℕ,
      (fun z : ℝ =>
        bumpSatField z (realDecayRate lambda step))^[N]
          ((fun z : ℝ =>
            bumpSatField z
              (SatOrFieldAlgebra.satOrFieldInv
                (realDecayRate lambda step)))^[N] h) =
        h

/-- THEOREM 5: the finite sampled inverse-block cancellation receipt. -/
theorem finiteSampledInverseBlockCancellationReceipt :
    FiniteSampledInverseBlockCancellationReceipt where
  rate_then_inverse_block :=
    bumpSatField_iterate_sampled_rate_then_inv_cancel
  inverse_then_rate_block :=
    bumpSatField_iterate_sampled_inv_then_rate_cancel

end

end AffineRelaxation
end SaturationMonoid
