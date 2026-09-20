/-
  Proposition 484: alternating forward/inverse saturation oscillations are net
  zero.

  P483 proves finite block cancellation:

      inverse^N (forward^N h) = h.

  This file proves the stricter oscillation shape suggested by the carrier
  picture: each adjacent forward/inverse pair is already the identity operator,
  so iterating the pair any finite number of times is still exactly the
  identity.

  Boundary: this is finite scalar-carrier algebra.  It formalizes "alternating
  sampled rate/inverse-rate pairs have zero net carrier effect"; it does not
  by itself certify a physical vacuum-fluctuation interpretation.
-/

import H0mework.Realization.RelaxationAlgebra.P483

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Alternating pair cancellation for any non-absorbing rate -/

/-- THEOREM 1: an alternating forward-then-inverse pair is the identity
operator. -/
theorem bumpSatField_rate_inv_pair_id
    {sigma : ℝ} (hσ : sigma ≠ 1) :
    (fun h : ℝ =>
      bumpSatField
        (bumpSatField h sigma)
        (SatOrFieldAlgebra.satOrFieldInv sigma)) =
      id := by
  funext h
  exact bumpSatField_rate_then_inv_cancel hσ h

/-- THEOREM 2: an alternating inverse-then-forward pair is also the identity
operator. -/
theorem bumpSatField_inv_rate_pair_id
    {sigma : ℝ} (hσ : sigma ≠ 1) :
    (fun h : ℝ =>
      bumpSatField
        (bumpSatField h (SatOrFieldAlgebra.satOrFieldInv sigma))
        sigma) =
      id := by
  funext h
  exact bumpSatField_inv_then_rate_cancel hσ h

/-- THEOREM 3: any finite number of forward-then-inverse pairs is net zero. -/
theorem bumpSatField_iterate_rate_inv_pair_cancel
    {sigma : ℝ} (hσ : sigma ≠ 1) (h : ℝ) (N : ℕ) :
    (fun h : ℝ =>
      bumpSatField
        (bumpSatField h sigma)
        (SatOrFieldAlgebra.satOrFieldInv sigma))^[N] h =
      h := by
  rw [bumpSatField_rate_inv_pair_id hσ]
  simp

/-- THEOREM 4: any finite number of inverse-then-forward pairs is net zero. -/
theorem bumpSatField_iterate_inv_rate_pair_cancel
    {sigma : ℝ} (hσ : sigma ≠ 1) (h : ℝ) (N : ℕ) :
    (fun h : ℝ =>
      bumpSatField
        (bumpSatField h (SatOrFieldAlgebra.satOrFieldInv sigma))
        sigma)^[N] h =
      h := by
  rw [bumpSatField_inv_rate_pair_id hσ]
  simp

/-! ## Sampled alternating cancellation -/

/-- THEOREM 5: every finite sampled forward/inverse oscillation is net zero. -/
theorem bumpSatField_iterate_sampled_rate_inv_pair_cancel
    (h lambda step : ℝ) (N : ℕ) :
    (fun h : ℝ =>
      bumpSatField
        (bumpSatField h (realDecayRate lambda step))
        (SatOrFieldAlgebra.satOrFieldInv
          (realDecayRate lambda step)))^[N] h =
      h :=
  bumpSatField_iterate_rate_inv_pair_cancel
    (realDecayRate_ne_one lambda step) h N

/-- THEOREM 6: every finite sampled inverse/forward oscillation is net zero. -/
theorem bumpSatField_iterate_sampled_inv_rate_pair_cancel
    (h lambda step : ℝ) (N : ℕ) :
    (fun h : ℝ =>
      bumpSatField
        (bumpSatField h
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)))
        (realDecayRate lambda step))^[N] h =
      h :=
  bumpSatField_iterate_inv_rate_pair_cancel
    (realDecayRate_ne_one lambda step) h N

/-! ## Bundled receipt -/

/-- A compact receipt that finite sampled alternating forward/inverse
oscillations have exactly zero net scalar-carrier effect. -/
structure FiniteSampledOscillationNetZeroReceipt : Prop where
  sampled_rate_inv_pair_id :
    ∀ lambda step : ℝ,
      (fun h : ℝ =>
        bumpSatField
          (bumpSatField h (realDecayRate lambda step))
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step))) =
        id
  sampled_inv_rate_pair_id :
    ∀ lambda step : ℝ,
      (fun h : ℝ =>
        bumpSatField
          (bumpSatField h
            (SatOrFieldAlgebra.satOrFieldInv
              (realDecayRate lambda step)))
          (realDecayRate lambda step)) =
        id
  sampled_rate_inv_pair_iterate :
    ∀ h lambda step : ℝ, ∀ N : ℕ,
      (fun h : ℝ =>
        bumpSatField
          (bumpSatField h (realDecayRate lambda step))
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)))^[N] h =
        h
  sampled_inv_rate_pair_iterate :
    ∀ h lambda step : ℝ, ∀ N : ℕ,
      (fun h : ℝ =>
        bumpSatField
          (bumpSatField h
            (SatOrFieldAlgebra.satOrFieldInv
              (realDecayRate lambda step)))
          (realDecayRate lambda step))^[N] h =
        h

/-- THEOREM 7: the finite sampled oscillation net-zero receipt. -/
theorem finiteSampledOscillationNetZeroReceipt :
    FiniteSampledOscillationNetZeroReceipt where
  sampled_rate_inv_pair_id :=
    fun lambda step =>
      bumpSatField_rate_inv_pair_id
        (realDecayRate_ne_one lambda step)
  sampled_inv_rate_pair_id :=
    fun lambda step =>
      bumpSatField_inv_rate_pair_id
        (realDecayRate_ne_one lambda step)
  sampled_rate_inv_pair_iterate :=
    bumpSatField_iterate_sampled_rate_inv_pair_cancel
  sampled_inv_rate_pair_iterate :=
    bumpSatField_iterate_sampled_inv_rate_pair_cancel

end

end AffineRelaxation
end SaturationMonoid
