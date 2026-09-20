/-
  Proposition 482: sampled forward/inverse saturation cancels on the operator.

  P481 proves the sampled inverse closed form in the headroom coordinate.  This
  file records the stricter operator fact behind the "net zero" reading:
  noisy-OR inverse is not merely a divergent scalar in isolation; it is the
  actual inverse of the corresponding saturation bump on the non-absorbing
  carrier.

  For a sampled continuous rate `realDecayRate lambda step`, the rate is never
  absorbing (`≠ 1`), so a forward sampled bump followed by its noisy-OR inverse
  returns every scalar state exactly to where it started, and conversely.

  Boundary: this is an operator identity for the scalar saturation carrier.  It
  does not identify the carrier with physical vacuum fluctuation or energy
  without an additional interpretation/producer certificate.
-/

import H0mework.Realization.Residual.P481

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Field-level bump composition and cancellation -/

/-- THEOREM 1: field-valued saturation bumps compose by noisy-OR. -/
theorem bumpSatField_compose_field
    {α : Type*} [Field α] (h sigma tau : α) :
    bumpSatField (bumpSatField h sigma) tau =
      bumpSatField h (satOrField sigma tau) := by
  unfold bumpSatField satOrField
  ring

/-- THEOREM 2: rate `0` is the no-op bump on any field carrier. -/
theorem bumpSatField_zero_rate_field
    {α : Type*} [Field α] (h : α) :
    bumpSatField h 0 = h := by
  unfold bumpSatField
  ring

/-- THEOREM 3: a non-absorbing rate followed by its noisy-OR inverse is the
identity operator on scalar states. -/
theorem bumpSatField_rate_then_inv_cancel
    {sigma : ℝ} (hσ : sigma ≠ 1) (h : ℝ) :
    bumpSatField
        (bumpSatField h sigma)
        (SatOrFieldAlgebra.satOrFieldInv sigma) =
      h := by
  rw [bumpSatField_compose_field]
  rw [SatOrFieldAlgebra.satOrField_right_inv hσ]
  exact bumpSatField_zero_rate_field h

/-- THEOREM 4: the noisy-OR inverse followed by the original non-absorbing rate
is also the identity operator on scalar states. -/
theorem bumpSatField_inv_then_rate_cancel
    {sigma : ℝ} (hσ : sigma ≠ 1) (h : ℝ) :
    bumpSatField
        (bumpSatField h (SatOrFieldAlgebra.satOrFieldInv sigma))
        sigma =
      h := by
  rw [bumpSatField_compose_field]
  rw [SatOrFieldAlgebra.satOrField_left_inv hσ]
  exact bumpSatField_zero_rate_field h

/-! ## Sampled continuous rates are non-absorbing -/

/-- THEOREM 5: every sampled continuous rate is non-absorbing. -/
theorem realDecayRate_ne_one (lambda step : ℝ) :
    realDecayRate lambda step ≠ 1 :=
  ne_of_lt (realDecayRate_lt_one lambda step)

/-- THEOREM 6: a sampled continuous bump followed by its noisy-OR inverse
returns every scalar state exactly. -/
theorem bumpSatField_sampled_rate_then_inv_cancel
    (h lambda step : ℝ) :
    bumpSatField
        (bumpSatField h (realDecayRate lambda step))
        (SatOrFieldAlgebra.satOrFieldInv
          (realDecayRate lambda step)) =
      h :=
  bumpSatField_rate_then_inv_cancel
    (realDecayRate_ne_one lambda step) h

/-- THEOREM 7: a sampled continuous inverse bump followed by the sampled rate
also returns every scalar state exactly. -/
theorem bumpSatField_sampled_inv_then_rate_cancel
    (h lambda step : ℝ) :
    bumpSatField
        (bumpSatField h
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)))
        (realDecayRate lambda step) =
      h :=
  bumpSatField_inv_then_rate_cancel
    (realDecayRate_ne_one lambda step) h

/-- THEOREM 8: the sampled rate and its noisy-OR inverse compose to the no-op
rate. -/
theorem satOrField_sampled_rate_inv_eq_zero
    (lambda step : ℝ) :
    satOrField
        (realDecayRate lambda step)
        (SatOrFieldAlgebra.satOrFieldInv
          (realDecayRate lambda step)) =
      0 :=
  SatOrFieldAlgebra.satOrField_right_inv
    (realDecayRate_ne_one lambda step)

/-! ## Bundled receipt -/

/-- A compact receipt that sampled forward/inverse saturation is exact
operator cancellation, not merely a scalar asymptotic slogan. -/
structure SampledSaturationInverseCancellationReceipt : Prop where
  compose_field :
    ∀ h sigma tau : ℝ,
      bumpSatField (bumpSatField h sigma) tau =
        bumpSatField h (satOrField sigma tau)
  sampled_nonabsorbing :
    ∀ lambda step : ℝ, realDecayRate lambda step ≠ 1
  sampled_rate_inv_zero :
    ∀ lambda step : ℝ,
      satOrField
          (realDecayRate lambda step)
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)) =
        0
  sampled_forward_inverse_cancel :
    ∀ h lambda step : ℝ,
      bumpSatField
          (bumpSatField h (realDecayRate lambda step))
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)) =
        h
  sampled_inverse_forward_cancel :
    ∀ h lambda step : ℝ,
      bumpSatField
          (bumpSatField h
            (SatOrFieldAlgebra.satOrFieldInv
              (realDecayRate lambda step)))
          (realDecayRate lambda step) =
        h

/-- THEOREM 9: the sampled saturation inverse-cancellation receipt. -/
theorem sampledSaturationInverseCancellationReceipt :
    SampledSaturationInverseCancellationReceipt where
  compose_field :=
    bumpSatField_compose_field
  sampled_nonabsorbing :=
    realDecayRate_ne_one
  sampled_rate_inv_zero :=
    satOrField_sampled_rate_inv_eq_zero
  sampled_forward_inverse_cancel :=
    bumpSatField_sampled_rate_then_inv_cancel
  sampled_inverse_forward_cancel :=
    bumpSatField_sampled_inv_then_rate_cancel

end

end AffineRelaxation
end SaturationMonoid
