/-
  Proposition 485: complement-then-inverse gives the exact reciprocal blow-up
  coordinate.

  P484 proves that alternating a sampled rate with its noisy-OR inverse has
  zero net scalar-carrier effect.  The prose also uses the composite

      sigma ↦ complement sigma ↦ satOrFieldInv (complement sigma)

  as the algebraic source of a large negative coordinate for small positive
  `sigma`.  This file records the exact formula:

      satOrFieldInv (complement sigma) = 1 - sigma⁻¹.

  Thus the phrase "approximately `-1/sigma`" has a precise carrier identity:
  the value plus `sigma⁻¹` is exactly `1`; for `0 < sigma < 1` it is negative,
  and its keep-coordinate is exactly `sigma⁻¹ > 1`.

  Boundary: this proves the scalar carrier formula.  It does not assert that a
  physical process can realize this composite without an additional producer
  certificate.
-/

import H0mework.Realization.RelaxationAlgebra.P484
import H0mework.Realization.Fibres.P314

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Exact complement/inverse formula -/

/-- THEOREM 1: complement followed by noisy-OR inversion has the exact closed
form `1 - sigma⁻¹`. -/
theorem satOrFieldInv_complement_eq_one_sub_inv
    {sigma : ℝ} (hσ : sigma ≠ 0) :
    SatOrFieldAlgebra.satOrFieldInv (complement sigma) =
      1 - sigma⁻¹ := by
  unfold SatOrFieldAlgebra.satOrFieldInv complement
  field_simp [hσ]
  ring

/-- THEOREM 2: equivalently, the complement/inverse coordinate differs from
`-sigma⁻¹` by exactly `1`. -/
theorem satOrFieldInv_complement_add_inv_eq_one
    {sigma : ℝ} (hσ : sigma ≠ 0) :
    SatOrFieldAlgebra.satOrFieldInv (complement sigma) + sigma⁻¹ =
      1 := by
  rw [satOrFieldInv_complement_eq_one_sub_inv hσ]
  ring

/-- THEOREM 3: the keep-coordinate of complement-then-inverse is exactly
`sigma⁻¹`. -/
theorem keep_satOrFieldInv_complement_eq_inv
    {sigma : ℝ} (hσ : sigma ≠ 0) :
    SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv (complement sigma)) =
      sigma⁻¹ := by
  rw [satOrFieldInv_complement_eq_one_sub_inv hσ]
  unfold SatOrFieldAlgebra.keep
  ring

/-- THEOREM 4: for `0 < sigma < 1`, complement-then-inverse is a negative
rate-coordinate. -/
theorem satOrFieldInv_complement_neg_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    SatOrFieldAlgebra.satOrFieldInv (complement sigma) < 0 := by
  rw [satOrFieldInv_complement_eq_one_sub_inv hpos.ne']
  have hinv : 1 < sigma⁻¹ := (one_lt_inv₀ hpos).mpr hlt
  linarith

/-- THEOREM 5: for `0 < sigma < 1`, the keep-coordinate is greater than one. -/
theorem one_lt_keep_satOrFieldInv_complement_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    1 <
      SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv (complement sigma)) := by
  rw [keep_satOrFieldInv_complement_eq_inv hpos.ne']
  exact (one_lt_inv₀ hpos).mpr hlt

/-! ## Sampled continuous-rate version -/

/-- THEOREM 6: sampled complement-then-inverse has the exact reciprocal closed
form whenever the sampled scale is positive. -/
theorem satOrFieldInv_complement_realDecayRate_eq_one_sub_inv
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    SatOrFieldAlgebra.satOrFieldInv
        (complement (realDecayRate lambda step)) =
      1 - (realDecayRate lambda step)⁻¹ :=
  satOrFieldInv_complement_eq_one_sub_inv
    (ne_of_gt (realDecayRate_pos_of_mul_pos hpos))

/-- THEOREM 7: sampled complement-then-inverse differs from the negative
reciprocal by exactly one. -/
theorem satOrFieldInv_complement_realDecayRate_add_inv_eq_one
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    SatOrFieldAlgebra.satOrFieldInv
        (complement (realDecayRate lambda step)) +
        (realDecayRate lambda step)⁻¹ =
      1 :=
  satOrFieldInv_complement_add_inv_eq_one
    (ne_of_gt (realDecayRate_pos_of_mul_pos hpos))

/-- THEOREM 8: sampled complement-then-inverse has keep-coordinate equal to the
reciprocal sampled rate. -/
theorem keep_satOrFieldInv_complement_realDecayRate_eq_inv
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv
          (complement (realDecayRate lambda step))) =
      (realDecayRate lambda step)⁻¹ :=
  keep_satOrFieldInv_complement_eq_inv
    (ne_of_gt (realDecayRate_pos_of_mul_pos hpos))

/-- THEOREM 9: sampled complement-then-inverse is negative for every positive
sampled scale. -/
theorem satOrFieldInv_complement_realDecayRate_neg
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    SatOrFieldAlgebra.satOrFieldInv
        (complement (realDecayRate lambda step)) < 0 :=
  satOrFieldInv_complement_neg_of_mem_Ioo
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)

/-- THEOREM 10: sampled complement-then-inverse has keep-coordinate greater
than one for every positive sampled scale. -/
theorem one_lt_keep_satOrFieldInv_complement_realDecayRate
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    1 <
      SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv
          (complement (realDecayRate lambda step))) :=
  one_lt_keep_satOrFieldInv_complement_of_mem_Ioo
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)

/-! ## Bundled receipt -/

/-- A compact receipt that complement-then-inverse is the exact reciprocal
carrier blow-up coordinate, with sampled positive-scale consequences. -/
structure ComplementInverseReciprocalReceipt : Prop where
  closed_form :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      SatOrFieldAlgebra.satOrFieldInv (complement sigma) =
        1 - sigma⁻¹
  reciprocal_offset :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      SatOrFieldAlgebra.satOrFieldInv (complement sigma) + sigma⁻¹ =
        1
  keep_closed :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv (complement sigma)) =
        sigma⁻¹
  negative_on_unit_interval :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      SatOrFieldAlgebra.satOrFieldInv (complement sigma) < 0
  sampled_negative :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      SatOrFieldAlgebra.satOrFieldInv
          (complement (realDecayRate lambda step)) < 0
  sampled_keep_gt_one :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      1 <
        SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv
            (complement (realDecayRate lambda step)))

/-- THEOREM 11: the complement/inverse reciprocal receipt. -/
theorem complementInverseReciprocalReceipt :
    ComplementInverseReciprocalReceipt where
  closed_form :=
    fun _ hσ => satOrFieldInv_complement_eq_one_sub_inv hσ
  reciprocal_offset :=
    fun _ hσ => satOrFieldInv_complement_add_inv_eq_one hσ
  keep_closed :=
    fun _ hσ => keep_satOrFieldInv_complement_eq_inv hσ
  negative_on_unit_interval :=
    fun _ hpos hlt => satOrFieldInv_complement_neg_of_mem_Ioo hpos hlt
  sampled_negative :=
    fun _ _ hpos => satOrFieldInv_complement_realDecayRate_neg hpos
  sampled_keep_gt_one :=
    fun _ _ hpos =>
      one_lt_keep_satOrFieldInv_complement_realDecayRate hpos

end

end AffineRelaxation
end SaturationMonoid
