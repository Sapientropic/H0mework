/-
  Proposition 481: sampled inverse saturation gives exponential headroom growth.

  P480 proves the sampled forward carrier law: a one-step rate

      sigma = 1 - exp(-lambda * step)

  has a zero-origin orbit whose residual/headroom is `exp(-lambda * N * step)`.
  P478 proves the general inverse side: iterating the noisy-OR inverse makes
  headroom diverge for every positive nonabsorbing rate.

  This file composes those two facts and records the exact sampled inverse
  closed form.  The inverse step has keep-coordinate

      exp(lambda * step),

  hence after `N` inverse steps the headroom is

      exp(lambda * N * step).

  Boundary: this is a scalar saturation-carrier theorem.  It proves the
  algebraic inverse/exponential-growth law, not a physical energy claim.
-/

import H0mework.Realization.RelaxationFlow.P480

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

open Filter

/-! ## Inverse keep coordinate -/

/-- THEOREM 1: in the residual coordinate, noisy-OR inversion is ordinary
multiplicative inversion. -/
theorem keep_satOrFieldInv_eq_inv_keep
    {sigma : ℝ} (hkeep : SatOrFieldAlgebra.keep sigma ≠ 0) :
    SatOrFieldAlgebra.keep (SatOrFieldAlgebra.satOrFieldInv sigma) =
      (SatOrFieldAlgebra.keep sigma)⁻¹ := by
  have hkeep' : 1 - sigma ≠ 0 := by
    simpa [SatOrFieldAlgebra.keep] using hkeep
  unfold SatOrFieldAlgebra.keep SatOrFieldAlgebra.satOrFieldInv
  have hden : sigma - 1 ≠ 0 := by
    intro h
    apply hkeep'
    linarith
  field_simp [hden, hkeep']
  ring_nf

/-- THEOREM 2: the noisy-OR inverse of a sampled continuous rate has
keep-coordinate equal to the reciprocal continuous residual. -/
theorem keep_satOrFieldInv_realDecayRate
    (lambda step : ℝ) :
    SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step)) =
      (realDecayResidual lambda step)⁻¹ := by
  have hkeep_eq :
      SatOrFieldAlgebra.keep (realDecayRate lambda step) =
        realDecayResidual lambda step := by
    unfold SatOrFieldAlgebra.keep realDecayRate
    ring
  have hres : realDecayResidual lambda step ≠ 0 := by
    unfold realDecayResidual
    exact (Real.exp_pos _).ne'
  have hkeep :
      SatOrFieldAlgebra.keep (realDecayRate lambda step) ≠ 0 := by
    rw [hkeep_eq]
    exact hres
  rw [keep_satOrFieldInv_eq_inv_keep hkeep]
  rw [hkeep_eq]

/-! ## Sampled inverse orbit -/

/-- THEOREM 3: after `N` inverse sampled steps, the zero-origin orbit's
headroom is the reciprocal continuous residual at total sampled time. -/
theorem headroom_bumpSatField_iterate_zero_inv_realDecayRate_eq_exp_growth
    (lambda step : ℝ) (N : ℕ) :
    (1 : ℝ) -
        (fun z : ℝ =>
          bumpSatField z
            (SatOrFieldAlgebra.satOrFieldInv
              (realDecayRate lambda step)))^[N] 0 =
      (realDecayResidual lambda ((N : ℝ) * step))⁻¹ := by
  rw [headroom_bumpSatField_iterate_zero_eq_keep_pow]
  rw [keep_satOrFieldInv_realDecayRate]
  rw [realDecayResidual_nat_mul]
  rw [inv_pow]

/-- THEOREM 4: the inverse sampled zero-origin orbit itself is
`1 - exp(lambda * N * step)` in residual notation. -/
theorem bumpSatField_iterate_zero_inv_realDecayRate_eq_one_sub_exp_growth
    (lambda step : ℝ) (N : ℕ) :
    (fun z : ℝ =>
      bumpSatField z
        (SatOrFieldAlgebra.satOrFieldInv
          (realDecayRate lambda step)))^[N] 0 =
      1 - (realDecayResidual lambda ((N : ℝ) * step))⁻¹ := by
  have h :=
    headroom_bumpSatField_iterate_zero_inv_realDecayRate_eq_exp_growth
      lambda step N
  linarith

/-- THEOREM 5: with positive sampled scale, inverse sampled iteration makes
the headroom coordinate diverge. -/
theorem tendsto_inv_realDecayRate_headroom_atTop
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    Tendsto
      (fun N : ℕ =>
        (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z
              (SatOrFieldAlgebra.satOrFieldInv
                (realDecayRate lambda step)))^[N] 0)
      atTop atTop :=
  tendsto_inverse_bumpSatField_iterate_zero_headroom_atTop
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)

/-! ## Bundled receipt -/

/-- A compact receipt for the sampled inverse saturation law: noisy-OR inverse
turns the sampled continuous residual into its reciprocal, and positive sampled
scale diverges in the headroom coordinate. -/
structure SampledInverseSaturationReceipt : Prop where
  inverse_keep_closed :
    ∀ lambda step : ℝ,
      SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step)) =
        (realDecayResidual lambda step)⁻¹
  inverse_headroom_closed :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z
              (SatOrFieldAlgebra.satOrFieldInv
                (realDecayRate lambda step)))^[N] 0 =
        (realDecayResidual lambda ((N : ℝ) * step))⁻¹
  inverse_orbit_closed :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (fun z : ℝ =>
        bumpSatField z
          (SatOrFieldAlgebra.satOrFieldInv
            (realDecayRate lambda step)))^[N] 0 =
        1 - (realDecayResidual lambda ((N : ℝ) * step))⁻¹
  inverse_headroom_diverges :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      Tendsto
        (fun N : ℕ =>
          (1 : ℝ) -
            (fun z : ℝ =>
              bumpSatField z
                (SatOrFieldAlgebra.satOrFieldInv
                  (realDecayRate lambda step)))^[N] 0)
        atTop atTop

/-- THEOREM 6: the sampled inverse saturation receipt. -/
theorem sampledInverseSaturationReceipt :
    SampledInverseSaturationReceipt where
  inverse_keep_closed :=
    keep_satOrFieldInv_realDecayRate
  inverse_headroom_closed :=
    headroom_bumpSatField_iterate_zero_inv_realDecayRate_eq_exp_growth
  inverse_orbit_closed :=
    bumpSatField_iterate_zero_inv_realDecayRate_eq_one_sub_exp_growth
  inverse_headroom_diverges :=
    fun _ _ hpos => tendsto_inv_realDecayRate_headroom_atTop hpos

end

end AffineRelaxation
end SaturationMonoid
