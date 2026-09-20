/-
  Proposition 478: vacuum-origin saturation orbit accounting.

  P477 proves the accounting identity

      sum_{n<N} sigma * (1 - sigma)^n = 1 - (1 - sigma)^N.

  This file ties that sum back to the actual saturation operator.  Starting
  from the empty/rate-zero state `0`, the N-step `bumpSatField` orbit is exactly
  that cumulative gain.  Thus "from zero, a tiny positive rate eventually
  consumes all headroom" is not a separate slogan; it is the operator orbit.

  It also records the inverse side without adding physical interpretation:
  for `0 < sigma < 1`, iterating the noisy-OR inverse makes the headroom
  coordinate diverge.
-/

import H0mework.Realization.Residual.P477

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

open Filter

/-! ## Forward orbit from zero -/

/-- THEOREM 1: the actual `bumpSatField` orbit from zero has the same closed
form as the cumulative geometric accounting. -/
theorem bumpSatField_iterate_zero_eq_one_sub_keep_pow
    (sigma : ℝ) (N : ℕ) :
    (fun z : ℝ => bumpSatField z sigma)^[N] 0 =
      1 - (1 - sigma) ^ N := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      unfold bumpSatField
      rw [pow_succ]
      ring

/-- THEOREM 2: the actual `bumpSatField` orbit from zero is exactly the
cumulative saturation increment from P477. -/
theorem bumpSatField_iterate_zero_eq_cumulativeSaturationIncrement
    (sigma : ℝ) (N : ℕ) :
    (fun z : ℝ => bumpSatField z sigma)^[N] 0 =
      cumulativeSaturationIncrement sigma N := by
  rw [bumpSatField_iterate_zero_eq_one_sub_keep_pow]
  rw [cumulativeSaturationIncrement_eq_one_sub_keep_pow]

/-- THEOREM 3: for every nontrivial forward rate, the actual orbit from zero
tends to the absorbing state `1`. -/
theorem tendsto_bumpSatField_iterate_zero_one
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    Tendsto (fun N : ℕ =>
      (fun z : ℝ => bumpSatField z sigma)^[N] 0) atTop (nhds 1) := by
  have horbit :
      (fun N : ℕ => (fun z : ℝ => bumpSatField z sigma)^[N] 0) =
        fun N : ℕ => cumulativeSaturationIncrement sigma N := by
    funext N
    exact bumpSatField_iterate_zero_eq_cumulativeSaturationIncrement sigma N
  rw [horbit]
  exact tendsto_cumulativeSaturationIncrement_one hpos hlt

/-! ## Inverse orbit headroom -/

/-- THEOREM 4: the headroom of a zero-origin orbit is the keep power. -/
theorem headroom_bumpSatField_iterate_zero_eq_keep_pow
    (sigma : ℝ) (N : ℕ) :
    (1 : ℝ) - (fun z : ℝ => bumpSatField z sigma)^[N] 0 =
      SatOrFieldAlgebra.keep sigma ^ N := by
  rw [bumpSatField_iterate_zero_eq_one_sub_keep_pow]
  unfold SatOrFieldAlgebra.keep
  ring

/-- THEOREM 5: iterating the noisy-OR inverse of a positive non-absorbing rate
from zero makes the headroom/residual coordinate diverge. -/
theorem tendsto_inverse_bumpSatField_iterate_zero_headroom_atTop
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    Tendsto
      (fun N : ℕ =>
        (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma))^[N] 0)
      atTop atTop := by
  have hhead :
      (fun N : ℕ =>
        (1 : ℝ) -
          (fun z : ℝ =>
            bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma))^[N] 0) =
        fun N : ℕ =>
          (SatOrFieldAlgebra.keep
            (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N := by
    funext N
    exact headroom_bumpSatField_iterate_zero_eq_keep_pow
      (SatOrFieldAlgebra.satOrFieldInv sigma) N
  rw [hhead]
  exact tendsto_inverse_keep_pow_atTop hpos hlt

/-! ## Bundled receipt -/

/-- A compact receipt that the P477 cumulative accounting is literally the
zero-origin `bumpSatField` orbit, and that inverse-rate iteration diverges in
headroom coordinates. -/
structure VacuumOrbitAccountingReceipt : Prop where
  orbit_closed :
    ∀ sigma : ℝ, ∀ N : ℕ,
      (fun z : ℝ => bumpSatField z sigma)^[N] 0 =
        1 - (1 - sigma) ^ N
  orbit_eq_cumulative :
    ∀ sigma : ℝ, ∀ N : ℕ,
      (fun z : ℝ => bumpSatField z sigma)^[N] 0 =
        cumulativeSaturationIncrement sigma N
  orbit_tends_one :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      Tendsto (fun N : ℕ =>
        (fun z : ℝ => bumpSatField z sigma)^[N] 0) atTop (nhds 1)
  headroom_closed :
    ∀ sigma : ℝ, ∀ N : ℕ,
      (1 : ℝ) - (fun z : ℝ => bumpSatField z sigma)^[N] 0 =
        SatOrFieldAlgebra.keep sigma ^ N
  inverse_headroom_diverges :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      Tendsto
        (fun N : ℕ =>
          (1 : ℝ) -
            (fun z : ℝ =>
              bumpSatField z (SatOrFieldAlgebra.satOrFieldInv sigma))^[N] 0)
        atTop atTop

/-- THEOREM 6: the vacuum-orbit accounting receipt. -/
theorem vacuumOrbitAccountingReceipt :
    VacuumOrbitAccountingReceipt where
  orbit_closed :=
    bumpSatField_iterate_zero_eq_one_sub_keep_pow
  orbit_eq_cumulative :=
    bumpSatField_iterate_zero_eq_cumulativeSaturationIncrement
  orbit_tends_one :=
    fun _ hpos hlt =>
      tendsto_bumpSatField_iterate_zero_one hpos hlt
  headroom_closed :=
    headroom_bumpSatField_iterate_zero_eq_keep_pow
  inverse_headroom_diverges :=
    fun _ hpos hlt =>
      tendsto_inverse_bumpSatField_iterate_zero_headroom_atTop hpos hlt

end

end AffineRelaxation
end SaturationMonoid
