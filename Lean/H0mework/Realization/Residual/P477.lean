/-
  Proposition 477: saturation increment accounting.

  The slogan "loss is gain" has a precise algebraic core.  A fixed positive
  saturation rate consumes headroom in geometric slices:

      increment n = sigma * (1 - sigma)^n.

  The finite cumulative gain telescopes to

      sum_{n<N} sigma * (1 - sigma)^n = 1 - (1 - sigma)^N,

  hence for `0 < sigma < 1` it tends to `1`.  The same carrier also explains
  the dangerous inverse direction: the noisy-OR inverse of a positive
  non-absorbing rate is negative, its keep-rate is greater than one, and its
  residual powers diverge.

  Boundary: this is an accounting theorem for the saturation carrier.  It does
  not identify physical energy, mass, or consciousness with this scalar without
  an additional producer/interpretation certificate.
-/

import H0mework.Realization.RelaxationFlow.P476
import H0mework.Realization.RelaxationAlgebra.P298

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

open Filter
open scoped BigOperators

/-! ## Forward geometric accounting -/

/-- The per-step saturation increment after `n` previous fixed-rate steps. -/
def saturationIncrement (sigma : ℝ) (n : ℕ) : ℝ :=
  sigma * (1 - sigma) ^ n

/-- The cumulative saturation increment over the first `N` steps. -/
def cumulativeSaturationIncrement (sigma : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, saturationIncrement sigma n

/-- THEOREM 1: finite saturation increments telescope exactly to consumed
headroom. -/
theorem cumulativeSaturationIncrement_eq_one_sub_keep_pow
    (sigma : ℝ) (N : ℕ) :
    cumulativeSaturationIncrement sigma N =
      1 - (1 - sigma) ^ N := by
  induction N with
  | zero =>
      simp [cumulativeSaturationIncrement]
  | succ N ih =>
      rw [cumulativeSaturationIncrement, Finset.sum_range_succ]
      rw [show
        (∑ n ∈ Finset.range N, saturationIncrement sigma n) =
          cumulativeSaturationIncrement sigma N by
          rfl]
      rw [ih]
      simp [saturationIncrement, pow_succ]
      ring

/-- THEOREM 2: cumulative gain plus remaining keep is exactly one. -/
theorem cumulativeSaturationIncrement_add_keep_pow
    (sigma : ℝ) (N : ℕ) :
    cumulativeSaturationIncrement sigma N + (1 - sigma) ^ N = 1 := by
  rw [cumulativeSaturationIncrement_eq_one_sub_keep_pow]
  ring

/-- THEOREM 3: for any nontrivial forward rate `0 < sigma < 1`, cumulative
gain tends to total headroom `1`. -/
theorem tendsto_cumulativeSaturationIncrement_one
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
      atTop (nhds 1) := by
  have habs : |1 - sigma| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hpow :
      Tendsto (fun N : ℕ => (1 - sigma) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
  have hclosed :
      (fun N : ℕ => cumulativeSaturationIncrement sigma N) =
        fun N : ℕ => 1 - (1 - sigma) ^ N := by
    funext N
    exact cumulativeSaturationIncrement_eq_one_sub_keep_pow sigma N
  rw [hclosed]
  simpa using tendsto_const_nhds.sub hpow

/-! ## Inverse-direction accounting -/

/-- THEOREM 4: the noisy-OR inverse of a positive non-absorbing rate in `(0,1)`
is negative. -/
theorem satOrFieldInv_neg_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    SatOrFieldAlgebra.satOrFieldInv sigma < 0 := by
  unfold SatOrFieldAlgebra.satOrFieldInv
  exact div_neg_of_pos_of_neg hpos (by linarith)

/-- THEOREM 5: the keep-rate of that inverse is greater than one. -/
theorem keep_satOrFieldInv_gt_one_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    1 < SatOrFieldAlgebra.keep
      (SatOrFieldAlgebra.satOrFieldInv sigma) := by
  have hneg := satOrFieldInv_neg_of_mem_Ioo hpos hlt
  unfold SatOrFieldAlgebra.keep
  linarith

/-- THEOREM 6: inverse-direction residual powers diverge. -/
theorem tendsto_inverse_keep_pow_atTop
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    Tendsto
      (fun N : ℕ =>
        (SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N)
      atTop atTop := by
  exact tendsto_pow_atTop_atTop_of_one_lt
    (keep_satOrFieldInv_gt_one_of_mem_Ioo hpos hlt)

/-! ## Bundled receipt -/

/-- A compact receipt for saturation increment accounting: forward positive
rates exhaust exactly one unit of headroom in the limit, while their noisy-OR
inverse has a divergent keep coordinate. -/
structure SaturationIncrementAccountingReceipt : Prop where
  finite_telescoping :
    ∀ sigma : ℝ, ∀ N : ℕ,
      cumulativeSaturationIncrement sigma N =
        1 - (1 - sigma) ^ N
  finite_balance :
    ∀ sigma : ℝ, ∀ N : ℕ,
      cumulativeSaturationIncrement sigma N + (1 - sigma) ^ N = 1
  forward_limit :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
        atTop (nhds 1)
  inverse_negative :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      SatOrFieldAlgebra.satOrFieldInv sigma < 0
  inverse_keep_gt_one :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      1 < SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv sigma)
  inverse_keep_diverges :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      Tendsto
        (fun N : ℕ =>
          (SatOrFieldAlgebra.keep
            (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N)
        atTop atTop

/-- THEOREM 7: the saturation increment accounting receipt. -/
theorem saturationIncrementAccountingReceipt :
    SaturationIncrementAccountingReceipt where
  finite_telescoping :=
    cumulativeSaturationIncrement_eq_one_sub_keep_pow
  finite_balance :=
    cumulativeSaturationIncrement_add_keep_pow
  forward_limit :=
    fun _ hpos hlt =>
      tendsto_cumulativeSaturationIncrement_one hpos hlt
  inverse_negative :=
    fun _ hpos hlt =>
      satOrFieldInv_neg_of_mem_Ioo hpos hlt
  inverse_keep_gt_one :=
    fun _ hpos hlt =>
      keep_satOrFieldInv_gt_one_of_mem_Ioo hpos hlt
  inverse_keep_diverges :=
    fun _ hpos hlt =>
      tendsto_inverse_keep_pow_atTop hpos hlt

end

end AffineRelaxation
end SaturationMonoid
