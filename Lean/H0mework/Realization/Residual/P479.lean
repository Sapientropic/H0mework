/-
  Proposition 479: infinite saturation series accounting.

  P477 proved finite telescoping sums and P478 tied those sums to the actual
  zero-origin `bumpSatField` orbit.  This file records the corresponding
  infinite-series theorem:

      HasSum (fun n => sigma * (1 - sigma)^n) 1.

  Thus every nontrivial forward rate `0 < sigma < 1`, however small, exhausts
  exactly one unit of headroom over infinitely many steps.

  Boundary: this remains a scalar saturation-carrier theorem.  It does not
  identify the scalar series with physical energy, mass, or consciousness
  without a separate producer/interpretation certificate.
-/

import H0mework.Realization.Residual.P478

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

open scoped BigOperators

/-! ## Infinite forward accounting -/

/-- THEOREM 1: for every nontrivial forward rate, the per-step saturation
increments sum to exactly one unit of headroom. -/
theorem hasSum_saturationIncrement_one
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    HasSum (saturationIncrement sigma) 1 := by
  have hkeep_nonneg : 0 ≤ 1 - sigma := by
    linarith
  have hkeep_lt_one : 1 - sigma < 1 := by
    linarith
  have hgeom :
      HasSum (fun n : ℕ => (1 - sigma) ^ n) (1 - (1 - sigma))⁻¹ :=
    hasSum_geometric_of_lt_one hkeep_nonneg hkeep_lt_one
  have hscaled :
      HasSum (fun n : ℕ => sigma * (1 - sigma) ^ n)
        (sigma * (1 - (1 - sigma))⁻¹) := by
    simpa [smul_eq_mul] using hgeom.mul_left sigma
  convert hscaled using 1
  · ext n
    simp [saturationIncrement]
  · have hden : 1 - (1 - sigma) = sigma := by ring
    rw [hden]
    exact (mul_inv_cancel₀ hpos.ne').symm

/-- THEOREM 2: the saturation increment stream is summable for every
nontrivial forward rate. -/
theorem summable_saturationIncrement
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    Summable (saturationIncrement sigma) :=
  (hasSum_saturationIncrement_one hpos hlt).summable

/-- THEOREM 3: the infinite `tsum` of saturation increments is one. -/
theorem tsum_saturationIncrement_eq_one
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    (∑' n : ℕ, saturationIncrement sigma n) = 1 :=
  (hasSum_saturationIncrement_one hpos hlt).tsum_eq

/-! ## Tail accounting -/

/-- THEOREM 4: after `N` steps, the remaining infinite tail of future
increments sums to the remaining headroom `(1 - sigma)^N`. -/
theorem hasSum_saturationIncrement_tail_keep_pow
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) (N : ℕ) :
    HasSum (fun k : ℕ => saturationIncrement sigma (N + k))
      ((1 - sigma) ^ N) := by
  have hone := hasSum_saturationIncrement_one hpos hlt
  have hscaled :
      HasSum (fun k : ℕ =>
        (1 - sigma) ^ N * saturationIncrement sigma k)
        ((1 - sigma) ^ N * 1) := by
    simpa [smul_eq_mul] using hone.mul_left ((1 - sigma) ^ N)
  convert hscaled using 1
  · ext k
    simp [saturationIncrement, pow_add, mul_left_comm]
  · ring

/-- THEOREM 5: the tail `tsum` after `N` steps is the remaining headroom. -/
theorem tsum_saturationIncrement_tail_eq_keep_pow
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) (N : ℕ) :
    (∑' k : ℕ, saturationIncrement sigma (N + k)) =
      (1 - sigma) ^ N :=
  (hasSum_saturationIncrement_tail_keep_pow hpos hlt N).tsum_eq

/-! ## Arbitrarily small positive rates -/

/-- THEOREM 6: no positive lower bound on the rate is needed.  For any
positive threshold `epsilon`, there is a rate below it whose infinite
saturation accounting still sums to exactly one. -/
theorem exists_arbitrarily_small_rate_hasSum_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ sigma : ℝ,
      0 < sigma ∧ sigma < epsilon ∧ sigma < 1 ∧
        HasSum (saturationIncrement sigma) 1 := by
  let sigma : ℝ := min epsilon 1 / 2
  have hmin_pos : 0 < min epsilon 1 := by
    exact lt_min hepsilon zero_lt_one
  have hpos : 0 < sigma := by
    dsimp [sigma]
    linarith
  have hlt_epsilon : sigma < epsilon := by
    dsimp [sigma]
    have hle : min epsilon 1 ≤ epsilon := min_le_left _ _
    linarith
  have hlt_one : sigma < 1 := by
    dsimp [sigma]
    have hle : min epsilon 1 ≤ (1 : ℝ) := min_le_right _ _
    linarith
  exact ⟨sigma, hpos, hlt_epsilon, hlt_one,
    hasSum_saturationIncrement_one hpos hlt_one⟩

/-! ## Bundled receipt -/

/-- A compact receipt for the infinite-series form of saturation accounting:
positive non-absorbing rates sum to one unit of headroom, their tails are the
remaining headroom, and such rates can be chosen below any positive bound. -/
structure InfiniteSaturationSeriesReceipt : Prop where
  hasSum_one :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      HasSum (saturationIncrement sigma) 1
  summable :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      Summable (saturationIncrement sigma)
  tsum_eq_one :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      (∑' n : ℕ, saturationIncrement sigma n) = 1
  tail_hasSum_keep :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 -> ∀ N : ℕ,
      HasSum (fun k : ℕ => saturationIncrement sigma (N + k))
        ((1 - sigma) ^ N)
  tail_tsum_keep :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 -> ∀ N : ℕ,
      (∑' k : ℕ, saturationIncrement sigma (N + k)) =
        (1 - sigma) ^ N
  arbitrarily_small :
    ∀ epsilon : ℝ, 0 < epsilon ->
      ∃ sigma : ℝ,
        0 < sigma ∧ sigma < epsilon ∧ sigma < 1 ∧
          HasSum (saturationIncrement sigma) 1

/-- THEOREM 7: the infinite saturation-series accounting receipt. -/
theorem infiniteSaturationSeriesReceipt :
    InfiniteSaturationSeriesReceipt where
  hasSum_one :=
    fun _ hpos hlt => hasSum_saturationIncrement_one hpos hlt
  summable :=
    fun _ hpos hlt => summable_saturationIncrement hpos hlt
  tsum_eq_one :=
    fun _ hpos hlt => tsum_saturationIncrement_eq_one hpos hlt
  tail_hasSum_keep :=
    fun _ hpos hlt N =>
      hasSum_saturationIncrement_tail_keep_pow hpos hlt N
  tail_tsum_keep :=
    fun _ hpos hlt N =>
      tsum_saturationIncrement_tail_eq_keep_pow hpos hlt N
  arbitrarily_small :=
    fun _ hepsilon =>
      exists_arbitrarily_small_rate_hasSum_one hepsilon

end

end AffineRelaxation
end SaturationMonoid
