/-
  Proposition 143: shifted power tails have a first-three-point obstruction.

  The executable forgetting harness includes the Murre-Chessa / Anderson-Tweney
  gamma-mixture curve

      A(t) = (1 + b t)^(-a).

  Full formalization of the continuous gamma integral / Laplace-transform
  theorem is still out of scope for this file.  This proposition proves the
  next algebraic bridge that is already enough for the first-three-point
  obstruction language: for positive scale `b` and positive integer exponent
  `m`, the discrete shifted-power sequence

      Aₙ = (1 + b n)^(-m)

  has strictly positive first-three residual `A₀ A₂ - A₁²`.  Therefore it
  cannot be explained by a single geometric/exponential first-three fit.
-/

import H0mework.Realization.Relations.P128

/-! ## Shifted power tail -/

/-- Discrete shifted-power retention `Aₙ = (1 + scale * n)^(-exponent)`. -/
def shiftedPowerRetention
    {α : Type*} [DivisionSemiring α]
    (scale : α) (exponent n : Nat) : α :=
  ((1 + scale * (n : α)) ^ exponent)⁻¹

/-! ## First-three obstruction -/

/-- THEOREM 1: shifted-power tails with positive scale and positive integer
exponent have a strictly positive first-three residual. -/
theorem shiftedPowerRetention_first_three_residual_pos
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {scale : α} {exponent : Nat}
    (hscale : 0 < scale) (hexponent : 0 < exponent) :
    0 <
      shiftedPowerRetention scale exponent 0 *
        shiftedPowerRetention scale exponent 2 -
      (shiftedPowerRetention scale exponent 1) ^ 2 := by
  have hbase1_pos : 0 < 1 + scale := by positivity
  have hbase2_pos : 0 < 1 + scale * (2 : α) := by positivity
  have hbase_lt : 1 + scale * (2 : α) < (1 + scale) ^ 2 := by
    nlinarith [sq_pos_of_pos hscale]
  have hpow_lt :
      (1 + scale * (2 : α)) ^ exponent < ((1 + scale) ^ 2) ^ exponent := by
    exact pow_lt_pow_left₀ hbase_lt (le_of_lt hbase2_pos)
      (Nat.ne_of_gt hexponent)
  have hpow_pos : 0 < (1 + scale * (2 : α)) ^ exponent := by positivity
  have hpow_sq_pos : 0 < ((1 + scale) ^ 2) ^ exponent := by positivity
  have hinv_lt :
      (((1 + scale) ^ 2) ^ exponent)⁻¹ <
        ((1 + scale * (2 : α)) ^ exponent)⁻¹ := by
    exact (inv_lt_inv₀ hpow_sq_pos hpow_pos).2 hpow_lt
  have hsq :
      ((1 + scale) ^ exponent)⁻¹ ^ 2 =
        (((1 + scale) ^ 2) ^ exponent)⁻¹ := by
    rw [inv_pow]
    congr 1
    rw [← pow_mul, ← pow_mul]
    rw [Nat.mul_comm]
  have hzero :
      shiftedPowerRetention scale exponent 0 = 1 := by
    simp [shiftedPowerRetention]
  have hone :
      shiftedPowerRetention scale exponent 1 = ((1 + scale) ^ exponent)⁻¹ := by
    norm_num [shiftedPowerRetention]
  have htwo :
      shiftedPowerRetention scale exponent 2 =
        ((1 + scale * (2 : α)) ^ exponent)⁻¹ := by
    norm_num [shiftedPowerRetention]
  rw [hzero, hone, htwo, one_mul, hsq]
  exact sub_pos.mpr hinv_lt

/-- THEOREM 2: shifted-power tails with positive scale and positive integer
exponent refute every single-geometric first-three fit. -/
theorem shiftedPowerRetention_refutes_single_geometric_first_three
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {scale : α} {exponent : Nat}
    (hscale : 0 < scale) (hexponent : 0 < exponent) :
    ¬ FitsSingleGeometricFirstThree
      (fun n => shiftedPowerRetention scale exponent n) := by
  have hpos := shiftedPowerRetention_first_three_residual_pos
    (scale := scale) (exponent := exponent) hscale hexponent
  have hres :
      shiftedPowerRetention scale exponent 0 *
        shiftedPowerRetention scale exponent 2 -
      (shiftedPowerRetention scale exponent 1) ^ 2 ≠ 0 := ne_of_gt hpos
  intro hfit
  exact hres (moment_zero_of_fitsSingleGeometricFirstThree hfit)

/-!
  The theorem above is intentionally kept at the sequence level.  It proves
  the same first-three obstruction shape as P127, but for the shifted-power
  curve used by the executable gamma-mixture harness.  It does not prove the
  continuous gamma-mixture integral identity itself.
-/
