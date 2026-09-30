import H0mework.Chemistry.LAlanineBandCache.SaturationBounds

/-! The original squaring recurrence reaches its exact smallest positive grid interval. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation

open SourceExponential

private def upperFrom (bound : ℚ) : ℕ → ℚ
  | 0 => bound
  | n+1 => roundUp (upperFrom bound n ^ 2)

private theorem upperSequence_pos {x : ℚ} (small : |x| ≤ 1/2) (n : ℕ) :
    0 < upperSequence x n := by
  have h := (Real.exp_pos _).trans_le (sequence_contains x small n).2.2
  exact_mod_cast h

private theorem lowerSequence_le_upper {x : ℚ} (small : |x| ≤ 1/2) (n : ℕ) :
    lowerSequence x n ≤ upperSequence x n := by
  have h := (sequence_contains x small n).2.1.trans (sequence_contains x small n).2.2
  exact_mod_cast h

private theorem upperSequence_le {x bound : ℚ} (small : |x| ≤ 1/2)
    (initial : initialUpper x ≤ bound) (n : ℕ) : upperSequence x n ≤ upperFrom bound n := by
  induction n with
  | zero => exact initial
  | succ n ih =>
      apply roundUp_mono
      simpa only [pow_two] using mul_self_le_mul_self (upperSequence_pos small n).le ih

private theorem roundDown_eq_zero {a : ℚ} (nonnegative : 0 ≤ a) (small : a < 1/scale) :
    roundDown a = 0 := by
  have product : scale*a < 1 := by
    have h := (lt_div_iff₀ scale_positive).mp small
    simpa only [mul_comm] using h
  have rounded : ⌊scale*a⌋ = (0:ℤ) := Int.floor_eq_iff.mpr (by
    simpa only [Int.cast_zero, zero_add] using
      And.intro (mul_nonneg scale_positive.le nonnegative) product)
  simp only [roundDown, rounded, Int.cast_zero, zero_div]

private theorem roundUp_eq_unit {a : ℚ} (positive : 0 < a) (small : a ≤ 1/scale) :
    roundUp a = 1/scale := by
  have product : scale*a ≤ 1 := by
    have h := (le_div_iff₀ scale_positive).mp small
    simpa only [mul_comm] using h
  have rounded : ⌈scale*a⌉ = (1:ℤ) := Int.ceil_eq_iff.mpr (by
    simpa only [Int.cast_one, sub_self] using
      And.intro (mul_pos scale_positive positive) product)
  simp only [roundUp, rounded, Int.cast_one]

private theorem sequences_saturate {x bound : ℚ} (small : |x| ≤ 1/2)
    (initial : initialUpper x ≤ bound) (n : ℕ)
    (cut : upperFrom bound n ^ 2 < 1/scale) :
    lowerSequence x (n+1) = 0 ∧ upperSequence x (n+1) = 1/scale := by
  have upper := upperSequence_le small initial n
  have lower := (lowerSequence_le_upper small n).trans upper
  have lower_nonneg := (sequence_contains x small n).1
  have lower_square : lowerSequence x n ^ 2 ≤ upperFrom bound n ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self lower_nonneg lower
  have upper_square : upperSequence x n ^ 2 ≤ upperFrom bound n ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (upperSequence_pos small n).le upper
  constructor
  · exact roundDown_eq_zero (sq_nonneg _) (lower_square.trans_lt cut)
  · exact roundUp_eq_unit (sq_pos_of_pos (upperSequence_pos small n))
      (upper_square.trans_lt cut).le

private theorem sequences_saturated_add {x : ℚ} {k : ℕ}
    (base : lowerSequence x k = 0 ∧ upperSequence x k = 1/scale) (n : ℕ) :
    lowerSequence x (k+n) = 0 ∧ upperSequence x (k+n) = 1/scale := by
  induction n with
  | zero => simpa only [Nat.add_zero] using base
  | succ n ih =>
      rw [Nat.add_succ, lowerSequence, upperSequence, ih.1, ih.2]
      exact ⟨by decide +kernel, by decide +kernel⟩

/-- Eight squarings suffice throughout this interval of reduced source arguments. -/
theorem sequences_saturated_eight {x : ℚ} {k : ℕ} (small : |x| ≤ 1/2)
    (upper : x ≤ -7/16) (depth : 8 ≤ k) :
    lowerSequence x k = 0 ∧ upperSequence x k = 1/scale := by
  have base := sequences_saturate small (initialUpper_le_eight small upper)
    7 (by decide +kernel)
  have split : k = 8+(k-8) := by omega
  rw [split]
  exact sequences_saturated_add base (k-8)

/-- Nine squarings suffice throughout the wider interval needed by the other groups. -/
theorem sequences_saturated_nine {x : ℚ} {k : ℕ} (small : |x| ≤ 1/2)
    (upper : x ≤ -7/32) (depth : 9 ≤ k) :
    lowerSequence x k = 0 ∧ upperSequence x k = 1/scale := by
  have base := sequences_saturate small (initialUpper_le_nine small upper)
    8 (by decide +kernel)
  have split : k = 9+(k-9) := by omega
  rw [split]
  exact sequences_saturated_add base (k-9)

/-- A raw argument and its original reduction determine the exact saturated leaf. -/
theorem leaf_saturated {a : ℚ} {k : ℕ}
    (small : |reducedArgument a k| ≤ 1/2)
    (upper : (k = 8 ∧ reducedArgument a k ≤ -7/16) ∨
      (9 ≤ k ∧ reducedArgument a k ≤ -7/32)) :
    leafLower a k = 0 ∧ leafUpper a k = 1/scale := by
  rcases upper with ⟨depth, upper⟩ | ⟨depth, upper⟩
  · exact sequences_saturated_eight small upper (by omega)
  · exact sequences_saturated_nine small upper depth

end LAlanine40K2025.BasinRefinement.WholeBandSaturation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
