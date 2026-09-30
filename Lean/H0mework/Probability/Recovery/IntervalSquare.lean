import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceIntervalSquare

noncomputable section

def lower (left right : ℝ) : ℝ := (max 0 left) ^ 2 + (min 0 right) ^ 2

def upper (left right : ℝ) : ℝ := max (left ^ 2) (right ^ 2)

theorem bounds {left value right : ℝ} (lo : left ≤ value) (hi : value ≤ right) :
    lower left right ≤ value ^ 2 ∧ value ^ 2 ≤ upper left right := by
  constructor
  · by_cases nonnegative : 0 ≤ left
    · have rightNonnegative : 0 ≤ right := nonnegative.trans (lo.trans hi)
      simp only [lower, max_eq_right nonnegative, min_eq_left rightNonnegative, zero_pow (by decide : 2 ≠ 0), add_zero]
      nlinarith
    · have leftNonpositive := le_of_lt (lt_of_not_ge nonnegative)
      by_cases nonpositive : right ≤ 0
      · simp only [lower, max_eq_left leftNonpositive, min_eq_right nonpositive, zero_pow (by decide : 2 ≠ 0), zero_add]
        nlinarith
      · have rightNonnegative := le_of_lt (lt_of_not_ge nonpositive)
        simp only [lower, max_eq_left leftNonpositive, min_eq_left rightNonnegative,
          zero_pow (by decide : 2 ≠ 0), zero_add]
        exact sq_nonneg value
  · by_cases nonnegative : 0 ≤ value
    · have square : value ^ 2 ≤ right ^ 2 := by nlinarith
      exact square.trans (le_max_right _ _)
    · have nonpositive : value ≤ 0 := le_of_lt (lt_of_not_ge nonnegative)
      have square : value ^ 2 ≤ left ^ 2 := by nlinarith
      exact square.trans (le_max_left _ _)

end
end SourceIntervalSquare
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
