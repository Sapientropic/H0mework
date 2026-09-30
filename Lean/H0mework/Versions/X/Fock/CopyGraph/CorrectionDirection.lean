import H0mework.Versions.X.Fock.CopyGraph.CorrectionEquation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def ratio (bound : Nat) : ℝ := (bound + 1 : ℝ) / (bound + 2 : ℝ)

def direction (bound : Nat) (query : Fin (bound + 1) → Observed) : Space (observed (historyPMF bound) query) :=
  clockMean bound query - ((ratio bound : ℂ) * inner ℂ (one bound query) (clockMean bound query)) • one bound query

def coupling (bound : Nat) (query : Fin (bound + 1) → Observed) : ℝ :=
  ‖clockMean bound query‖ ^ 2 - ratio bound * ‖inner ℂ (one bound query) (clockMean bound query)‖ ^ 2

theorem ratio_nonneg (bound : Nat) : 0 ≤ ratio bound := by unfold ratio; positivity

theorem ratio_lt_one (bound : Nat) : ratio bound < 1 := by
  unfold ratio
  exact (div_lt_one (by positivity : (0 : ℝ) < bound + 2)).mpr (by linarith)

theorem coupling_nonneg (bound : Nat) (query : Fin (bound + 1) → Observed) : 0 ≤ coupling bound query := by
  have cauchy := norm_inner_le_norm (𝕜 := ℂ) (one bound query) (clockMean bound query)
  rw [one_norm, one_mul] at cauchy
  have square := pow_le_pow_left₀ (norm_nonneg _) cauchy 2
  unfold coupling
  have boundCost := mul_le_mul_of_nonneg_right (ratio_lt_one bound).le
    (sq_nonneg ‖inner ℂ (one bound query) (clockMean bound query)‖)
  nlinarith only [square, boundCost]

theorem direction_pairing (bound : Nat) (query : Fin (bound + 1) → Observed) :
    inner ℂ (clockMean bound query) (direction bound query) = (coupling bound query : ℂ) := by
  unfold direction coupling
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have cross : inner ℂ (one bound query) (clockMean bound query) *
      inner ℂ (clockMean bound query) (one bound query) =
        (‖inner ℂ (one bound query) (clockMean bound query)‖ : ℂ) ^ 2 := by
    rw [← inner_conj_symm (clockMean bound query) (one bound query), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  push_cast
  linear_combination -(ratio bound : ℂ) * cross

theorem direction_law (bound : Nat) (query : Fin (bound + 1) → Observed) :
    direction bound query + ((bound + 1 : ℂ) * inner ℂ (one bound query) (direction bound query)) • one bound query =
      clockMean bound query := by
  have unit : inner ℂ (one bound query) (one bound query) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, one_norm]
    norm_num
  unfold direction
  rw [inner_sub_right, inner_smul_right, unit, mul_one, sub_eq_add_neg, ← neg_smul, add_assoc, ← add_smul]
  have coefficient : -((ratio bound : ℂ) * inner ℂ (one bound query) (clockMean bound query)) +
      (bound + 1 : ℂ) * (inner ℂ (one bound query) (clockMean bound query) -
        (ratio bound : ℂ) * inner ℂ (one bound query) (clockMean bound query)) = 0 := by
    unfold ratio
    push_cast
    have denominator : (bound + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : bound + 2 ≠ 0)
    field_simp
    ring
  rw [coefficient, zero_smul, add_zero]

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
