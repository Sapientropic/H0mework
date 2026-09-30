import H0mework.Probability.Information.SeparationIndices
import H0mework.Probability.Information.Pairwise
import H0mework.Probability.Information.Entropy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreVariance.Separation

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped Classical
noncomputable section

theorem time_pair_spread {total : Nat} (indices : Finset (Fin total)) (time : Fin total → ℝ) (scale : ℝ)
    (separated : ∀ left right, scale ^ 2 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 ≤
      (time right - time left) ^ 2) :
    scale ^ 2 * ((indices.card : ℝ) ^ 2 * ((indices.card : ℝ) ^ 2 - 1) / 6) ≤
      ∑ left ∈ indices, ∑ right ∈ indices, (time right - time left) ^ 2 := by
  calc
    _ ≤ scale ^ 2 * ∑ left ∈ indices, ∑ right ∈ indices, ((right.val : ℝ) - (left.val : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (fibre_pair_square indices) (sq_nonneg scale)
    _ ≤ _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact separated left right

variable {Observed : Type*} [DecidableEq Observed]
  [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem residual_spread (bound : Nat) (query : Fin (bound + 1) → Observed)
    (time : Fin (bound + 1) → ℝ) (scale : ℝ)
    (separated : ∀ left right, scale ^ 2 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 ≤
      (time right - time left) ^ 2) :
    scale ^ 2 / (12 * (bound + 1 : ℝ)) *
        (∑ value ∈ outputs bound query,
          (fibre bound query value).card * (((fibre bound query value).card : ℝ) ^ 2 - 1)) ≤
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (fun actor => (time actor : ℂ)))‖ ^ 2 := by
  rw [residual_pairwise]
  have individual (value : Observed) (present : value ∈ outputs bound query) :
      scale ^ 2 / 6 * ((fibre bound query value).card * (((fibre bound query value).card : ℝ) ^ 2 - 1)) ≤
        ((fibre bound query value).card : ℝ)⁻¹ *
          ∑ left ∈ fibre bound query value, ∑ right ∈ fibre bound query value, (time right - time left) ^ 2 := by
    have cardPositive := positive_card bound query value present
    have generated := time_pair_spread (fibre bound query value) time scale separated
    calc
      _ = ((fibre bound query value).card : ℝ)⁻¹ *
          (scale ^ 2 * (((fibre bound query value).card : ℝ) ^ 2 *
            (((fibre bound query value).card : ℝ) ^ 2 - 1) / 6)) := by
          field_simp [cardPositive.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left generated (inv_nonneg.mpr cardPositive.le)
  have totals := Finset.sum_le_sum individual
  have weighted := mul_le_mul_of_nonneg_left totals (by positivity : 0 ≤ (1 / (2 * (bound + 1 : ℝ))))
  rw [← Finset.mul_sum] at weighted
  have coefficients : scale ^ 2 / (12 * (bound + 1 : ℝ)) =
      (1 / (2 * (bound + 1 : ℝ))) * (scale ^ 2 / 6) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [coefficients, mul_assoc]
  exact weighted

theorem information_spread (bound : Nat) (query : Fin (bound + 1) → Observed)
    (time : Fin (bound + 1) → ℝ) (scale : ℝ)
    (separated : ∀ left right, scale ^ 2 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 ≤
      (time right - time left) ^ 2) :
    scale ^ 2 / 12 * (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy bound query) - 1) ≤
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (fun actor => (time actor : ℂ)))‖ ^ 2 := by
  have entropy := SourceUniformFibreInformation.entropy_spread_lower bound query (scale / 2)
  have normalized :
      scale ^ 2 / 12 * (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy bound query) - 1) ≤
        scale ^ 2 / (12 * (bound + 1 : ℝ)) *
          (∑ value ∈ outputs bound query, (fibre bound query value).card *
            (((fibre bound query value).card : ℝ) ^ 2 - 1)) := by
    have first : (scale / 2) ^ 2 / 3 = scale ^ 2 / 12 := by ring
    have second : (scale / 2) ^ 2 / (3 * (bound + 1 : ℝ)) = scale ^ 2 / (12 * (bound + 1 : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [first, second] at entropy
    exact entropy
  exact normalized.trans (residual_spread bound query time scale separated)

end
end SourceUniformFibreVariance.Separation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
