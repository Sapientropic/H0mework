import H0mework.Probability.Information.InventorySource
import H0mework.Probability.Source.HistoryGrowth
import H0mework.Probability.Information.Entropy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery SourceUniformFibreVariance
open SourceUniformFibreInformation SourceGeneratedAtomicObservation MeasureTheory
open scoped Classical
noncomputable section

theorem unit_is_original_cotest (bound : Nat) (actor : Fin (bound + 1)) :
    taskValue (historyPMF bound) (fun index => (unitTask bound actor index : ℂ)) =
      (Real.sqrt (bound + 1 : ℝ) : ℂ) • cotest (historyPMF bound) actor := by
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro index
  rw [taskValue_at _ _ _ (source_positive bound index)]
  change (unitTask bound actor index : ℂ) =
    evalAt (historyPMF bound) index (source_positive bound index)
      ((Real.sqrt (bound + 1 : ℝ) : ℂ) • cotest (historyPMF bound) actor)
  rw [map_smul]
  change (unitTask bound actor index : ℂ) =
    (Real.sqrt (bound + 1 : ℝ) : ℂ) * cotest (historyPMF bound) actor index
  rw [SourceHistoryGrowth.cotest_value]
  by_cases same : index = actor <;> simp [unitTask, same]

theorem unit_norm (bound : Nat) (actor : Fin (bound + 1)) :
    ‖taskValue (historyPMF bound) (fun index => (unitTask bound actor index : ℂ))‖ = 1 := by
  rw [unit_is_original_cotest, norm_smul, cotest_norm, source_weight,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    one_div, Real.sqrt_inv, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < bound + 1)).ne']

variable {Observed : Type*} [DecidableEq Observed]
  [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem all_decoder_error (bound : Nat) (query : Fin (bound + 1) → Observed)
    (decoder : Fin (bound + 1) → Observed → ℂ) :
    (∑ actor, error (historyPMF bound) query (fun index => (unitTask bound actor index : ℂ)) (decoder actor)) =
      (bound + 1 : ℝ) - (outputs bound query).card +
        ∑ actor, error (historyPMF bound) query
          (fun index => optimalDecoder (historyPMF bound) query
            (fun point => (unitTask bound actor point : ℂ)) (query index)) (decoder actor) := by
  have generated := congrArg (fun values : Fin (bound + 1) → ℝ => ∑ actor, values actor)
    (funext (fun actor => residual_decomposition (historyPMF bound) query
      (fun index => (unitTask bound actor index : ℂ)) (decoder actor)))
  change (∑ actor, error (historyPMF bound) query (fun index => (unitTask bound actor index : ℂ)) (decoder actor)) =
    ∑ actor, (‖residual (historyPMF bound) query
      (taskValue (historyPMF bound) (fun index => (unitTask bound actor index : ℂ)))‖ ^ 2 +
      error (historyPMF bound) query (fun index => optimalDecoder (historyPMF bound) query
        (fun point => (unitTask bound actor point : ℂ)) (query index)) (decoder actor)) at generated
  rw [Finset.sum_add_distrib, ← cost, cost_eq] at generated
  exact generated

theorem all_decoder_lower (bound : Nat) (query : Fin (bound + 1) → Observed)
    (decoder : Fin (bound + 1) → Observed → ℂ) :
    (bound + 1 : ℝ) - (outputs bound query).card ≤
      ∑ actor, error (historyPMF bound) query (fun index => (unitTask bound actor index : ℂ)) (decoder actor) := by
  rw [all_decoder_error]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

theorem exact_inventory (bound : Nat) (query : Fin (bound + 1) → Observed)
    (injective : Function.Injective query) : cost bound query = 0 := by
  rw [cost_eq, outputs, Finset.card_image_of_injective _ injective]
  simp

theorem information_cost (bound : Nat) (query : Fin (bound + 1) → Observed) :
    cost bound query / (bound + 1 : ℝ) ≤ conditionalEntropy bound query := by
  rw [cost_eq, conditional_entropy_formula]
  have counts : (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ)) = bound + 1 := by
    exact_mod_cast fibre_card_sum bound query
  have source : ((bound + 1 : ℝ) - (outputs bound query).card) / (bound + 1 : ℝ) =
      ∑ value ∈ outputs bound query, (((fibre bound query value).card : ℝ) - 1) / (bound + 1 : ℝ) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, counts]
    simp
  rw [source]
  apply Finset.sum_le_sum
  intro value present
  have positive := positive_card bound query value present
  have generated := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos positive)
    (div_nonneg positive.le (by positivity : (0 : ℝ) ≤ bound + 1))
  have paid : ((fibre bound query value).card : ℝ) / (bound + 1 : ℝ) *
      (1 - ((fibre bound query value).card : ℝ)⁻¹) =
        (((fibre bound query value).card : ℝ) - 1) / (bound + 1 : ℝ) := by
    field_simp
  exact paid.symm.trans_le generated

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
