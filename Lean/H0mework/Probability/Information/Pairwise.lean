import H0mework.Probability.Information.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreVariance

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped Classical
noncomputable section

variable {Observed : Type*} [DecidableEq Observed]
  [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem fibre_error_pairwise (bound : Nat) (query : Fin (bound + 1) → Observed)
    (task : Fin (bound + 1) → ℝ) (value : Observed)
    (supported : value ∈ ((historyPMF bound).map query).support) :
    (∑ index ∈ fibre bound query value,
      ‖(task index : ℂ) - optimalDecoder (historyPMF bound) query (fun point => (task point : ℂ)) value‖ ^ 2) =
      (1 / (2 * ((fibre bound query value).card : ℝ))) *
        ∑ left ∈ fibre bound query value, ∑ right ∈ fibre bound query value,
          (task right - task left) ^ 2 := by
  rw [optimalDecoder_fibre_mean bound query task value supported]
  simp_rw [real_norm_square]
  exact mean_pairwise (fibre bound query value) task

omit [MeasurableSingletonClass Observed] in
theorem error_fibre_sum (bound : Nat) (query : Fin (bound + 1) → Observed)
    (task : Fin (bound + 1) → ℝ) :
    error (historyPMF bound) query (fun index => (task index : ℂ))
        (optimalDecoder (historyPMF bound) query (fun index => (task index : ℂ))) =
      (1 / (bound + 1 : ℝ)) * ∑ value ∈ outputs bound query, ∑ index ∈ fibre bound query value,
        ‖(task index : ℂ) - optimalDecoder (historyPMF bound) query (fun point => (task point : ℂ)) value‖ ^ 2 := by
  rw [error]
  simp_rw [source_weight]
  rw [← Finset.mul_sum]
  apply congrArg (fun total : ℝ => (1 / (bound + 1 : ℝ)) * total)
  have partition := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin (bound + 1)))) (t := outputs bound query) (g := query)
    (fun index _ => Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
    (fun index => ‖(task index : ℂ) -
      optimalDecoder (historyPMF bound) query (fun point => (task point : ℂ)) (query index)‖ ^ 2)
  apply partition.symm.trans
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro index inside
  rw [(fibre_mem bound query value index).mp inside]

theorem residual_pairwise (bound : Nat) (query : Fin (bound + 1) → Observed)
    (task : Fin (bound + 1) → ℝ) :
    ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (fun index => (task index : ℂ)))‖ ^ 2 =
      (1 / (2 * (bound + 1 : ℝ))) *
        ∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ)⁻¹ *
          ∑ left ∈ fibre bound query value, ∑ right ∈ fibre bound query value,
            (task right - task left) ^ 2 := by
  rw [← optimal_attains, error_fibre_sum]
  calc
    _ = (1 / (bound + 1 : ℝ)) *
        ∑ value ∈ outputs bound query, (1 / (2 * ((fibre bound query value).card : ℝ))) *
          ∑ left ∈ fibre bound query value, ∑ right ∈ fibre bound query value,
            (task right - task left) ^ 2 := by
      apply congrArg (fun total : ℝ => (1 / (bound + 1 : ℝ)) * total)
      apply Finset.sum_congr rfl
      intro value present
      exact fibre_error_pairwise bound query task value (output_supported bound query value present)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro value _
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

omit [DecidableEq Observed] in
theorem decoder_lower (bound : Nat) (query : Fin (bound + 1) → Observed)
    (task : Fin (bound + 1) → ℝ) (decoder : Observed → ℂ) :
    ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (fun index => (task index : ℂ)))‖ ^ 2 ≤
      error (historyPMF bound) query (fun index => (task index : ℂ)) decoder := by
  rw [residual_decomposition]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun point _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

end
end SourceUniformFibreVariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
