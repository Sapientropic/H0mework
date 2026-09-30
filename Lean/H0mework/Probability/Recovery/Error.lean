import H0mework.Probability.Recovery.Conditional

/-! Any raw decoder's finite source error decomposes around the generated conditional optimum. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

open MeasureTheory

noncomputable section

universe u v

variable {Source : Type u} [Fintype Source] {Observed : Type v}
variable (source : PMF Source) (observer : Source → Observed)

def error (task : Source → ℂ) (decoder : Observed → ℂ) : ℝ :=
  ∑ point : Source, (source point).toReal * ‖task point - decoder (observer point)‖ ^ 2

variable [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem error_eq_norm (task : Source → ℂ) (decoder : Observed → ℂ) :
    error source observer task decoder =
      ‖taskValue source task - pullback source observer (decoderValue source observer decoder)‖ ^ 2 := by
  rw [error, norm_source_sq]
  apply Finset.sum_congr rfl
  intro point _
  by_cases zero : source point = 0
  · simp only [zero, ENNReal.toReal_zero, zero_mul]
  · have evaluated := (evalAt source point zero).map_sub (taskValue source task)
      (pullback source observer (decoderValue source observer decoder))
    change (taskValue source task - pullback source observer (decoderValue source observer decoder)) point =
      taskValue source task point - pullback source observer (decoderValue source observer decoder) point at evaluated
    rw [evaluated, taskValue_at source task point zero, pullback_at source observer _ point zero,
      decoderValue_at source observer decoder (observer point) (observed_supported source observer point zero)]

theorem deviation_eq_norm (value : Space (observed source observer)) (decoder : Observed → ℂ) :
    error source observer (fun point => value (observer point)) decoder =
      ‖value - decoderValue source observer decoder‖ ^ 2 := by
  rw [← (pullback source observer).norm_map (value - decoderValue source observer decoder), error, norm_source_sq]
  apply Finset.sum_congr rfl
  intro point _
  by_cases zero : source point = 0
  · simp only [zero, ENNReal.toReal_zero, zero_mul]
  · rw [pullback_at source observer _ point zero]
    have supported := observed_supported source observer point zero
    have evaluated := (evalAt (observed source observer) (observer point) supported).map_sub value
      (decoderValue source observer decoder)
    change (value - decoderValue source observer decoder) (observer point) =
      value (observer point) - decoderValue source observer decoder (observer point) at evaluated
    rw [evaluated, decoderValue_at source observer decoder (observer point) supported]

theorem residual_decomposition (task : Source → ℂ) (decoder : Observed → ℂ) :
    error source observer task decoder = ‖residual source observer (taskValue source task)‖ ^ 2 +
      error source observer (fun point => optimalDecoder source observer task (observer point)) decoder := by
  change error source observer task decoder = _ +
    error source observer (fun point => transfer source observer (taskValue source task) (observer point)) decoder
  rw [error_eq_norm, deviation_eq_norm]
  exact IsometricRetainedTransfer.decoder_error_decomposition (pullback source observer)
    (taskValue source task) (decoderValue source observer decoder)

theorem optimal_attains (task : Source → ℂ) :
    error source observer task (optimalDecoder source observer task) =
      ‖residual source observer (taskValue source task)‖ ^ 2 := by
  rw [residual_decomposition]
  simp [error]

theorem error_decomposition (task : Source → ℂ) (decoder : Observed → ℂ) :
    error source observer task decoder = error source observer task (optimalDecoder source observer task) +
      error source observer (fun point => optimalDecoder source observer task (observer point)) decoder := by
  rw [residual_decomposition, optimal_attains]

theorem optimal_lower_bound (task : Source → ℂ) (decoder : Observed → ℂ) :
    error source observer task (optimalDecoder source observer task) ≤ error source observer task decoder := by
  rw [error_decomposition source observer task decoder]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun point _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
