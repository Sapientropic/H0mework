import H0mework.Probability.Source.ConditionalNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNext

open SourceWeightedRecovery
open scoped InnerProductSpace
noncomputable section

universe u v w
variable {Source : Type u} [Fintype Source] {Next : Type w}
variable (source : PMF Source) (nextRead : Source → Next) (decode : Next → ℂ) (sourceError : Source → ℂ)

theorem next_decoder_error :
    error source nextRead ((decode ∘ nextRead) + sourceError) decode =
      ∑ point, (source point).toReal * ‖sourceError point‖ ^ 2 := by
  simp only [error, Pi.add_apply, Function.comp_apply, add_sub_cancel_left]

variable [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable {Observed : Type v} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
variable (read : Source → Observed)

omit [MeasurableSingletonClass Observed] in
theorem residual_error_sum (source : PMF Source) (read : Source → Observed)
    (nextRead : Source → Next) (decode : Next → ℂ) (sourceError : Source → ℂ) :
    residual source read (taskValue source ((decode ∘ nextRead) + sourceError)) =
      residual source read (taskValue source (decode ∘ nextRead)) +
        residual source read (taskValue source sourceError) :=
  (residual source read).map_add (taskValue source (decode ∘ nextRead)) (taskValue source sourceError)

variable [Fintype Next] [MeasurableSpace Next] [MeasurableSingletonClass Next]

theorem optimal_with_source_error (source : PMF Source) (read : Source → Observed)
    (nextRead : Source → Next) (decode : Next → ℂ) (sourceError : Source → ℂ)
    (value : Observed) (supported : value ∈ (source.map read).support) :
    optimalDecoder source read ((decode ∘ nextRead) + sourceError) value =
      mean source read nextRead decode value supported + optimalDecoder source read sourceError value := by
  have linear := (transfer source read).map_add
    (taskValue source (decode ∘ nextRead)) (taskValue source sourceError)
  have evaluated := congrArg (evalAt (source.map read) value supported) linear
  have added := (evalAt (source.map read) value supported).map_add
    (transfer source read (taskValue source (decode ∘ nextRead)))
    (transfer source read (taskValue source sourceError))
  exact (evaluated.trans added).trans (congrArg (fun result : ℂ => result + optimalDecoder source read sourceError value)
    (optimal_is_mean source read nextRead decode value supported))

theorem residual_error_square (source : PMF Source) (read : Source → Observed)
    (nextRead : Source → Next) (decode : Next → ℂ) (sourceError : Source → ℂ)
    (positive : ∀ point, point ∈ source.support) :
    ‖residual source read (taskValue source ((decode ∘ nextRead) + sourceError))‖ ^ 2 =
      (∑ point, (source point).toReal * variance source read nextRead decode (read point)
        (observed_supported source read point (positive point))) +
      ‖residual source read (taskValue source sourceError)‖ ^ 2 +
      2 * (⟪residual source read (taskValue source (decode ∘ nextRead)),
        residual source read (taskValue source sourceError)⟫_ℂ).re := by
  rw [residual_error_sum, norm_add_sq (𝕜 := ℂ), residual_variance source read nextRead decode positive]
  simp only [RCLike.re_to_complex]
  ring

end
end SourceConditionalNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
