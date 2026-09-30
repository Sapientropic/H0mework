import H0mework.Probability.Recovery.Error

/-! The existing weighted error equation computes the gain of an actual observation refinement. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.ObservationRefinement

noncomputable section

universe u v w

variable {Source : Type u} [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable {Fine : Type v} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type w} [MeasurableSpace Coarse]
variable (source : PMF Source) (fine : Source → Fine) (forget : Fine → Coarse)

omit [MeasurableSpace Source] [MeasurableSingletonClass Source] [MeasurableSpace Coarse] in
theorem error_zero_iff_of_positive (read : Source → Coarse)
    (positive : ∀ point : Source, (source point).toReal ≠ 0)
    (task : Source → ℂ) (decoder : Coarse → ℂ) :
    error source read task decoder = 0 ↔
      ∀ point : Source, task point = decoder (read point) := by
  unfold error
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))]
  constructor
  · intro all point
    have zero := (mul_eq_zero.mp (all point (Finset.mem_univ point))).resolve_left
      (positive point)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp zero))
  · intro all point _
    rw [all point, sub_self, norm_zero]
    simp

omit [MeasurableSpace Coarse] in
theorem decoder_error (task : Source → ℂ) (decoder : Coarse → ℂ) :
    error source (forget ∘ fine) task decoder =
      error source fine task (optimalDecoder source fine task) +
        error source (forget ∘ fine) (fun point => optimalDecoder source fine task (fine point)) decoder :=
  error_decomposition source fine task (decoder ∘ forget)

theorem optimal_gain (task : Source → ℂ) :
    error source (forget ∘ fine) task (optimalDecoder source (forget ∘ fine) task) =
      error source fine task (optimalDecoder source fine task) +
        error source (forget ∘ fine) (fun point => optimalDecoder source fine task (fine point))
          (optimalDecoder source (forget ∘ fine) task) :=
  decoder_error source fine forget task _

end
end SourceWeightedRecovery.ObservationRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
