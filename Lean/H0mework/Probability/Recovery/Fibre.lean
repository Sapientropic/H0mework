import H0mework.Probability.Recovery.Conditional

/-! Exact source fibres specialize the existing full conditional PMF, including its weights. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.ObservationRefinement

open scoped Classical

noncomputable section

universe u v

variable {Source : Type u} {Observed : Type v}
variable (source : PMF Source) (read : Source → Observed)

theorem conditional_injective (injective : Function.Injective read) (point : Source) (positive : source point ≠ 0) :
    SourceConditionalHistory.conditional source read (read point) (observed_supported source read point positive) =
      PMF.pure point := by
  have weight : observed source read (read point) = source point := by
    rw [observed, PMF.map_apply, tsum_eq_single point]
    · exact if_pos rfl
    · intro candidate different
      exact if_neg (fun same => different (injective same).symm)
  apply PMF.ext
  intro candidate
  rw [SourceConditionalHistory.conditional_apply, weight, PMF.pure_apply]
  by_cases same : candidate = point
  · subst candidate
    rw [if_pos rfl, if_pos rfl]
    exact ENNReal.mul_inv_cancel positive (source.apply_ne_top point)
  · rw [if_neg (fun equal => same (injective equal)), if_neg same]

theorem conditional_constant (atom : Observed) (constant : ∀ point, read point = atom)
    (supported : atom ∈ (observed source read).support) :
    SourceConditionalHistory.conditional source read atom supported = source := by
  have law : observed source read = PMF.pure atom := by
    have same : read = Function.const Source atom := funext constant
    rw [observed, same, PMF.map_const]
  apply PMF.ext
  intro point
  rw [SourceConditionalHistory.conditional_apply, constant, if_pos rfl]
  change source point * (observed source read atom)⁻¹ = source point
  rw [law]
  simp

variable [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem optimum_injective (injective : Function.Injective read) (task : Source → ℂ)
    (point : Source) (positive : source point ≠ 0) :
    optimalDecoder source read task (read point) = task point := by
  rw [optimal_is_conditional source read task (read point) (observed_supported source read point positive),
    conditionalMean, conditional_injective source read injective point positive, Finset.sum_eq_single point]
  · simp
  · intro candidate _ different
    rw [PMF.pure_apply, if_neg different]
    simp
  · intro absent
    exact (absent (Finset.mem_univ point)).elim

end
end SourceWeightedRecovery.ObservationRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
