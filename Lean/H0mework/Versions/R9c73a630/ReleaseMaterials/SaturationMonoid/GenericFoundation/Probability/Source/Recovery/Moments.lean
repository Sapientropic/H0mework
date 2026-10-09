import H0mework.Probability.Recovery.Conditional

/-! The complete conditional optimum preserves the source task's weighted first moment. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery

noncomputable section

universe u v

variable {Source : Type u} [Fintype Source] [MeasurableSpace Source] [MeasurableSingletonClass Source]
variable {Observed : Type v} [Fintype Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
variable (source : PMF Source) (observer : Source → Observed) (task : Source → ℂ)

theorem optimal_first_moment :
    ∑ atom : Observed, (observed source observer atom).toReal • optimalDecoder source observer task atom =
      ∑ point : Source, (source point).toReal • task point := by
  simp_rw [weighted_optimal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  simp only [← Finset.smul_sum]
  apply congrArg ((source point).toReal • ·)
  rw [Finset.sum_eq_single (observer point)]
  · simp
  · intro other _ distinct
    exact if_neg (Ne.symm distinct)
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

end
end SourceWeightedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
