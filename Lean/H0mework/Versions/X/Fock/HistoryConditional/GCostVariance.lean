import H0mework.Versions.X.Fock.HistoryConditional.GCostGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalInventory (values)
noncomputable section
variable {Observed : Type*} [DecidableEq Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

def totalVariance (bound : Nat) (query : Fin (bound + 1) → Observed) : ℝ :=
  ∑ i, (historyPMF bound i).toReal * SourceVectorMoment.variance
    (SourceConditionalHistory.conditional (historyPMF bound) query (query i)
      (observed_supported _ _ i (SourceUniformFibreVariance.source_positive bound i))) (values bound)

omit [DecidableEq Observed] in
theorem scalar_variance (bound : Nat) (query : Fin (bound + 1) → Observed) (decode : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ) :
    (∑ i, (historyPMF bound i).toReal * SourceVectorMoment.variance
      (SourceConditionalHistory.conditional (historyPMF bound) query (query i)
        (observed_supported _ _ i (SourceUniformFibreVariance.source_positive bound i))) (decode ∘ values bound)) =
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (decode ∘ values bound))‖ ^ 2 := by
  have source := SourceConditionalNext.residual_variance (historyPMF bound) query id (decode ∘ values bound)
    (SourceUniformFibreVariance.source_positive bound)
  simpa only [SourceConditionalNext.variance_is_conditional, SourceConditionalNext.mean_is_conditional,
    conditionalMean, SourceVectorMoment.variance, SourceVectorMoment.error, SourceVectorMoment.mean,
    Function.comp_def, id_eq, Complex.real_smul, smul_eq_mul] using source.symm

omit [DecidableEq Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem native_variance_parts (bound : Nat) (p : PMF (Fin (bound + 1))) :
    SourceVectorMoment.variance p (values bound) =
      (∑ actor : Fin (bound + 1), SourceVectorMoment.variance p ((coordinateRead (actor.val + 1)).toLinearMap ∘ values bound)) +
        SourceVectorMoment.variance p (SourceJointClockGraph.clock.toLinearMap ∘ values bound) := by
  simp only [SourceVectorMoment.variance, SourceVectorMoment.error, SourceVectorMoment.mean_map, Function.comp_apply]
  simp only [← map_sub]
  rw [show (∑ i, (p i).toReal * ‖values bound i - SourceVectorMoment.mean p (values bound)‖ ^ 2) =
      ∑ i, (p i).toReal * ((∑ actor : Fin (bound + 1), ‖coordinateRead (actor.val + 1)
        (values bound i - SourceVectorMoment.mean p (values bound))‖ ^ 2) +
        ‖SourceJointClockGraph.clock (values bound i - SourceVectorMoment.mean p (values bound))‖ ^ 2) by
      apply Finset.sum_congr rfl
      intro i _
      rw [centered_norm]]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

omit [DecidableEq Observed] in
theorem full_variance_cost (bound : Nat) (query : Fin (bound + 1) → Observed) :
    totalVariance bound query = SourceConditionalInventory.cost bound query / (bound + 1 : ℝ) +
      ‖residual (historyPMF bound) query
        (taskValue (historyPMF bound) (SourceJointClockGraph.clock ∘ values bound))‖ ^ 2 := by
  simp only [totalVariance, native_variance_parts, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [scalar_variance]
  exact congrArg (fun result : ℝ => result +
    ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (SourceJointClockGraph.clock ∘ values bound))‖ ^ 2)
      (coordinate_cost bound query)

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
