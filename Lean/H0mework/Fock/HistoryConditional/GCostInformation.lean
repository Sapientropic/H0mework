import H0mework.Fock.HistoryConditional.GCostVariance

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalInventory (values)
noncomputable section
variable {Observed : Type*} [DecidableEq Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [DecidableEq Observed] in
theorem error_account (bound : Nat) (query : Fin (bound + 1) → Observed) (decoder : Observed → SourceJointClockGraph.Carrier) :
    (∑ i, (historyPMF bound i).toReal * ‖values bound i - decoder (query i)‖ ^ 2) =
      SourceConditionalInventory.cost bound query / (bound + 1 : ℝ) +
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (SourceJointClockGraph.clock ∘ values bound))‖ ^ 2 +
      ∑ i, (historyPMF bound i).toReal *
        ‖SourceVectorMoment.mean (SourceConditionalHistory.conditional (historyPMF bound) query (query i)
          (observed_supported _ _ i (SourceUniformFibreVariance.source_positive bound i))) (values bound) - decoder (query i)‖ ^ 2 := by
  have source := SourceVectorMoment.conditional_error (historyPMF bound) query
    (SourceUniformFibreVariance.source_positive bound) (values bound) decoder
  change (∑ i, (historyPMF bound i).toReal * ‖values bound i - decoder (query i)‖ ^ 2) =
    totalVariance bound query + _ at source
  rw [full_variance_cost] at source
  exact source

omit [DecidableEq Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed] in
theorem clock_signal (bound : Nat) :
    (SourceJointClockGraph.clock ∘ values bound) = (fun index : Fin (bound + 1) => (((index.val : ℝ) + 2 : ℝ) : ℂ)) := by
  funext index
  rw [Function.comp_apply, actual_clock]
  push_cast
  rfl

theorem clock_information_lower (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy bound query) - 1) / 12 ≤
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (SourceJointClockGraph.clock ∘ values bound))‖ ^ 2 := by
  have source := SourceUniformFibreVariance.Separation.information_spread bound query
    (fun index => (index.val : ℝ) + 2) 1 (by intro left right; ring_nf; exact le_rfl)
  rw [clock_signal]
  convert source using 1
  ring

theorem information_lower (bound : Nat) (query : Fin (bound + 1) → Observed) :
    SourceConditionalInventory.cost bound query / (bound + 1 : ℝ) +
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy bound query) - 1) / 12 ≤ totalVariance bound query := by
  rw [full_variance_cost]
  exact add_le_add le_rfl (clock_information_lower bound query)

theorem decoder_information_lower (bound : Nat) (query : Fin (bound + 1) → Observed) (decoder : Observed → SourceJointClockGraph.Carrier) :
    SourceConditionalInventory.cost bound query / (bound + 1 : ℝ) +
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy bound query) - 1) / 12 ≤
      ∑ i, (historyPMF bound i).toReal * ‖values bound i - decoder (query i)‖ ^ 2 := by
  have generated := information_lower bound query
  rw [full_variance_cost] at generated
  rw [error_account]
  exact generated.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
