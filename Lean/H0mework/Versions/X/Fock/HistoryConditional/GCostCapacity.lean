import H0mework.Versions.X.Fock.HistoryConditional.GCostInformation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalInventory (values)
noncomputable section
variable {Observed : Type*} [Fintype Observed] [DecidableEq Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem clock_capacity_lower (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (((bound + 1 : ℝ) / Fintype.card Observed) ^ 2 - 1) / 12 ≤
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (SourceJointClockGraph.clock ∘ values bound))‖ ^ 2 := by
  have source := SourceUniformFibreInformation.Capacity.residual_capacity_lower bound query
    (fun index => (index.val : ℝ) + 2) 1 (by intro left right; ring_nf; exact le_rfl)
  rw [clock_signal]
  convert source using 1
  ring

theorem capacity_lower (bound : Nat) (query : Fin (bound + 1) → Observed) :
    ((bound + 1 : ℝ) - (SourceUniformFibreVariance.outputs bound query).card) / (bound + 1 : ℝ) +
      (((bound + 1 : ℝ) / Fintype.card Observed) ^ 2 - 1) / 12 ≤ totalVariance bound query := by
  rw [full_variance_cost, SourceConditionalInventory.cost_eq]
  exact add_le_add le_rfl (clock_capacity_lower bound query)

theorem decoder_capacity_lower (bound : Nat) (query : Fin (bound + 1) → Observed) (decoder : Observed → SourceJointClockGraph.Carrier) :
    ((bound + 1 : ℝ) - (SourceUniformFibreVariance.outputs bound query).card) / (bound + 1 : ℝ) +
      (((bound + 1 : ℝ) / Fintype.card Observed) ^ 2 - 1) / 12 ≤
      ∑ i, (historyPMF bound i).toReal * ‖values bound i - decoder (query i)‖ ^ 2 := by
  have generated := capacity_lower bound query
  rw [full_variance_cost] at generated
  rw [error_account]
  exact generated.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
