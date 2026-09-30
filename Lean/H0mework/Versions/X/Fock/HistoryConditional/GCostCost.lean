import H0mework.Versions.X.Fock.HistoryConditional.GCostSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGInformationCost

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
noncomputable section
variable {Observed : Type*} [DecidableEq Observed] [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [DecidableEq Observed] [MeasurableSingletonClass Observed] in
theorem unit_residual (bound : Nat) (query : Fin (bound + 1) → Observed) (actor : Fin (bound + 1)) :
    ‖residual (historyPMF bound) query
      (taskValue (historyPMF bound) (fun index => (SourceConditionalInventory.unitTask bound actor index : ℂ)))‖ ^ 2 =
      (bound + 1 : ℝ) * ‖residual (historyPMF bound) query
        (taskValue (historyPMF bound) (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)))‖ ^ 2 := by
  rw [unit_original_coordinate, map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ bound + 1)]

omit [DecidableEq Observed] [MeasurableSingletonClass Observed] in
theorem coordinate_cost (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (∑ actor : Fin (bound + 1), ‖residual (historyPMF bound) query
      (taskValue (historyPMF bound) (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)))‖ ^ 2) =
      SourceConditionalInventory.cost bound query / (bound + 1 : ℝ) := by
  have source : SourceConditionalInventory.cost bound query =
      (bound + 1 : ℝ) * ∑ actor : Fin (bound + 1), ‖residual (historyPMF bound) query
        (taskValue (historyPMF bound) (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)))‖ ^ 2 := by
    simp only [SourceConditionalInventory.cost, unit_residual, Finset.mul_sum]
  apply (eq_div_iff (by positivity : (bound + 1 : ℝ) ≠ 0)).mpr
  rw [mul_comm]
  exact source.symm

theorem coordinate_cost_exact (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (∑ actor : Fin (bound + 1), ‖residual (historyPMF bound) query
      (taskValue (historyPMF bound) (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)))‖ ^ 2) =
      ((bound + 1 : ℝ) - (SourceUniformFibreVariance.outputs bound query).card) / (bound + 1 : ℝ) := by
  rw [coordinate_cost, SourceConditionalInventory.cost_eq]

theorem coordinate_information (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (∑ actor : Fin (bound + 1), ‖residual (historyPMF bound) query
      (taskValue (historyPMF bound) (fun index => coordinateRead (actor.val + 1) (SourceConditionalInventory.values bound index)))‖ ^ 2) ≤
      SourceUniformFibreInformation.conditionalEntropy bound query := by
  rw [coordinate_cost]
  exact SourceConditionalInventory.information_cost bound query

end
end SourceGInformationCost
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
