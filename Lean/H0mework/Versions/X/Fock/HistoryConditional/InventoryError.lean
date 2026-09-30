import H0mework.Versions.X.Fock.HistoryConditional.InventorySource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability
noncomputable section

theorem sum_count (bound : Nat) (cost : Fin (bound + 1) → ℝ) :
    ((bound + 1 : Nat) : ℝ) * (∑ i, (historyPMF bound i).toReal * cost i) = ∑ i, cost i := by
  have nonzero : (bound : ℝ) + 1 ≠ 0 := by positivity
  simp only [Finset.mul_sum, historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]

theorem error_count {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (bound : Nat) (value : Fin (bound + 1) → E) (guess : E) :
    ((bound + 1 : Nat) : ℝ) * SourceVectorMoment.error (historyPMF bound) value guess =
      ∑ i, ‖value i - guess‖ ^ 2 := sum_count bound _

theorem error_append (bound : Nat) (guess : SourceJointClockGraph.Carrier) :
    ((bound + 2 : Nat) : ℝ) * SourceVectorMoment.error (historyPMF (bound + 1)) (values (bound + 1)) guess =
      ((bound + 1 : Nat) : ℝ) * SourceVectorMoment.error (historyPMF bound) (values bound) guess + ‖born bound - guess‖ ^ 2 := by
  change ((bound + 1 + 1 : Nat) : ℝ) * SourceVectorMoment.error (historyPMF (bound + 1)) (values (bound + 1)) guess = _
  rw [error_count, error_count, Fin.sum_univ_castSucc]
  simp only [values_retained, born]

theorem variance_append (bound : Nat) :
    ((bound + 2 : Nat) : ℝ) * SourceVectorMoment.variance (historyPMF (bound + 1)) (values (bound + 1)) +
      ((bound + 2 : Nat) : ℝ) * ‖SourceVectorMoment.mean (historyPMF (bound + 1)) (values (bound + 1)) -
        SourceVectorMoment.mean (historyPMF bound) (values bound)‖ ^ 2 =
      ((bound + 1 : Nat) : ℝ) * SourceVectorMoment.variance (historyPMF bound) (values bound) +
        ‖born bound - SourceVectorMoment.mean (historyPMF bound) (values bound)‖ ^ 2 := by
  have paid := error_append bound (SourceVectorMoment.mean (historyPMF bound) (values bound))
  rw [SourceVectorMoment.error_decomposition (historyPMF (bound + 1)), mul_add] at paid
  exact paid

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
