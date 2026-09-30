import H0mework.Fock.HistoryModel.DynamicHilbertConditional
import H0mework.Fock.HistoryModel.DynamicHilbertSeparation
import H0mework.Probability.Recovery.Fibre

/-! Actual prime separation pays full actor recovery; fresh letters do not receive an invented information gain. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability MeasureTheory

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := measurable depth
local instance (depth : Nat) : BorelSpace (Complete.Carrier depth) := ⟨rfl⟩
local instance (depth : Nat) : T2Space (Complete.Carrier depth) := field_t2 depth

theorem read_injective (depth bound : Nat) : Function.Injective (read depth bound) := by
  intro left right same
  exact Fin.ext (point_runtime_injective depth same)

theorem actor_posterior (depth bound : Nat) (index : Fin (bound + 1))
    (supported : read depth bound index ∈ (law depth bound).support) :
    SourceConditionalHistory.conditional (historyPMF bound) (read depth bound)
      (read depth bound index) supported = PMF.pure index :=
  ObservationRefinement.conditional_injective (historyPMF bound) (read depth bound)
    (read_injective depth bound) index (by simp [historyPMF])

theorem complete_recovery (depth bound : Nat) (task : Fin (bound + 1) → ℂ) (index : Fin (bound + 1)) :
    transfer (historyPMF bound) (read depth bound) (taskValue (historyPMF bound) task)
      (read depth bound index) = task index :=
  ObservationRefinement.optimum_injective (historyPMF bound) (read depth bound)
    (read_injective depth bound) task index (by simp [historyPMF])

theorem complete_residual_zero (depth bound : Nat) (value : Space (historyPMF bound)) :
    residual (historyPMF bound) (read depth bound) value = 0 := by
  have original : taskValue (historyPMF bound) (fun index => value index) = value :=
    Lp.toLp_coeFn value (task_memLp (historyPMF bound) (fun index => value index))
  have attained := (optimal_attains (historyPMF bound) (read depth bound) (fun index => value index)).symm
  have exactRead (index : Fin (bound + 1)) :
      optimalDecoder (historyPMF bound) (read depth bound) (fun index => value index) (read depth bound index) = value index :=
    complete_recovery depth bound (fun index => value index) index
  simp only [original, error, exactRead, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero] at attained
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (residual (historyPMF bound) (read depth bound) value)]

theorem restriction_residual_zero (depth bound : Nat) (value : Space (law (depth + 1) bound)) :
    IsometricRetainedTransfer.residual (restriction depth bound) value = 0 := by
  have composed := original_residual_energy depth bound (pullback (historyPMF bound) (read (depth + 1) bound) value)
  simp only [complete_residual_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    SourceWeightedRecovery.transfer, IsometricRetainedTransfer.transfer_pullback] at composed
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (IsometricRetainedTransfer.residual (restriction depth bound) value)]

theorem restriction_recovery (depth bound : Nat) (value : Space (law (depth + 1) bound)) :
    restriction depth bound (IsometricRetainedTransfer.transfer (restriction depth bound) value) = value := by
  have retained := IsometricRetainedTransfer.pullback_transfer_add_residual (restriction depth bound) value
  simpa only [restriction_residual_zero, add_zero] using retained

theorem actual_next_recovery (depth : Nat) (task : Fin (depth + 2) → ℂ) :
    transfer (historyPMF (depth + 1)) (read (depth + 1) (depth + 1))
      (taskValue (historyPMF (depth + 1)) task) (Complete.nativeNext depth) = task (Fin.last (depth + 1)) := by
  rw [← actual_new_atom]
  exact complete_recovery (depth + 1) (depth + 1) task (Fin.last (depth + 1))

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
