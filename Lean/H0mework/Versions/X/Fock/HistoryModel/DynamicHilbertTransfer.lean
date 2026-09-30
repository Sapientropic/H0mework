import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertMeasure

/-! The original conditional transfer consumes the generated restriction without dropping either residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open scoped InnerProductSpace

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := measurable depth
local instance (depth : Nat) : BorelSpace (Complete.Carrier depth) := ⟨rfl⟩
local instance (depth : Nat) : T2Space (Complete.Carrier depth) := field_t2 depth

theorem original_transfer (depth bound : Nat) :
    transfer (historyPMF bound) (read depth bound) =
      (IsometricRetainedTransfer.transfer (restriction depth bound)).comp
        (transfer (historyPMF bound) (read (depth + 1) bound)) := by
  have composed := IsometricRetainedTransfer.transfer_comp
    (pullback (historyPMF bound) (read (depth + 1) bound)) (restriction depth bound)
  rw [original_pullback] at composed
  exact composed

theorem original_residual (depth bound : Nat) (value : Space (historyPMF bound)) :
    residual (historyPMF bound) (read depth bound) value =
      residual (historyPMF bound) (read (depth + 1) bound) value +
        pullback (historyPMF bound) (read (depth + 1) bound)
          (IsometricRetainedTransfer.residual (restriction depth bound)
            (transfer (historyPMF bound) (read (depth + 1) bound) value)) := by
  have composed := IsometricRetainedTransfer.residual_comp
    (pullback (historyPMF bound) (read (depth + 1) bound)) (restriction depth bound) value
  rw [original_pullback] at composed
  exact composed

theorem original_residual_energy (depth bound : Nat) (value : Space (historyPMF bound)) :
    ‖residual (historyPMF bound) (read depth bound) value‖ ^ 2 =
      ‖residual (historyPMF bound) (read (depth + 1) bound) value‖ ^ 2 +
        ‖IsometricRetainedTransfer.residual (restriction depth bound)
          (transfer (historyPMF bound) (read (depth + 1) bound) value)‖ ^ 2 := by
  have composed := IsometricRetainedTransfer.residual_comp_energy
    (pullback (historyPMF bound) (read (depth + 1) bound)) (restriction depth bound) value
  rw [original_pullback] at composed
  exact composed

theorem original_reconstruction (depth bound : Nat) (value : Space (historyPMF bound)) :
    pullback (historyPMF bound) (read depth bound)
        (transfer (historyPMF bound) (read depth bound) value) +
      residual (historyPMF bound) (read (depth + 1) bound) value +
        pullback (historyPMF bound) (read (depth + 1) bound)
          (IsometricRetainedTransfer.residual (restriction depth bound)
            (transfer (historyPMF bound) (read (depth + 1) bound) value)) = value := by
  rw [add_assoc, ← original_residual]
  exact IsometricRetainedTransfer.pullback_transfer_add_residual _ value

theorem conditional_weights (depth bound : Nat) (task : Fin (bound + 1) → ℂ)
    (atom : Complete.Carrier depth) (supported : atom ∈ (law depth bound).support) :
    transfer (historyPMF bound) (read depth bound) (taskValue (historyPMF bound) task) atom =
      ∑ index : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) (read depth bound) atom supported index).toReal • task index :=
  optimal_is_conditional (historyPMF bound) (read depth bound) task atom supported

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
