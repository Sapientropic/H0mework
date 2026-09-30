import H0mework.Fock.HistoryModel.OriginalHilbertTime
import H0mework.Fock.HistoryModel.OriginalHilbertInverse

/-! The paid observer identity leaves exactly the original temporal residual, with its full norm and reconstruction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory

noncomputable section

local instance residualWordsMeasurable (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := Dynamic.Hilbert.measurable depth
local instance residualFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)

theorem sourceTime_original_residual (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceWeightedRecovery.Space (wordLaw depth current bound)) :
    IsometricRetainedTransfer.residual (sourceTimePullback depth current bound) value =
      fieldPullback depth current bound
        (IsometricRetainedTransfer.residual (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)
          (IsometricRetainedTransfer.transfer (fieldPullback depth current bound) value)) := by
  rw [sourceTime_full_residual, fieldPullback_residual_zero, zero_add]

theorem sourceTime_original_residual_norm (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceWeightedRecovery.Space (wordLaw depth current bound)) :
    ‖IsometricRetainedTransfer.residual (sourceTimePullback depth current bound) value‖ =
      ‖IsometricRetainedTransfer.residual (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)
        (IsometricRetainedTransfer.transfer (fieldPullback depth current bound) value)‖ := by
  rw [sourceTime_original_residual, (fieldPullback depth current bound).norm_map]

theorem sourceTime_transfer_original (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) current bound) :
    IsometricRetainedTransfer.transfer (sourceTimePullback depth current bound) (fieldPullback depth current bound value) =
      IsometricRetainedTransfer.transfer (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound) value := by
  rw [sourceTime_transfer]
  change IsometricRetainedTransfer.transfer _
    (IsometricRetainedTransfer.transfer (fieldPullback depth current bound) (fieldPullback depth current bound value)) = _
  rw [IsometricRetainedTransfer.transfer_pullback]

theorem sourceTime_original_reconstruction (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceWeightedRecovery.Space (wordLaw depth current bound)) :
    fieldPullback depth current bound
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound
          (IsometricRetainedTransfer.transfer (sourceTimePullback depth current bound) value)) +
      fieldPullback depth current bound
        (IsometricRetainedTransfer.residual (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)
          (IsometricRetainedTransfer.transfer (fieldPullback depth current bound) value)) = value := by
  have original := IsometricRetainedTransfer.pullback_transfer_add_residual (sourceTimePullback depth current bound) value
  rw [sourceTime_original_residual] at original
  exact original

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
