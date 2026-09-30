import H0mework.Fock.HistoryModel.OriginalHilbertDictionary
import H0mework.Realization.HilbertTransfer.Composition

/-! The actual native-action square generates the correctly oriented adjoint equation and both residual sums. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory

noncomputable section

local instance squareFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem time_dictionary_square (depth : Nat) (current : Current) (bound : Nat) :
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1)) current bound).comp
        (dictionaryPullback depth (nativeStep current) bound) =
      (dictionaryPullback depth current bound).comp
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound) := by
  apply LinearIsometry.ext
  intro value
  have fine := Lp.compMeasurePreserving_comp_apply value (dictionary_preserving depth (nativeStep current) bound)
    (source_measurePreserving nativeStep (rawWords (depth + 1)) current bound)
  have coarse := Lp.compMeasurePreserving_comp_apply value
    (source_measurePreserving nativeStep (rawWords depth) current bound) (dictionary_preserving depth current bound)
  have square : dictionary depth ∘ fieldAction nativeStep (rawWords (depth + 1)) =
      fieldAction nativeStep (rawWords depth) ∘ dictionary depth := funext (dictionary_action depth)
  simp only [square] at fine
  exact fine.symm.trans coarse

theorem time_dictionary_adjoint (depth : Nat) (current : Current) (bound : Nat) :
    (IsometricRetainedTransfer.transfer (dictionaryPullback depth (nativeStep current) bound)).comp
        (IsometricRetainedTransfer.transfer (SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1)) current bound)) =
      (IsometricRetainedTransfer.transfer (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)).comp
        (IsometricRetainedTransfer.transfer (dictionaryPullback depth current bound)) := by
  have generated := congrArg IsometricRetainedTransfer.transfer (time_dictionary_square depth current bound)
  simpa only [IsometricRetainedTransfer.transfer_comp] using generated

theorem time_dictionary_residual (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords (depth + 1)) current bound) :
    IsometricRetainedTransfer.residual (SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1)) current bound) value +
      SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1)) current bound
        (IsometricRetainedTransfer.residual (dictionaryPullback depth (nativeStep current) bound)
          (IsometricRetainedTransfer.transfer (SourceOwnedObservationHistory.pullback nativeStep (rawWords (depth + 1)) current bound) value)) =
      IsometricRetainedTransfer.residual (dictionaryPullback depth current bound) value +
        dictionaryPullback depth current bound
          (IsometricRetainedTransfer.residual (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)
            (IsometricRetainedTransfer.transfer (dictionaryPullback depth current bound) value)) := by
  have generated := congrArg (fun arrow => IsometricRetainedTransfer.residual arrow value)
    (time_dictionary_square depth current bound)
  simpa only [IsometricRetainedTransfer.residual_comp] using generated

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
