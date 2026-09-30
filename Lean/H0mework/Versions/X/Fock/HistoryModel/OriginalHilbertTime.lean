import H0mework.Versions.X.Fock.HistoryModel.OriginalHilbertMeasure

/-! Actual word action feeds the already existing native time pullback and its original adjoint. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory

noncomputable section

local instance timeWordsMeasurable (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := Dynamic.Hilbert.measurable depth
local instance timeFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) := fieldBorel nativeStep (rawWords depth)

abbrev sourceTimePullback (depth : Nat) (current : Current) (bound : Nat) :=
  (fieldPullback depth current bound).comp (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)

theorem sourceTimePullback_ae (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) (nativeStep current) bound) :
    sourceTimePullback depth current bound value =ᵐ[(wordLaw depth current bound).toMeasure]
      fun point => value (originalField depth (Complete.action depth (.inl ()) point)) := by
  have original := (original_preserving depth current bound).quasiMeasurePreserving.ae_eq
    (SourceOwnedObservationHistory.pullback_ae nativeStep (rawWords depth) current bound value)
  have words := fieldPullback_ae depth current bound
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound value)
  have generated := words.trans original
  filter_upwards [generated] with point same
  exact same.trans (congrArg value (original_action depth point).symm)

theorem sourceTime_transfer (depth : Nat) (current : Current) (bound : Nat) :
    IsometricRetainedTransfer.transfer (sourceTimePullback depth current bound) =
      (IsometricRetainedTransfer.transfer (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)).comp
        (IsometricRetainedTransfer.transfer (fieldPullback depth current bound)) :=
  IsometricRetainedTransfer.transfer_comp (fieldPullback depth current bound)
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)

theorem sourceTime_full_residual (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceWeightedRecovery.Space (wordLaw depth current bound)) :
    IsometricRetainedTransfer.residual (sourceTimePullback depth current bound) value =
      IsometricRetainedTransfer.residual (fieldPullback depth current bound) value +
        fieldPullback depth current bound
          (IsometricRetainedTransfer.residual (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound)
            (IsometricRetainedTransfer.transfer (fieldPullback depth current bound) value)) :=
  IsometricRetainedTransfer.residual_comp (fieldPullback depth current bound)
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) current bound) value

theorem sourceTime_original_energy (depth : Nat) (current : Current) (bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) current bound) :
    ‖fieldPullback depth current bound value‖ ^ 2 =
      ‖(retainedUpdate nativeStep (rawWords depth) current bound value).1‖ ^ 2 +
        ‖(retainedUpdate nativeStep (rawWords depth) current bound value).2‖ ^ 2 := by
  rw [(fieldPullback depth current bound).norm_map]
  exact retainedUpdate_energy nativeStep (rawWords depth) current bound value

end
end SourceGeneratedActionWords.Fock.OriginalHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
