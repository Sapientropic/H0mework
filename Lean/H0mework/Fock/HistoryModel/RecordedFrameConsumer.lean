import H0mework.Fock.HistoryModel.RecordedFrameSource
import H0mework.Fock.HistoryModel.RecordedAtomicConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRecordFrame

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourcePrimeHistoryRecovery SourcePrimeCalculation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance consumerMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem original_transfer_norm (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    ‖IsometricRetainedTransfer.transfer
      (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) value‖ = ‖value‖ := by
  have conserved := (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
    CanonicalUnitArithmeticRoot.initialCurrent bound).norm_map
      (IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) value)
  rw [original_time_recovery] at conserved
  exact conserved.symm

theorem original_decoder_error (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    (decoder : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
      (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) bound) :
    ‖value - SourceOwnedObservationHistory.pullback nativeStep (rawWords depth)
        CanonicalUnitArithmeticRoot.initialCurrent bound decoder‖ ^ 2 =
      ‖IsometricRetainedTransfer.transfer
          (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
          value - decoder‖ ^ 2 := by
  have error := IsometricRetainedTransfer.decoder_error_decomposition
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    value decoder
  rw [original_temporal_residual_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at error
  exact error

theorem recorded_family_consumed (actorBound : Nat) :
    let position := completionDepth sourceOwner actorBound + 1
    let depth := position + 1
    type_of% (joint_action_square depth actorBound) ∧
      (∀ value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent actorBound,
        type_of% (original_time_recovery depth actorBound value) ∧
        type_of% (original_temporal_residual_zero depth actorBound value) ∧
        type_of% (whole_query_reconstruction depth actorBound value) ∧
        type_of% (whole_query_energy depth actorBound value) ∧
        type_of% (original_transfer_norm depth actorBound value) ∧
        (∀ decoder : SourceOwnedObservationHistory.Space nativeStep (rawWords depth)
          (nativeStep CanonicalUnitArithmeticRoot.initialCurrent) actorBound,
          type_of% (original_decoder_error depth actorBound value decoder))) ∧
      type_of% (SourceGeneratedAtomicObservation.Installed.recorded_queries_consumed actorBound) := by
  dsimp only
  refine ⟨joint_action_square _ actorBound, ?_, SourceGeneratedAtomicObservation.Installed.recorded_queries_consumed actorBound⟩
  intro value
  exact ⟨original_time_recovery _ actorBound value, original_temporal_residual_zero _ actorBound value,
    whole_query_reconstruction _ actorBound value, whole_query_energy _ actorBound value,
    original_transfer_norm _ actorBound value, original_decoder_error _ actorBound value⟩

end
end SourceGeneratedRecordFrame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
