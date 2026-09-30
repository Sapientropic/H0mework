import H0mework.Fock.HistoryModel.RecordedAtomicQuery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRecordFrame

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed MeasureTheory
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
open SourceGeneratedAtomicObservation.Recorded SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance frameUniform (depth : Nat) : UniformSpace (Field nativeStep (rawWords depth)) :=
  fieldUniform nativeStep (rawWords depth)
local instance frameMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)
local instance frameBorel (depth : Nat) : BorelSpace (Field nativeStep (rawWords depth)) := ⟨rfl⟩
local instance frameT2 (depth : Nat) : T2Space (Field nativeStep (rawWords depth)) := Actor.conditionalFieldT2 depth

theorem query_sample (depth bound : Nat) (actor : Fin (bound + 1))
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    query depth bound actor value = value (Actor.originalRead depth bound actor) := by
  have recovered := original_next_recovery depth bound
    (fun index => value (Actor.originalRead depth bound index)) actor
  rw [Actor.currentTransfer_samples] at recovered
  change IsometricRetainedTransfer.transfer
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    value (whole depth bound (SourcePrimeCalculation.recordedQuery bound actor)) = _
  rw [whole_recorded]
  exact recovered

theorem joint_action_square (depth bound : Nat) :
    (Actor.nextPullback depth bound).toContinuousLinearMap.comp
        (IsometricRetainedTransfer.transfer
          (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)) =
      (Actor.currentPullback depth bound).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro value
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro actor
  have nextRead := Actor.nextPullback_at depth bound
    (IsometricRetainedTransfer.transfer
      (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) value) actor
  have queryPoint := congrArg (fun point => IsometricRetainedTransfer.transfer
    (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    value point) (whole_recorded depth bound actor)
  exact nextRead.trans (queryPoint.symm.trans ((query_sample depth bound actor value).trans
    (Actor.currentPullback_at depth bound value actor).symm))

theorem original_time_recovery (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound
      (IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) value) = value := by
  apply (Actor.currentPullback depth bound).injective
  exact DFunLike.congr_fun (joint_action_square depth bound) value

theorem original_temporal_residual_zero (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    IsometricRetainedTransfer.residual
      (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) value = 0 := by
  change value - SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound
    (IsometricRetainedTransfer.transfer
      (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) value) = 0
  rw [original_time_recovery, sub_self]

theorem whole_query_reconstruction (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    Actor.currentTransfer depth bound
      (taskValue (historyPMF bound) (fun actor => query depth bound actor value)) = value := by
  have same := funext fun actor => query_sample depth bound actor value
  rw [same]
  exact Actor.currentTransfer_samples depth bound value

theorem whole_query_energy (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound) :
    ‖value‖ ^ 2 = ∑ actor : Fin (bound + 1), (historyPMF bound actor).toReal * ‖query depth bound actor value‖ ^ 2 := by
  have energy := norm_source_sq (historyPMF bound) (Actor.currentPullback depth bound value)
  rw [(Actor.currentPullback depth bound).norm_map] at energy
  simpa only [Actor.currentPullback_at, query_sample] using energy

end
end SourceGeneratedRecordFrame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
