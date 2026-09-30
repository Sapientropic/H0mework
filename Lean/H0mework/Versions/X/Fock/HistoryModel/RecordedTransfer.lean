import H0mework.Versions.X.Fock.HistoryModel.RecordedConditional

/-! The generated finite-record whole value is read by both original time consumers through one source-born answer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability SourcePrimeHistoryRecovery SourcePrimeCalculation SourceWeightedRecovery
open SourceConditionalTransfer
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance recordedTransferFieldMeasurable (depth : Nat) : MeasurableSpace (Field nativeStep (rawWords depth)) :=
  fieldBorel nativeStep (rawWords depth)

theorem original_transfer_on_record (depth bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
        (Actor.currentTransfer depth bound (taskValue (historyPMF bound) task))
        (whole depth bound (recordedQuery bound actor)) = decoder sourceOwner bound task (recordedQuery bound actor) := by
  rw [whole_recorded]
  exact (original_transfer_from_birth depth bound task actor).trans (source_answer_is_recorded bound task actor)

theorem original_field_transfer_on_record (depth bound : Nat)
    (value : SourceOwnedObservationHistory.Space nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
    (actor : Fin (bound + 1)) :
    IsometricRetainedTransfer.transfer
        (SourceOwnedObservationHistory.pullback nativeStep (rawWords depth) CanonicalUnitArithmeticRoot.initialCurrent bound)
        value (whole depth bound (recordedQuery bound actor)) =
      decoder sourceOwner bound (fun index => value (Actor.originalRead depth bound index)) (recordedQuery bound actor) := by
  rw [whole_recorded]
  exact (original_field_transfer_from_birth depth bound value actor).trans (source_answer_is_recorded bound _ actor)

theorem prime_transfer_on_record (bound : Nat) (task : Fin (bound + 1) → ℂ) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
      (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task))
      (nextAtom (process := process) rawField runtimeSeed bound actor) = decoder sourceOwner bound task (recordedQuery bound actor) :=
  (transfer_from_birth bound task actor).trans (source_answer_is_recorded bound task actor)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
