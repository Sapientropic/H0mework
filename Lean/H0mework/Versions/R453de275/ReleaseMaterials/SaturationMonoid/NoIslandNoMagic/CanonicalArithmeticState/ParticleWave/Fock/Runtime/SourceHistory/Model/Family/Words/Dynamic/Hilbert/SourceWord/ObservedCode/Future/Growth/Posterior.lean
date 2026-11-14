import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Model
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Fresh

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFutureBitGrowth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- The already counted receiver reads every retained letter through the
enlarged inventory on the full advanced history, including its new actor.
This does not assert that the actor's posterior weight equals an old weight. -/
theorem counted_old_letter_posterior (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound (runtime.advance steps))).map
      (fun actor : Actors (runtime.advance steps) =>
        SourceWordObservedCode.readAt (inventoryBound runtime + 1)
          (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter
            (inventoryBound runtime + 1))) actor.val)).support) :
    SourcePosteriorReadback.readWeight (runtime.advance steps)
      (SourceCountedPosterior.model (runtime.advance steps)
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
        (SourceWordObservedCode.table runtime nonunit word steps) key) =
      (fun actor => SourceConditionalHistory.conditional
        (historyPMF (inventoryBound (runtime.advance steps)))
        (fun index : Actors (runtime.advance steps) =>
          SourceWordObservedCode.readAt (inventoryBound runtime + 1)
            (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter
              (inventoryBound runtime + 1))) index.val)
        key supported actor) := by
  have queryEq : (fun actor : Actors (runtime.advance steps) =>
      SourceWordObservedCode.readAt (inventoryBound runtime + 1)
        (word.map (SourceGeneratedActionWords.Fock.Dynamic.oldLetter
          (inventoryBound runtime + 1))) actor.val) =
      (fun actor : Actors (runtime.advance steps) =>
        SourceWordObservedCode.readAt (inventoryBound runtime) word actor.val) := by
    funext actor
    exact old_read_at (inventoryBound runtime) word actor.val
  have supportedOld : key ∈ ((historyPMF (inventoryBound (runtime.advance steps))).map
      (fun actor : Actors (runtime.advance steps) =>
        SourceWordObservedCode.readAt (inventoryBound runtime) word actor.val)).support := by
    simpa only [queryEq] using supported
  simpa only [queryEq] using
    (SourceWordObservedCode.counted_complete_posterior_at runtime nonunit word steps key
      supportedOld)


end
end SourceWordFutureBitGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
