import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Fresh
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Posterior

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFreshReceiver

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

def freshWord (depth : Nat) : List (Fock.Letter (inventoryBound (runtimeAt depth) + 1)) :=
  SourceWordFutureBitGrowth.oldWordAt depth
    [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))]

theorem fresh_read_all (depth index : Nat) :
    SourceWordObservedCode.readAt depth
        [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))] index =
      SourceWordObservedCode.readAt depth [] index *
        SourceWordObservedCode.observe
          ((runtimeAt depth).tick.next.current.visit.current : Current) := by
  change SourceWordObservedCode.observe
    (Fock.step (depth + 1) (.inr (FamilyModel.Fock.newestIndex depth))
      (nativeStep ((runtimeAt index).current.visit.current : Current))) = _
  rw [SourceWordFutureBit.step_observe, SourceWordFutureBitGrowth.fresh_bit_action]
  rfl

theorem fresh_query_all (depth : Nat) (actor : Actors (runtimeAt depth)) :
    SourceWordObservedCode.sourceQuery (runtimeAt depth) (freshWord depth) actor =
      SourceWordObservedCode.readAt depth [] actor.val *
        SourceWordObservedCode.observe
          ((runtimeAt depth).tick.next.current.visit.current : Current) := by
  rw [SourceWordObservedCode.source_query_read]
  have hTransport := SourceWordFutureBitGrowth.transport_read_at
    (((inventory_bound (runtimeAt depth)).trans (runtimeAt_state depth)).symm)
    [(.inr (FamilyModel.Fock.newestIndex depth) : Fock.Letter (depth + 1))]
    actor.val
  simpa only [freshWord, SourceWordFutureBitGrowth.oldWordAt] using
    hTransport.trans (fresh_read_all depth actor.val)

theorem fresh_post_word_law (depth : Nat) :
    SourceWordObservedCode.postWordLaw (runtimeAt depth) (freshWord depth) =
      (historyPMF (inventoryBound (runtimeAt depth))).map
        (fun actor : Actors (runtimeAt depth) =>
          SourceWordObservedCode.readAt depth [] actor.val *
            SourceWordObservedCode.observe
              ((runtimeAt depth).tick.next.current.visit.current : Current)) := by
  rw [SourceWordObservedCode.post_word_law]
  congr 1
  funext actor
  exact fresh_query_all depth actor


end
end SourceWordFreshReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
