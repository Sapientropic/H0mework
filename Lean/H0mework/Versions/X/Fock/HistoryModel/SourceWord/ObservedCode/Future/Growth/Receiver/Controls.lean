import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.Account

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

theorem fresh_material_bit (depth : Nat) :
    SourceWordObservedCode.observe
      ((runtimeAt depth).tick.next.current.visit.current : Current) =
        ((depth + 2 : Nat) : ZMod 2) := by
  change (scanIndex ((runtimeAt (depth + 1)).current.visit.current : Current) : ZMod 2) = _
  rw [runtimeAt_scanIndex]

theorem erased_at_two (actor : Actors (runtimeAt 2)) :
    SourceWordObservedCode.sourceQuery (runtimeAt 2) (freshWord 2) actor = 0 := by
  rw [fresh_query_all, fresh_material_bit]
  have evenBit : (4 : ZMod 2) = 0 := by decide
  rw [show (2 + 2 : Nat) = 4 by decide, Nat.cast_ofNat, evenBit, mul_zero]

theorem retained_at_three (actor : Actors (runtimeAt 3)) :
    SourceWordObservedCode.sourceQuery (runtimeAt 3) (freshWord 3) actor =
      SourceWordObservedCode.readAt 3 [] actor.val := by
  rw [fresh_query_all, fresh_material_bit]
  have oddBit : (5 : ZMod 2) = 1 := by decide
  rw [show (3 + 2 : Nat) = 5 by decide, Nat.cast_ofNat, oddBit, mul_one]

theorem retained_read_all_at_three (index : Nat) :
    SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3)) (freshWord 3) index =
      SourceWordObservedCode.readAt 3 [] index := by
  have hTransport := SourceWordFutureBitGrowth.transport_read_at
    (((inventory_bound (runtimeAt 3)).trans (runtimeAt_state 3)).symm)
    [(.inr (FamilyModel.Fock.newestIndex 3) : Fock.Letter (3 + 1))] index
  have hFresh := fresh_read_all 3 index
  have oddBit : (5 : ZMod 2) = 1 := by decide
  rw [fresh_material_bit, show (3 + 2 : Nat) = 5 by decide,
    Nat.cast_ofNat, oddBit, mul_one] at hFresh
  simpa only [freshWord, SourceWordFutureBitGrowth.oldWordAt] using hTransport.trans hFresh

theorem retained_complete_model_at_three (key : ZMod 2) :
    SourceCountedPosterior.model (runtimeAt 3)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 3)
        SourceWordObservedCode.actual_nonunit 0)
      (SourceWordObservedCode.table (runtimeAt 3)
        SourceWordObservedCode.actual_nonunit (freshWord 3) 0) key =
    SourceCountedPosterior.model (runtimeAt 3)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 3)
        SourceWordObservedCode.actual_nonunit 0)
      (SourceWordObservedCode.table (runtimeAt 3)
        SourceWordObservedCode.actual_nonunit [] 0) key := by
  have fresh := SourceWordObservedCode.counted_model
    (runtimeAt 3) SourceWordObservedCode.actual_nonunit (freshWord 3) 0 key
  have native := SourceWordObservedCode.counted_model
    (runtimeAt 3) SourceWordObservedCode.actual_nonunit [] 0 key
  simp only [LivingRuntimeState.advance] at fresh native
  rw [fresh, native]
  have readEq : SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
      (freshWord 3) = SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3)) [] := by
    funext index
    rw [retained_read_all_at_three]
    rw [inventory_bound, runtimeAt_state]
  rw [readEq]

theorem erased_posterior_at_two :
    SourcePosteriorReadback.readWeight (runtimeAt 2)
      (SourceCountedPosterior.model (runtimeAt 2)
        (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1) 0)
        (SourceWordObservedCode.table (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1) (freshWord 2) 0) 0) =
      (fun actor => historyPMF (inventoryBound (runtimeAt 2)) actor) := by
  have supported : (0 : ZMod 2) ∈
      ((historyPMF (inventoryBound (runtimeAt 2))).map
        (SourceWordObservedCode.sourceQuery (runtimeAt 2) (freshWord 2))).support := by
    have positive := SourceUniformFibreVariance.source_positive
      (inventoryBound (runtimeAt 2)) (⟨0, by
        rw [inventory_bound, runtimeAt_state]
        decide⟩ : Actors (runtimeAt 2))
    have observed := SourceWeightedRecovery.observed_supported
      (historyPMF (inventoryBound (runtimeAt 2)))
      (SourceWordObservedCode.sourceQuery (runtimeAt 2) (freshWord 2))
      (⟨0, by
        rw [inventory_bound, runtimeAt_state]
        decide⟩ : Actors (runtimeAt 2)) positive
    simpa only [erased_at_two] using observed
  have queryConst : SourceWordObservedCode.sourceQuery (runtimeAt 2) (freshWord 2) =
      fun _ => (0 : ZMod 2) := by
    funext actor
    exact erased_at_two actor
  rw [SourceWordObservedCode.counted_complete_posterior
    (runtimeAt 2) (SourceWordFutureBitGrowth.nextNonunit 1)
    (freshWord 2) 0 supported]
  funext actor
  simp only [queryConst]
  exact congrArg (fun p : PMF (Actors (runtimeAt 2)) => p actor)
    (SourceWeightedRecovery.ObservationRefinement.conditional_constant
    (historyPMF (inventoryBound (runtimeAt 2)))
    (fun _ : Actors (runtimeAt 2) => (0 : ZMod 2)) 0 (fun _ => rfl)
    (by simpa only [queryConst] using supported))

end
end SourceWordFreshReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
