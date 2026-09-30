import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.Controls

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFixedErasure

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors nextRead)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

theorem read_all_zero (index : Nat) :
    SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
      (SourceWordFreshReceiver.freshWord 2) index = 0 := by
  have hTransport := SourceWordFutureBitGrowth.transport_read_at
    (((inventory_bound (runtimeAt 2)).trans (runtimeAt_state 2)).symm)
    [(.inr (FamilyModel.Fock.newestIndex 2) : Fock.Letter (2 + 1))] index
  have hFresh := SourceWordFreshReceiver.fresh_read_all 2 index
  have evenBit : (4 : ZMod 2) = 0 := by decide
  rw [SourceWordFreshReceiver.fresh_material_bit,
    show (2 + 2 : Nat) = 4 by decide, Nat.cast_ofNat, evenBit, mul_zero] at hFresh
  simpa only [SourceWordFreshReceiver.freshWord, SourceWordFutureBitGrowth.oldWordAt]
    using hTransport.trans hFresh

theorem key_zero_supported (steps : Nat) :
    (0 : ZMod 2) ∈ ((historyPMF (inventoryBound ((runtimeAt 2).advance steps))).map
      (fun actor : Actors ((runtimeAt 2).advance steps) =>
        SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
          (SourceWordFreshReceiver.freshWord 2) actor.val)).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨⟨0, Nat.zero_lt_succ _⟩, SourceUniformFibreVariance.source_positive _ _, ?_⟩
  exact read_all_zero 0

theorem complete_history_at (steps : Nat) :
    SourcePosteriorReadback.readWeight ((runtimeAt 2).advance steps)
      (SourceCountedPosterior.model ((runtimeAt 2).advance steps)
        (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1) steps)
        (SourceWordObservedCode.table (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1)
          (SourceWordFreshReceiver.freshWord 2) steps) 0) =
      (fun actor => historyPMF (inventoryBound ((runtimeAt 2).advance steps)) actor) := by
  rw [SourceWordObservedCode.counted_complete_posterior_at
    (runtimeAt 2) (SourceWordFutureBitGrowth.nextNonunit 1)
    (SourceWordFreshReceiver.freshWord 2) steps 0 (key_zero_supported steps)]
  funext actor
  have queryConst : (fun index : Actors ((runtimeAt 2).advance steps) =>
      SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
        (SourceWordFreshReceiver.freshWord 2) index.val) =
      fun _ => (0 : ZMod 2) := by
    funext index
    exact read_all_zero index.val
  simp only [queryConst]
  exact congrArg (fun p : PMF (Actors ((runtimeAt 2).advance steps)) => p actor)
    (SourceWeightedRecovery.ObservationRefinement.conditional_constant
      (historyPMF (inventoryBound ((runtimeAt 2).advance steps)))
      (fun _ : Actors ((runtimeAt 2).advance steps) => (0 : ZMod 2)) 0
      (fun _ => rfl) (by simpa only [queryConst] using key_zero_supported steps))

theorem next_model_fixed (steps : Nat) :
    SourceCountedAdvance.nextModel ((runtimeAt 2).advance steps)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 2)
        (SourceWordFutureBitGrowth.nextNonunit 1) steps)
      (SourceWordObservedCode.table (runtimeAt 2)
        (SourceWordFutureBitGrowth.nextNonunit 1)
        (SourceWordFreshReceiver.freshWord 2) steps)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
        (SourceWordFreshReceiver.freshWord 2)
        ((runtimeAt 2).advance steps).tick.next.state) 0 =
      SourceConditionalNativePosterior.model ((runtimeAt 2).advance steps).tick.next
        (fun _ => (0 : ZMod 2)) 0 := by
  rw [SourceWordObservedCode.counted_next_model]
  congr 1
  funext index
  exact read_all_zero index

theorem constant_key_supported (runtime : LivingRuntimeState process) :
    (0 : ZMod 2) ∈ ((historyPMF (inventoryBound runtime)).map
      (fun _ : Actors runtime => (0 : ZMod 2))).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨⟨0, Nat.zero_lt_succ _⟩,
    SourceUniformFibreVariance.source_positive _ _, rfl⟩

theorem constant_model_is_full_history (runtime : LivingRuntimeState process) :
    SourceConditionalNativePosterior.model runtime
        (fun _ => (0 : ZMod 2)) 0 =
      ∑ actor : Actors runtime,
        (((historyPMF (inventoryBound runtime) actor).toReal : ℂ) •
          nextRead runtime actor) := by
  rw [SourceConditionalNativePosterior.model_original runtime
    (fun _ => (0 : ZMod 2)) 0 (constant_key_supported runtime)]
  unfold SourceConditionalVector.estimate
  apply Finset.sum_congr rfl
  intro actor _
  have same := SourceWeightedRecovery.ObservationRefinement.conditional_constant
    (historyPMF (inventoryBound runtime))
    (fun _ : Actors runtime => (0 : ZMod 2)) 0 (fun _ => rfl)
    (constant_key_supported runtime)
  rw [same]

theorem next_model_is_full_history (steps : Nat) :
    SourceCountedAdvance.nextModel ((runtimeAt 2).advance steps)
      (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 2)
        (SourceWordFutureBitGrowth.nextNonunit 1) steps)
      (SourceWordObservedCode.table (runtimeAt 2)
        (SourceWordFutureBitGrowth.nextNonunit 1)
        (SourceWordFreshReceiver.freshWord 2) steps)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
        (SourceWordFreshReceiver.freshWord 2)
        ((runtimeAt 2).advance steps).tick.next.state) 0 =
      ∑ actor : Actors ((runtimeAt 2).advance steps).tick.next,
        (((historyPMF (inventoryBound ((runtimeAt 2).advance steps).tick.next)
          actor).toReal : ℂ) •
          nextRead ((runtimeAt 2).advance steps).tick.next actor) := by
  rw [next_model_fixed, constant_model_is_full_history]

theorem next_readback_is_full_history (steps : Nat) :
    SourcePosteriorReadback.readWeight ((runtimeAt 2).advance steps).tick.next
      (SourceCountedAdvance.nextModel ((runtimeAt 2).advance steps)
        (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1) steps)
        (SourceWordObservedCode.table (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1)
          (SourceWordFreshReceiver.freshWord 2) steps)
        (SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
          (SourceWordFreshReceiver.freshWord 2)
          ((runtimeAt 2).advance steps).tick.next.state) 0) =
      (fun actor =>
        historyPMF (inventoryBound ((runtimeAt 2).advance steps).tick.next) actor) := by
  rw [next_model_fixed]
  rw [SourceConditionalNativePosterior.complete_posterior
    ((runtimeAt 2).advance steps).tick.next (fun _ => (0 : ZMod 2)) 0
    (constant_key_supported _)]
  funext actor
  exact congrArg (fun p : PMF (Actors ((runtimeAt 2).advance steps).tick.next) => p actor)
    (SourceWeightedRecovery.ObservationRefinement.conditional_constant
      (historyPMF (inventoryBound ((runtimeAt 2).advance steps).tick.next))
      (fun _ : Actors ((runtimeAt 2).advance steps).tick.next => (0 : ZMod 2)) 0
      (fun _ => rfl) (constant_key_supported _))

theorem generated_stage (steps : Nat) :
    let advanced := (runtimeAt 2).advance steps
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate advanced
    process.toAnswerNextCausalWorld.emitted (ULift.up advanced.state) =
        ULift.up stage.activated.generated ∧
      stage.activated.generated.occurrence =
        advanced.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          advanced.current.visit.current ∧
      HEq stage.wholeLedgerWriteBack
        (advanced.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          advanced.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent := by
  exact (SourceGeneratedRuntimeMaterialStageAt.generate ((runtimeAt 2).advance steps)).factorizes

theorem received_on_generated_stage (steps : Nat) :
    let advanced := (runtimeAt 2).advance steps
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate advanced
    SourceCountedObservation.Simulates
      (inventoryBound advanced)
      (SourceCopyCurrentCoordinates.maximumIndex advanced).val
      (SourceWordObservedCode.table (runtimeAt 2)
        (SourceWordFutureBitGrowth.nextNonunit 1)
        (SourceWordFreshReceiver.freshWord 2) steps)
      (SourceRetainedReceiver.trajectory (runtimeAt 2)
        (SourceWordObservedCode.initial (runtimeAt 2)
          (SourceWordFutureBitGrowth.nextNonunit 1)
          (SourceWordFreshReceiver.freshWord 2))
        (fun offset => SourceWordObservedCode.readAt (inventoryBound (runtimeAt 2))
          (SourceWordFreshReceiver.freshWord 2)
          (inventoryBound (runtimeAt 2) + offset + 1)) steps) ∧
      SourcePosteriorReadback.readWeight advanced
        (SourceCountedPosterior.model advanced
          (SourceRetainedReceiver.trajectory_nonunit (runtimeAt 2)
            (SourceWordFutureBitGrowth.nextNonunit 1) steps)
          (SourceWordObservedCode.table (runtimeAt 2)
            (SourceWordFutureBitGrowth.nextNonunit 1)
            (SourceWordFreshReceiver.freshWord 2) steps) 0) =
        (fun actor => historyPMF (inventoryBound advanced) actor) ∧
      HEq stage.wholeLedgerWriteBack
        (advanced.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          advanced.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent := by
  exact ⟨SourceWordFreshReceiver.fresh_received 2
      (SourceWordFutureBitGrowth.nextNonunit 1) steps,
    complete_history_at steps,
    (generated_stage steps).2.2.1,
    (generated_stage steps).2.2.2⟩


end
end SourceWordFixedErasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
