import H0mework.Versions.X.Fock.SourceHistory.CountedAdvance.Field
import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedAdvance

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem continued_next_field (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (steps depth : Nat) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    let table := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    let advanced := runtime.advance steps
    let nextTable := SourceCountedObservation.step (inventoryBound advanced) table (clockRead 0 advanced.tick.next.state)
    SourceConditionalVector.dynamicError advanced.tick.next depth
      (SourceCountedObservation.observationTable advanced.tick.next nextTable depth) =
      SourceConditionalVector.dynamicVariance advanced.tick.next depth +
      ∑ actor : Actors advanced.tick.next, (historyPMF (inventoryBound advanced.tick.next) actor).toReal *
        ‖∑ key ∈ nextTable.keys.toFinset,
          (SourceCountedObservation.weight nextTable forgetClock (actor.val : ZMod 2) key : ℂ) •
            (SourceCountedObservation.readValue advanced.tick.next nextTable key -
              SourceConditionalVector.realizeModel advanced.tick.next
                (nextModel advanced (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table (clockRead 0 advanced.tick.next.state) key))‖ ^ 2 := by
  dsimp only
  let initial : SourceRetainedReceiver.At runtime (ℤ × ℤ) := SourceRetainedReceiver.start
    (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
  let current := SourceRetainedReceiver.trajectory runtime initial
    (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
  let table := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  have native : initial.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime) :=
    SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets
  have source : SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val table current := by
    with_reducible exact (SourceCountedObservation.received_simulates runtime nonunit (clockRead 0)
      keys inventory samples budgets steps)
  have currentNative := SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) native steps
  have initialKeys : initial.keys =
      SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val) := rfl
  have currentKeys := SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) initialKeys steps
  have margins : ∀ key, ‖((current.native key).1 : ℂ) •
      SourceRetainedReceiver.residual (runtime.advance steps) current key‖ < 1 / 2 := by
    intro key
    have initialSmall : ‖((initial.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime initial key‖ < 1 / 2 := by
      with_reducible exact (SourceCountedPosterior.initial_half_margin runtime nonunit (clockRead 0) samples budgets key)
    with_reducible exact (SourceCountedPosterior.trajectory_half_margin runtime initial (clockRead 0) key native initialSmall steps)
  with_reducible exact (next_field_balance (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table current source currentNative currentKeys margins depth)


end
end SourceCountedAdvance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
