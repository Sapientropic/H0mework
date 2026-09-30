import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Continuation
import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem continued_field_update (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
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
    let bornKey := forgetClock (clockRead 0 advanced.tick.next.state)
    let count := SourceCountedObservation.total table forgetClock bornKey
    ((inventoryBound advanced + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError advanced.tick.next depth
      (SourceCountedObservation.observationTable advanced.tick.next
        (SourceCountedObservation.step (inventoryBound advanced) table (clockRead 0 advanced.tick.next.state)) depth) =
      ((inventoryBound advanced + 1 : Nat) : ℝ) *
        SourceConditionalVector.dynamicError advanced depth (SourceCountedObservation.observationTable advanced table depth) +
      SourceConditionalNativeBirth.innovation advanced (forgetClock ∘ clockRead 0) -
        (count : ℝ) / (count + 1) *
          ‖∑ key ∈ table.keys.toFinset, (SourceCountedObservation.weight table forgetClock bornKey key : ℂ) •
            (SourceCountedObservation.readValue advanced table key -
              SourceConditionalVector.realizeModel advanced
                (model advanced (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table key))‖ ^ 2 := by
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
      with_reducible exact (initial_half_margin runtime nonunit (clockRead 0) samples budgets key)
    with_reducible exact (trajectory_half_margin runtime initial (clockRead 0) key native initialSmall steps)
  with_reducible exact (field_update (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table current source currentNative currentKeys margins depth)

theorem continued_field_balance (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
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
    SourceConditionalVector.dynamicError advanced depth (SourceCountedObservation.observationTable advanced table depth) =
      SourceConditionalVector.dynamicVariance advanced depth +
      ∑ actor : Actors advanced, (historyPMF (inventoryBound advanced) actor).toReal *
        ‖∑ key ∈ table.keys.toFinset, (SourceCountedObservation.weight table forgetClock (actor.val : ZMod 2) key : ℂ) •
          (SourceCountedObservation.readValue advanced table key -
            SourceConditionalVector.realizeModel advanced
              (model advanced (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table key))‖ ^ 2 := by
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
      with_reducible exact (initial_half_margin runtime nonunit (clockRead 0) samples budgets key)
    with_reducible exact (trajectory_half_margin runtime initial (clockRead 0) key native initialSmall steps)
  with_reducible exact (field_balance (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table current source currentNative currentKeys margins depth)

end
end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
