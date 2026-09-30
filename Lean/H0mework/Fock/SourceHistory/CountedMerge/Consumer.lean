import H0mework.Fock.SourceHistory.CountedMerge.Field
import H0mework.Fock.SourceHistory.CountedMerge.Source
set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

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
    let coarseTable := mergeTable table forgetClock
    let nextCoarseTable := SourceCountedObservation.step (inventoryBound advanced) coarseTable (advanced.tick.next.state : ZMod 2)
    SourceConditionalVector.dynamicError advanced.tick.next depth
      (SourceCountedObservation.observationTable advanced.tick.next
        (SourceCountedObservation.step (inventoryBound advanced) table (clockRead 0 advanced.tick.next.state)) depth) =
      SourceConditionalVector.dynamicVariance advanced.tick.next depth +
      ∑ actor : Actors advanced.tick.next, (historyPMF (inventoryBound advanced.tick.next) actor).toReal *
        ‖SourceCountedObservation.readValue advanced.tick.next nextCoarseTable (actor.val : ZMod 2) -
          SourceConditionalVector.realizeModel advanced.tick.next
            (SourceCountedAdvance.nextModel advanced (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
              coarseTable (advanced.tick.next.state : ZMod 2) (actor.val : ZMod 2))‖ ^ 2 := by
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
  let coarse : SourceRetainedReceiver.At (runtime.advance steps) (ZMod 2) := SourceRetainedCoarsening.merge
    (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val current forgetClock
  have coarseSource : SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val (mergeTable table forgetClock) coarse :=
    merge_simulates _ _ table current source forgetClock
  have coarseNative : coarse.native = SourceConditionalNativeObservers.generate
      (fun index : Nat => (index : ZMod 2)) (inventoryBound (runtime.advance steps)) := by
    have generated := SourceRetainedCoarsening.native_source _ _ current (clockRead 0) forgetClock currentNative currentKeys
    have factor : forgetClock ∘ clockRead 0 = (fun index : Nat => (index : ZMod 2)) :=
      funext SourceConditionalNativeMerge.clock_factor
    rw [factor] at generated
    exact generated
  have margins : ∀ key, ‖((coarse.native key).1 : ℂ) •
      SourceRetainedReceiver.residual (runtime.advance steps) coarse key‖ < 1 / 2 := by
    intro key
    with_reducible exact (trajectory_half_margin runtime nonunit (clockRead 0) samples budgets forgetClock key steps)
  have paid := next_field_balance (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) (mergeTable table forgetClock) coarse
    coarseSource coarseNative margins depth
  have same := next_observation (runtime.advance steps) table current source currentNative currentKeys depth
  have observed := congrArg (fun data : SourceGeneratedScalarCofinalTopology.NativeProbability.Field
      SourceObservationInvariantControls.parity →₀ SourceJointClockGraph.Carrier =>
    SourceConditionalVector.dynamicError (runtime.advance steps).tick.next depth data) same
  with_reducible exact observed.symm.trans paid

end
end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
