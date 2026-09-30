import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Consumer
import H0mework.Versions.X.Fock.HistoryConditional.InformationLossRecovery
import H0mework.Versions.X.Fock.HistoryConditional.MergeLossClock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private theorem native_next_loss (current : LivingRuntimeState process) :
    (∑ actor : Actors current, (historyPMF (inventoryBound current) actor).toReal *
      ‖SourceConditionalVector.realizeModel current (nextRead current actor) -
        SourceConditionalNativePosterior.decoder current (forgetClock ∘ clockRead 0)
          (forgetClock (clockRead 0 actor.val))‖ ^ 2) =
      SourceConditionalMergeLoss.gap current (clockRead 0) forgetClock := by
  have paid := SourceConditionalMergeLoss.loss current (clockRead 0) forgetClock
  have fineZero :
      (∑ actor : Actors current, (historyPMF (inventoryBound current) actor).toReal *
        ‖SourceConditionalVector.realizeModel current (nextRead current actor) -
          SourceConditionalNativePosterior.decoder current (clockRead 0) (clockRead 0 actor.val)‖ ^ 2) = 0 := by
    simpa only [SourceConditionalMergeLoss.clock_fine] using SourceConditionalNativeObservers.error_zero current
  rw [fineZero, zero_add] at paid
  rw [SourceConditionalMergeLoss.decoder_original] at paid
  rw [SourceConditionalMergeLoss.gap, SourceConditionalMergeLoss.decoder_original]
  exact paid

theorem continued_next_table_loss (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
        SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    let advanced := runtime.advance steps
    let coarseTable := SourceCountedMerge.mergeTable fineTable forgetClock
    let nextCoarseTable := SourceCountedObservation.step (inventoryBound advanced) coarseTable
      (forgetClock (clockRead 0 advanced.tick.next.state))
    (∑ actor : Actors advanced.tick.next, (historyPMF (inventoryBound advanced.tick.next) actor).toReal *
      ‖SourceConditionalVector.realizeModel advanced.tick.next (nextRead advanced.tick.next actor) -
        SourceConditionalVector.realizeModel advanced.tick.next
          (SourceCountedPosterior.model advanced.tick.next (SourceMinimumSharedNext.next_nonunit advanced)
            nextCoarseTable
            (forgetClock (clockRead 0 actor.val)))‖ ^ 2) =
      SourceConditionalMergeLoss.gap advanced.tick.next (clockRead 0) forgetClock := by
  dsimp only
  let advanced := runtime.advance steps
  let initial : SourceRetainedReceiver.At runtime (ℤ × ℤ) := SourceRetainedReceiver.start
    (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
  let current := SourceRetainedReceiver.trajectory runtime initial
    (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
  let fineTable := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  let coarseTable := SourceCountedMerge.mergeTable fineTable forgetClock
  let coarse : SourceRetainedReceiver.At advanced (ZMod 2) := SourceRetainedCoarsening.merge
    (inventoryBound advanced) (maximumIndex advanced).val current forgetClock
  have fineSource : SourceCountedObservation.Simulates (inventoryBound advanced) (maximumIndex advanced).val
      fineTable current := by
    with_reducible exact (SourceCountedObservation.received_simulates runtime nonunit (clockRead 0)
      keys inventory samples budgets steps)
  have fineNative : current.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound advanced) := by
    with_reducible exact (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0)
      (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps)
  have fineKeys : current.keys = SourceUniformFibreVariance.outputs (inventoryBound advanced)
      (fun actor => clockRead 0 actor.val) := by
    with_reducible exact SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps
  have coarseSource : SourceCountedObservation.Simulates (inventoryBound advanced) (maximumIndex advanced).val
      coarseTable coarse := SourceCountedMerge.merge_simulates _ _ fineTable current fineSource forgetClock
  have coarseNative : coarse.native = SourceConditionalNativeObservers.generate (forgetClock ∘ clockRead 0)
      (inventoryBound advanced) :=
    SourceRetainedCoarsening.native_source _ _ current (clockRead 0) forgetClock fineNative fineKeys
  have coarseMargins : ∀ key, ‖((coarse.native key).1 : ℂ) •
      SourceRetainedReceiver.residual advanced coarse key‖ < 1 / 2 := by
    intro key
    with_reducible exact (SourceCountedMerge.trajectory_half_margin runtime nonunit
      (clockRead 0) samples budgets forgetClock key steps)
  rw [← native_next_loss (runtime.advance steps).tick.next]
  apply Finset.sum_congr rfl
  intro actor _
  have stepModel := SourceCountedAdvance.step_model_commutes advanced
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) coarseTable coarse
    (forgetClock ∘ clockRead 0) (forgetClock (clockRead 0 actor.val))
    coarseSource coarseNative coarseMargins
  have model := SourceCountedMerge.continued_next_model runtime nonunit (clockRead 0)
    keys inventory samples budgets forgetClock steps (forgetClock (clockRead 0 actor.val))
  simp only [Function.comp_apply] at stepModel model
  have sourceModel := stepModel.trans model
  exact congrArg (fun value : SourceConditionalModel.NextModel (runtime.advance steps).tick.next =>
    (historyPMF (inventoryBound (runtime.advance steps).tick.next) actor).toReal *
      ‖SourceConditionalVector.realizeModel (runtime.advance steps).tick.next
        (nextRead (runtime.advance steps).tick.next actor) -
        SourceConditionalVector.realizeModel (runtime.advance steps).tick.next value‖ ^ 2) sourceModel

theorem continued_next_table_strict (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0) (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
        SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    let advanced := runtime.advance steps
    let coarseTable := SourceCountedMerge.mergeTable fineTable forgetClock
    let nextCoarseTable := SourceCountedObservation.step (inventoryBound advanced) coarseTable
      (forgetClock (clockRead 0 advanced.tick.next.state))
    0 < (∑ actor : Actors advanced.tick.next, (historyPMF (inventoryBound advanced.tick.next) actor).toReal *
      ‖SourceConditionalVector.realizeModel advanced.tick.next (nextRead advanced.tick.next actor) -
        SourceConditionalVector.realizeModel advanced.tick.next
          (SourceCountedPosterior.model advanced.tick.next (SourceMinimumSharedNext.next_nonunit advanced)
            nextCoarseTable (forgetClock (clockRead 0 actor.val)))‖ ^ 2) ∧
      0 < SourceConditionalInformationLoss.amount advanced.tick.next (clockRead 0) forgetClock := by
  have base : 1 ≤ inventoryBound runtime := by
    rw [← SourceCopyCurrentCoordinates.maximum_index_val runtime]
    omega
  have enough : 2 ≤ inventoryBound (runtime.advance steps).tick.next := by
    rw [SourceActualImageStep.next_bound, SourceGraphRecurrence.advance_depth]
    omega
  let current := (runtime.advance steps).tick.next
  let left : Actors current := ⟨0, by omega⟩
  let right : Actors current := ⟨2, Nat.lt_succ_of_le enough⟩
  have collision : forgetClock (clockRead 0 left.val) = forgetClock (clockRead 0 right.val) := by
    simp only [SourceConditionalNativeMerge.clock_factor]
    change (0 : ZMod 2) = 2
    decide
  have different : clockRead 0 left.val ≠ clockRead 0 right.val := by
    intro same
    have forced := SourceConditionalNativeObservers.clock_injective 0 same
    have impossible : (0 : Nat) = 2 := forced
    omega
  have gapPositive : 0 < SourceConditionalMergeLoss.gap current (clockRead 0) forgetClock :=
    SourceConditionalMergeLoss.gap_positive_of_collision current (clockRead 0) forgetClock
      left right collision different
  have amountPositive : 0 < SourceConditionalInformationLoss.amount current (clockRead 0) forgetClock :=
    (SourceConditionalInformationLoss.amount_positive_iff_gap current (clockRead 0) forgetClock).mpr gapPositive
  dsimp only
  constructor
  · rw [continued_next_table_loss runtime nonunit keys inventory samples budgets steps]
    exact gapPositive
  · exact amountPositive

example (current : LivingRuntimeState process) :
    SourceConditionalMergeLoss.gap current (clockRead 0) (fun key : ℤ × ℤ => key) = 0 := by
  apply (SourceConditionalMergeLoss.lossless_iff current (clockRead 0)
    (fun key : ℤ × ℤ => key)).mpr
  intro _ _ same
  exact same

end
end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
