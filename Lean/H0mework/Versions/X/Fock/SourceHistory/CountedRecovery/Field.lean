import H0mework.Versions.X.Fock.SourceHistory.CountedRecovery.Energy
import H0mework.Versions.X.Fock.SourceHistory.CountedRecovery.Table

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedRecovery

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceRetainedReceiver (At)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem frame_field_error (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) :
    ((inventoryBound runtime + 1 : Nat) : ℝ) *
      SourceConditionalVector.dynamicError runtime depth (SourceRetainedCoarsening.observationTable runtime frame depth) =
        error runtime (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock)
          (forgetClock ∘ clockRead 0) := by
  rw [SourceConditionalVector.dynamicError, SourceConditionalInventory.sum_count, error]
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceRetainedCoarsening.observation_dynamic, ← SourceConditionalInventory.values_original,
    Function.comp_apply, SourceConditionalNativeMerge.clock_factor]

private theorem table_mixed_residual (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (coarse : ZMod 2) :
    (∑ key ∈ table.keys.toFinset, (SourceCountedObservation.weight table forgetClock coarse key : ℂ) •
      (SourceCountedObservation.readValue runtime table key - SourceConditionalVector.realizeModel runtime
        (SourceRetainedReceiver.model runtime frame key))) =
      SourceRetainedReceiver.residual runtime
        (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock) coarse := by
  simp only [SourceCountedObservation.inventory_source _ _ table frame source,
    SourceCountedObservation.weight_source runtime table frame source,
    SourceCountedObservation.readValue_source runtime table frame (clockRead 0) source native keys]
  exact (SourceRetainedCoarsening.residual_merge runtime frame forgetClock coarse).symm

theorem field_update (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) :
    let bornKey := forgetClock (clockRead 0 runtime.tick.next.state)
    let count := SourceCountedObservation.total table forgetClock bornKey
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth
      (SourceCountedObservation.observationTable runtime.tick.next
        (SourceCountedObservation.step (inventoryBound runtime) table (clockRead 0 runtime.tick.next.state)) depth) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) *
        SourceConditionalVector.dynamicError runtime depth (SourceCountedObservation.observationTable runtime table depth) +
      SourceConditionalNativeBirth.innovation runtime (forgetClock ∘ clockRead 0) -
        (count : ℝ) / (count + 1) *
          ‖∑ key ∈ table.keys.toFinset, (SourceCountedObservation.weight table forgetClock bornKey key : ℂ) •
            (SourceCountedObservation.readValue runtime table key - SourceConditionalVector.realizeModel runtime
              (SourceRetainedReceiver.model runtime frame key))‖ ^ 2 := by
  dsimp only
  have nextCount : ((inventoryBound runtime + 2 : Nat) : ℝ) =
      ((inventoryBound runtime.tick.next + 1 : Nat) : ℝ) := by
    rw [SourceActualImageStep.next_bound]
  rw [nextCount, next_observation runtime table frame source native keys depth,
    frame_field_error, SourceCountedObservation.observation_source runtime table frame source native keys depth,
    frame_field_error, SourceRetainedCoarsening.merge_next runtime frame (clockRead 0) forgetClock native keys,
    table_mixed_residual runtime table frame source native keys]
  simp only [total_merged_count runtime table frame source forgetClock]
  have paid := error_update (Key := ZMod 2) runtime
    (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock)
    (forgetClock ∘ clockRead 0)
    (SourceRetainedCoarsening.native_source (inventoryBound runtime) (maximumIndex runtime).val
      frame (clockRead 0) forgetClock native keys)
  simp only [Function.comp_apply] at paid
  with_reducible exact paid

end
end SourceCountedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
