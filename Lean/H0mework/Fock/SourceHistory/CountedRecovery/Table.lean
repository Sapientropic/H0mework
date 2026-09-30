import H0mework.Fock.SourceHistory.CountedObservation.Field

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
variable {Key : Type*} [DecidableEq Key]

theorem step_next_simulates (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (added : Key) :
    SourceCountedObservation.Simulates (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
      (SourceCountedObservation.step (inventoryBound runtime) table added)
      (SourceRetainedReceiver.next runtime frame added) :=
  SourceCountedObservation.simulates_reindex (SourceActualImageStep.next_bound runtime).symm rfl _ _
    (SourceCountedObservation.step_simulates _ _ _ table frame source added
      (SourceReceivedConditionalStep.capacity_grows runtime (maximumIndex runtime))
      (SourceReceivedConditionalStep.birth_included runtime))

theorem next_observation (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) :
    SourceCountedObservation.observationTable runtime.tick.next
      (SourceCountedObservation.step (inventoryBound runtime) table (clockRead 0 runtime.tick.next.state)) depth =
        SourceRetainedCoarsening.observationTable runtime.tick.next
          (SourceRetainedReceiver.next runtime frame (clockRead 0 runtime.tick.next.state)) depth := by
  apply SourceCountedObservation.observation_source runtime.tick.next _ _
    (step_next_simulates runtime table frame source _)
    (SourceRetainedReceiver.next_native runtime frame (clockRead 0) native) _ depth
  rw [SourceRetainedCoarsening.next_keys, keys]
  exact SourceReceivedKeyInventory.keys_next runtime (clockRead 0)

theorem total_merged_count (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    {Coarse : Type*} [DecidableEq Coarse] (forget : Key → Coarse) (coarse : Coarse) :
    SourceCountedObservation.total table forget coarse =
      ((SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forget).native coarse).1 := by
  simp only [SourceCountedObservation.total, SourceCountedObservation.inventory_source _ _ table frame source,
    (source.rows _).count_eq, SourceRetainedCoarsening.merge, SourceConditionalNativeMerge.inventoryMerge,
    SourceConditionalNativeMerge.inventoryCount]

end
end SourceCountedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
