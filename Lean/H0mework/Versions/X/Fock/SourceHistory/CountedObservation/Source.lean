import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Value

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (Frame Raw At)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Key : Type*} [DecidableEq Key]
noncomputable section

theorem fromInventory_simulates (bound stride : Nat) (keys : List Key) (frame : Frame Key bound stride)
    (inventory : keys.toFinset = frame.keys)
    (outside : ∀ key, key ∉ frame.keys → (frame.native key).1 = 0) :
    Simulates bound stride (fromInventory bound stride keys frame) frame := by
  refine ⟨?_, ?_⟩
  · intro key
    rw [fromInventory, collect_keys, ← List.mem_toFinset, inventory]
  · intro key
    have membership : key ∈ keys ↔ key ∈ frame.keys := by rw [← List.mem_toFinset, inventory]
    by_cases present : key ∈ frame.keys
    · have inkeys : key ∈ keys := membership.mpr present
      simp only [lookup, fromInventory, collect_lookup, if_pos inkeys, Option.getD_some]
      exact represents_encode _ _ _ _
    · have notInKeys : key ∉ keys := fun h => present (membership.mp h)
      simp only [lookup, fromInventory, collect_lookup, if_neg notInKeys, Option.getD_none,
        outside key present, SourceRetainedReceiver.rawAt, dif_neg present]
      exact empty_represents bound stride

theorem simulates_reindex {bound target stride nextStride : Nat} (bounds : bound = target) (strides : stride = nextStride)
    (table : Table Key) (frame : Frame Key bound stride) (source : Simulates bound stride table frame) :
    Simulates target nextStride table (SourceRetainedReceiver.reindex bounds strides frame) := by
  cases bounds
  cases strides
  exact source

theorem trajectory_simulates (runtime : LivingRuntimeState process) (table : Table Key) (frame : At runtime Key)
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (receipts : Nat → Key) (steps : Nat) :
    Simulates (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (run (inventoryBound runtime) receipts table steps) (SourceRetainedReceiver.trajectory runtime frame receipts steps) :=
  simulates_reindex (SourceGraphRecurrence.advance_depth runtime steps).symm
    (SourceRetainedReceiver.maximum_advance runtime steps).symm _ _
      (run_simulates _ _ table frame source receipts steps)

theorem source_decode (bound stride : Nat) (table : Table Key) (frame : Frame Key bound stride) (read : Nat → Key)
    (source : Simulates bound stride table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read bound)
    (keys : frame.keys = SourceUniformFibreVariance.outputs bound (fun actor => read actor.val)) (key : Key) :
    decode bound stride (lookup table key) = SourceRetainedReceiver.rawAt bound stride frame key := by
  by_cases present : key ∈ frame.keys
  · have occurrence : ∃ actor : Fin (bound + 1), read actor.val = key := by
      rw [keys] at present
      obtain ⟨actor, _, same⟩ := Finset.mem_image.mp present
      exact ⟨actor, same⟩
    obtain ⟨actor, same⟩ := occurrence
    apply simulated_decode _ _ _ _ source key
    rw [native]
    exact (SourceConditionalNativePosterior.count_positive read bound key actor same).ne'
  · have absent : table.lookup key = none := AList.lookup_eq_none.mpr (fun inside => present ((source.keys key).mp inside))
    rw [lookup, absent, Option.getD_none, SourceRetainedReceiver.rawAt, dif_neg present]
    apply Prod.ext
    · funext position
      simp [decode, emptyEntry, coordinate]
    · simp [decode, emptyEntry]

def readValue (runtime : LivingRuntimeState process) (table : Table Key) (key : Key) : SourceJointClockGraph.Carrier :=
  SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
    (decode (inventoryBound runtime) (maximumIndex runtime).val (lookup table key))

theorem readValue_source (runtime : LivingRuntimeState process) (table : Table Key) (frame : At runtime Key) (read : Nat → Key)
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) (key : Key) :
    readValue runtime table key = SourceRetainedReceiver.value runtime frame key := by
  rw [readValue, source_decode _ _ table frame read source native keys key]
  rfl

theorem initial_readValue (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (key : Key) :
    readValue runtime
      (ofFrame (inventoryBound runtime) (maximumIndex runtime).val
        (SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
          (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples)) key =
      SourceRetainedReceiver.value runtime
        (SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
          (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples) key := by
  let frame := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  have native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime) := by
    exact SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  have keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val) := rfl
  have outside : ∀ key, key ∉ frame.keys → (frame.native key).1 = 0 := by
    intro other absent
    rw [native]
    have outsideRow := SourceReceivedConditionalMerge.outside_row read (inventoryBound runtime) other
      (by rwa [← keys])
    rw [outsideRow]
  have simulated := ofFrame_simulates (inventoryBound runtime) (maximumIndex runtime).val frame outside
  exact readValue_source runtime (ofFrame (inventoryBound runtime) (maximumIndex runtime).val frame)
    frame read simulated native keys key

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
