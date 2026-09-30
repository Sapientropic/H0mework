import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Action
import H0mework.Versions.X.Fock.SourceHistory.CountedAdvance.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceObservationInvariantControls (parity)
open SourceConditionalModel (Actors dynamicRead)
open SourceRetainedReceiver (At)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def observationTable (runtime : LivingRuntimeState process) (table : SourceCountedObservation.Table (ZMod 2))
    (depth : Nat) : Field parity →₀ SourceJointClockGraph.Carrier :=
  (Finsupp.onFinset Finset.univ (SourceCountedObservation.readValue runtime table)
    (fun key _ => Finset.mem_univ key)).mapDomain (SourceConditionalNativeKeys.observed depth)

theorem observation_dynamic (runtime : LivingRuntimeState process) (table : SourceCountedObservation.Table (ZMod 2))
    (depth : Nat) (actor : Actors runtime) :
    observationTable runtime table depth (dynamicRead runtime depth actor) =
      SourceCountedObservation.readValue runtime table (actor.val : ZMod 2) := by
  rw [← SourceConditionalInventory.observation_original runtime depth,
    SourceConditionalNativeKeys.source_observed, observationTable,
    Finsupp.mapDomain_apply (SourceConditionalNativeKeys.observed_injective depth), Finsupp.onFinset_apply]

theorem next_observation (runtime : LivingRuntimeState process)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (depth : Nat) :
    observationTable runtime.tick.next
      (SourceCountedObservation.step (inventoryBound runtime) (mergeTable table forgetClock) (runtime.tick.next.state : ZMod 2)) depth =
    SourceCountedObservation.observationTable runtime.tick.next
      (SourceCountedObservation.step (inventoryBound runtime) table (clockRead 0 runtime.tick.next.state)) depth := by
  let current : At runtime.tick.next (ℤ × ℤ) :=
    SourceRetainedReceiver.next runtime frame (clockRead 0 runtime.tick.next.state)
  have nextSource := SourceCountedRecovery.step_next_simulates runtime table frame source (clockRead 0 runtime.tick.next.state)
  have nextNative := SourceRetainedReceiver.next_native runtime frame (clockRead 0) native
  have nextKeys : current.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime.tick.next)
      (fun actor => clockRead 0 actor.val) := by
    rw [SourceRetainedCoarsening.next_keys, keys]
    exact SourceReceivedKeyInventory.keys_next runtime (clockRead 0)
  have coarseSource := next_simulates runtime table frame (clockRead 0) forgetClock source native keys
  rw [SourceConditionalNativeMerge.clock_factor] at coarseSource
  have coarseNative := SourceRetainedCoarsening.native_source _ _ current (clockRead 0) forgetClock nextNative nextKeys
  have coarseKeys := SourceRetainedCoarsening.keys_source _ _ current (clockRead 0) forgetClock nextKeys
  unfold observationTable SourceCountedObservation.observationTable
  apply congrArg (fun data : ZMod 2 →₀ SourceJointClockGraph.Carrier =>
    data.mapDomain (SourceConditionalNativeKeys.observed depth))
  apply Finsupp.ext
  intro key
  simp only [Finsupp.onFinset_apply]
  have coarseValue := SourceCountedObservation.readValue_source runtime.tick.next _ _
    (forgetClock ∘ clockRead 0) coarseSource coarseNative coarseKeys key
  have fineValue := SourceCountedObservation.mixedValue_source runtime.tick.next _ current (clockRead 0)
    nextSource nextNative nextKeys forgetClock key
  exact coarseValue.trans fineValue.symm

theorem next_field_balance (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table (ZMod 2)) (frame : At runtime (ZMod 2))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2)) (inventoryBound runtime))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2)
    (depth : Nat) :
    let nextTable := SourceCountedObservation.step (inventoryBound runtime) table (runtime.tick.next.state : ZMod 2)
    SourceConditionalVector.dynamicError runtime.tick.next depth (observationTable runtime.tick.next nextTable depth) =
      SourceConditionalVector.dynamicVariance runtime.tick.next depth +
      ∑ actor : Actors runtime.tick.next, (historyPMF (inventoryBound runtime.tick.next) actor).toReal *
        ‖SourceCountedObservation.readValue runtime.tick.next nextTable (actor.val : ZMod 2) -
          SourceConditionalVector.realizeModel runtime.tick.next
            (SourceCountedAdvance.nextModel runtime nonunit table (runtime.tick.next.state : ZMod 2) (actor.val : ZMod 2))‖ ^ 2 := by
  dsimp only
  rw [SourceConditionalVector.dynamic_error_decomposition]
  apply congrArg (fun value : ℝ => SourceConditionalVector.dynamicVariance runtime.tick.next depth + value)
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceRetainedCoarsening.field_mean, observation_dynamic,
    SourceCountedAdvance.next_model_source runtime nonunit table frame (fun index : Nat => (index : ZMod 2))
      (actor.val : ZMod 2) source native margins]
  exact congrArg (fun value : ℝ => (historyPMF (inventoryBound runtime.tick.next) actor).toReal * value ^ 2)
    (norm_sub_rev _ _)

end
end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
