import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Representation
import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Margin
import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Complete
import H0mework.Versions.X.Fock.SourceHistory.CountedAdvance.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceRetainedReceiver (At)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

theorem continued_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Fine) (keys : List Fine)
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (forget : Fine → Coarse) (steps : Nat) (coarse : Coarse) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => read (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    SourceCountedPosterior.restore (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) (mergeTable fineTable forget) coarse =
        SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound (runtime.advance steps)) coarse := by
  dsimp only
  let initial : At runtime Fine := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  let current : At (runtime.advance steps) Fine := SourceRetainedReceiver.trajectory runtime initial
    (fun offset => read (inventoryBound runtime + offset + 1)) steps
  let fineTable := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => read (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  let merged : At (runtime.advance steps) Coarse := SourceRetainedCoarsening.merge
    (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val current forget
  have initialNative : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime) :=
    SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  have fineSource : SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val fineTable current := by
    with_reducible exact (SourceCountedObservation.received_simulates runtime nonunit read keys inventory samples budgets steps)
  have currentNative : current.native = SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps)) := by
    with_reducible exact (SourceRetainedReceiver.trajectory_native runtime initial read initialNative steps)
  have currentKeys : current.keys =
      SourceUniformFibreVariance.outputs (inventoryBound (runtime.advance steps)) (fun actor => read actor.val) := by
    with_reducible exact (SourceRetainedReceiver.trajectory_keys runtime initial read rfl steps)
  have source : SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val (mergeTable fineTable forget) merged :=
    merge_simulates _ _ fineTable current fineSource forget
  have native : merged.native = SourceConditionalNativeObservers.generate (forget ∘ read)
      (inventoryBound (runtime.advance steps)) :=
    SourceRetainedCoarsening.native_source _ _ current read forget currentNative currentKeys
  have margin : ‖((merged.native coarse).1 : ℂ) •
      SourceRetainedReceiver.residual (runtime.advance steps) merged coarse‖ < 1 / 2 := by
    with_reducible exact (trajectory_half_margin runtime nonunit read samples budgets forget coarse steps)
  with_reducible exact (SourceCountedPosterior.restored_source (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) (mergeTable fineTable forget) merged
    (forget ∘ read) coarse source native margin)

theorem continued_next_model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Fine) (keys : List Fine)
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (forget : Fine → Coarse) (steps : Nat) (coarse : Coarse) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    let fineTable := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => read (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    SourceCountedAdvance.nextModel (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (mergeTable fineTable forget) (forget (read (runtime.advance steps).tick.next.state)) coarse =
        SourceConditionalNativePosterior.model (runtime.advance steps).tick.next (forget ∘ read) coarse := by
  dsimp only
  let initial : At runtime Fine := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  let current : At (runtime.advance steps) Fine := SourceRetainedReceiver.trajectory runtime initial
    (fun offset => read (inventoryBound runtime + offset + 1)) steps
  let fineTable := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => read (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  let merged : At (runtime.advance steps) Coarse := SourceRetainedCoarsening.merge
    (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val current forget
  have initialNative : initial.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime) :=
    SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  have fineSource : SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val fineTable current := by
    with_reducible exact (SourceCountedObservation.received_simulates runtime nonunit read keys inventory samples budgets steps)
  have currentNative : current.native = SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps)) := by
    with_reducible exact (SourceRetainedReceiver.trajectory_native runtime initial read initialNative steps)
  have currentKeys : current.keys =
      SourceUniformFibreVariance.outputs (inventoryBound (runtime.advance steps)) (fun actor => read actor.val) := by
    with_reducible exact (SourceRetainedReceiver.trajectory_keys runtime initial read rfl steps)
  have source : SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val (mergeTable fineTable forget) merged :=
    merge_simulates _ _ fineTable current fineSource forget
  have native : merged.native = SourceConditionalNativeObservers.generate (forget ∘ read)
      (inventoryBound (runtime.advance steps)) :=
    SourceRetainedCoarsening.native_source _ _ current read forget currentNative currentKeys
  have margins : ∀ key, ‖((merged.native key).1 : ℂ) •
      SourceRetainedReceiver.residual (runtime.advance steps) merged key‖ < 1 / 2 := by
    intro key
    with_reducible exact (trajectory_half_margin runtime nonunit read samples budgets forget key steps)
  have paid := SourceCountedAdvance.next_model_source (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) (mergeTable fineTable forget) merged
    (forget ∘ read) coarse source native margins
  simp only [Function.comp_apply] at paid
  with_reducible exact paid

end
end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
