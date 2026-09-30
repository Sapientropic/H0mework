import H0mework.Fock.SourceHistory.CountedObservation.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (At)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Key : Type*} [DecidableEq Key]
noncomputable section

theorem source_ofFrame (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) :
    Simulates (inventoryBound runtime) (maximumIndex runtime).val
      (ofFrame (inventoryBound runtime) (maximumIndex runtime).val frame) frame := by
  apply ofFrame_simulates
  intro key absent
  rw [native, SourceReceivedConditionalMerge.outside_row read (inventoryBound runtime) key (by rwa [← keys])]

theorem continued_readValue (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) (key : Key) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    readValue (runtime.advance steps)
      (run (inventoryBound runtime) (fun offset => read (inventoryBound runtime + offset + 1))
        (ofFrame (inventoryBound runtime) (maximumIndex runtime).val initial) steps) key =
      SourceRetainedReceiver.value (runtime.advance steps)
        (SourceRetainedReceiver.trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key := by
  dsimp only
  have native := SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  exact readValue_source (runtime.advance steps) _ _ read
    (trajectory_simulates runtime _ _ (source_ofFrame runtime _ read native rfl) _ steps)
    (SourceRetainedReceiver.trajectory_native runtime _ read native steps)
    (SourceRetainedReceiver.trajectory_keys runtime _ read rfl steps) key

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
