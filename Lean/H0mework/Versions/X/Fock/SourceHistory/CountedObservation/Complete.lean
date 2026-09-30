import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Key : Type*} [DecidableEq Key]
noncomputable section

theorem received_simulates (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (keys : List Key)
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) :
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    Simulates (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (run (inventoryBound runtime) (fun offset => read (inventoryBound runtime + offset + 1))
        (fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps)
      (SourceRetainedReceiver.trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) := by
  dsimp only
  apply trajectory_simulates
  apply fromInventory_simulates _ _ keys _ inventory
  exact SourceRetainedCoarsening.outside_source runtime _ read
    (SourceRetainedReceiver.start_native runtime nonunit read samples budgets) rfl

theorem read_residual (runtime : LivingRuntimeState process) (table : Table Key) (frame : SourceRetainedReceiver.At runtime Key)
    (read : Nat → Key) (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) (key : Key) :
    ‖readValue runtime table key - SourceConditionalVector.realizeModel runtime (SourceRetainedReceiver.model runtime frame key)‖ ^ 2 =
      ‖SourceRetainedReceiver.residual runtime frame key‖ ^ 2 := by
  rw [readValue_source runtime table frame read source native keys key]
  rfl

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
