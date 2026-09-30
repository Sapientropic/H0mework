import H0mework.Fock.SourceHistory.CountedPosterior.Margin
import H0mework.Fock.SourceHistory.CountedPosterior.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem continued_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (keys : List Key)
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
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
    let table := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => read (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    restore (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table key =
        SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps)) key := by
  dsimp only
  let initial : SourceRetainedReceiver.At runtime Key := SourceRetainedReceiver.start
    (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  let current := SourceRetainedReceiver.trajectory runtime initial
    (fun offset => read (inventoryBound runtime + offset + 1)) steps
  let table := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => read (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  have native := SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  with_reducible exact (restored_source (runtime.advance steps)
    (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table current read key
    (SourceCountedObservation.received_simulates runtime nonunit read keys inventory samples budgets steps)
    (SourceRetainedReceiver.trajectory_native runtime initial read native steps)
    (trajectory_half_margin runtime initial read key native
      (initial_half_margin runtime nonunit read samples budgets key) steps))

theorem continued_model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (keys : List Key)
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
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
    let table := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => read (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    model (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table key =
      SourceConditionalNativePosterior.model (runtime.advance steps) read key := by
  dsimp only
  let initial : SourceRetainedReceiver.At runtime Key := SourceRetainedReceiver.start
    (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  let table := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => read (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  have paid := continued_source runtime nonunit read keys inventory samples budgets steps key
  unfold model SourceFibreExactState.model
  change (∑ actor : SourceConditionalModel.Actors (runtime.advance steps),
    ((restore (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table key).2 actor : ℂ) •
        SourceConditionalModel.nextRead (runtime.advance steps) actor) = _
  rw [paid]
  rfl

end
end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
