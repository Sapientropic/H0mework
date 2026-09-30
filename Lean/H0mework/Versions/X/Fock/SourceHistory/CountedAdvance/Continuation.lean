import H0mework.Versions.X.Fock.SourceHistory.CountedAdvance.State

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedAdvance

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem continued_next (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
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
    let table := SourceCountedObservation.run (inventoryBound runtime)
      (fun offset => read (inventoryBound runtime + offset + 1))
      (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
    next (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table
      (read (runtime.advance steps).tick.next.state) =
        SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps) + 1) := by
  dsimp only
  let initial : SourceRetainedReceiver.At runtime Key := SourceRetainedReceiver.start
    (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  let table := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => read (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  have restored : SourceFibreExactState.restoreState (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (SourceCountedAdvance.samples (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val table) =
        SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps)) := by
    funext key
    exact SourceCountedPosterior.continued_source runtime nonunit read keys inventory samples budgets steps key
  have receipt := congrArg read ((inventory_bound (runtime.advance steps).tick.next).symm.trans
    (SourceActualImageStep.next_bound (runtime.advance steps)))
  rw [next, SourceFibreExactState.next, restored, receipt, SourceConditionalNativeObservers.generated_next]
  rfl

end
end SourceCountedAdvance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
