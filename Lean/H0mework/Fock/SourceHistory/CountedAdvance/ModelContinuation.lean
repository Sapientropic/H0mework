import H0mework.Fock.SourceHistory.CountedAdvance.Continuation
import H0mework.Fock.SourceHistory.CountedAdvance.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedAdvance

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

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
    nextModel (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table
      (read (runtime.advance steps).tick.next.state) key =
        SourceConditionalNativePosterior.model (runtime.advance steps).tick.next read key := by
  dsimp only
  let initial : SourceRetainedReceiver.At runtime Key := SourceRetainedReceiver.start
    (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  let table := SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => read (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime) (maximumIndex runtime).val keys initial) steps
  have generated : SourceFibreExactState.next (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (SourceCountedAdvance.samples (inventoryBound (runtime.advance steps)) (maximumIndex (runtime.advance steps)).val table)
      (read (runtime.advance steps).tick.next.state) =
        SourceConditionalNativeObservers.generate read (inventoryBound (runtime.advance steps) + 1) := by
    have paid := continued_next runtime nonunit read keys inventory samples budgets steps
    dsimp only [next] at paid
    with_reducible exact paid
  have aligned (left right : Nat) (same : left = right) (actor : Fin (left + 1)) :
      (SourceConditionalNativeObservers.generate read right key).2 (Fin.cast (congrArg Nat.succ same) actor) =
        (SourceConditionalNativeObservers.generate read left key).2 actor := by
    cases same
    rfl
  change nextModel (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) table
    (read (runtime.advance steps).tick.next.state) key = _
  rw [nextModel, SourceFibreExactState.nextModel, generated, SourceConditionalNativePosterior.model]
  apply Finset.sum_congr rfl
  intro actor _
  rw [aligned _ _ (SourceActualImageStep.next_bound (runtime.advance steps)) actor]

end
end SourceCountedAdvance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
