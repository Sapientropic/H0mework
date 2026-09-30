import H0mework.Versions.X.Fock.FibreExactState.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFibreExactState

def next {Key : Type*} [DecidableEq Key] (bound stride : Nat) (nonunit : stride ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples bound (stride + 1)) (added : Key) :
    SourceConditionalNativeObservers.State Key (bound + 1) :=
  SourceConditionalNativeObservers.advance (fun _ => added) bound (restoreState bound stride nonunit received)

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem next_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key)
    (budgets : ∀ key : Key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (received key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    next (inventoryBound runtime) (maximumIndex runtime).val nonunit received (read runtime.tick.next.state) =
      SourceConditionalNativeObservers.generate read (inventoryBound runtime + 1) := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [next, state_source runtime nonunit received read budgets, receipt, SourceConditionalNativeObservers.generated_next]
  rfl

open SourceConditionalModel (Actors NextModel nextRead)

def nextModel (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (added key : Key) : NextModel runtime.tick.next :=
  ∑ actor : Actors runtime.tick.next,
    ((next (inventoryBound runtime) (maximumIndex runtime).val nonunit received added key).2
      (Fin.cast (congrArg Nat.succ (SourceActualImageStep.next_bound runtime)) actor) : ℂ) •
        nextRead runtime.tick.next actor

theorem next_model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budgets : ∀ key : Key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (received key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    nextModel runtime nonunit received (read runtime.tick.next.state) key =
      SourceConditionalNativePosterior.model runtime.tick.next read key := by
  have aligned (a b : Nat) (same : a = b) (actor : Fin (a + 1)) :
      (SourceConditionalNativeObservers.generate read b key).2 (Fin.cast (congrArg Nat.succ same) actor) =
        (SourceConditionalNativeObservers.generate read a key).2 actor := by
    cases same
    rfl
  rw [nextModel, next_source runtime nonunit received read budgets, SourceConditionalNativePosterior.model]
  apply Finset.sum_congr rfl
  intro actor _
  rw [aligned _ _ (SourceActualImageStep.next_bound runtime) actor]

end
end SourceFibreExactState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
