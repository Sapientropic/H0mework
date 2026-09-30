import H0mework.Versions.X.Fock.HistoryConditional.ReceivedMergeSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalMerge

variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse] [Fintype Fine]

def received (forget : Fine → Coarse) (bound stride : Nat) (nonunit : stride ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples bound (stride + 1)) :
    SourceConditionalNativeObservers.State Coarse bound :=
  merge forget bound (SourceFibreExactState.restoreState bound stride nonunit samples)

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem received_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    received forget (inventoryBound runtime) (maximumIndex runtime).val nonunit samples =
      SourceConditionalNativeObservers.generate (forget ∘ read) (inventoryBound runtime) := by
  rw [received, SourceFibreExactState.state_source runtime nonunit samples read budgets, source_generated]

theorem source_next (read : Nat → Fine) (forget : Fine → Coarse) (bound : Nat) :
    merge forget (bound + 1) (SourceConditionalNativeObservers.advance (fun _ => read (bound + 1)) bound
      (SourceConditionalNativeObservers.generate read bound)) =
      SourceConditionalNativeObservers.advance (fun _ => forget (read (bound + 1))) bound
        (merge forget bound (SourceConditionalNativeObservers.generate read bound)) := by
  have paid := SourceConditionalNativeMerge.merge_next read forget bound
  rw [← SourceConditionalNativeObservers.generated_next,
    ← source_native read forget (bound + 1), ← source_native read forget bound] at paid
  exact paid

theorem received_next (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Fine → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Fine) (forget : Fine → Coarse)
    (budgets : ∀ key : Fine, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    merge forget (inventoryBound runtime + 1)
      (SourceFibreExactState.next (inventoryBound runtime) (maximumIndex runtime).val nonunit samples (read runtime.tick.next.state)) =
      SourceConditionalNativeObservers.advance (fun _ => forget (read runtime.tick.next.state)) (inventoryBound runtime)
        (received forget (inventoryBound runtime) (maximumIndex runtime).val nonunit samples) := by
  have receipt := congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))
  rw [SourceFibreExactState.next, received,
    SourceFibreExactState.state_source runtime nonunit samples read budgets, receipt]
  exact source_next read forget (inventoryBound runtime)

end
end SourceReceivedConditionalMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
