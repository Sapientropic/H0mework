import H0mework.Fock.RetainedReceiver.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem continued_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) (steps : Nat) :
    ‖residual (runtime.advance steps) (trajectory runtime (start (inventoryBound runtime) (maximumIndex runtime).val nonunit
        (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples) (fun offset => read (inventoryBound runtime + offset + 1)) steps) key‖ ^ 2 ≤
      SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
        SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
          (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0
            (SourceReceivedKeyInventory.extend (inventoryBound runtime) (maximumIndex runtime).val
              (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples key) -
            SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
              (SourceConditionalNativePosterior.decoder runtime read key)) := by
  exact (trajectory_error_bound runtime
    (start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples)
    read key (start_native runtime nonunit read samples budgets) steps).trans
      (start_bound runtime nonunit read samples key budgets)

theorem continued_model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) (steps : Nat) :
    let initial := start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    model (runtime.advance steps) (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) key =
      SourceConditionalNativePosterior.model (runtime.advance steps) read key := by
  dsimp only
  exact model_source (runtime.advance steps) _ read key
    (trajectory_native runtime _ read (start_native runtime nonunit read samples budgets) steps)

theorem continued_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (key : Key)
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2) (steps : Nat)
    (supported : key ∈ ((SourceGeneratedRuntimeHistoryProbability.historyPMF (inventoryBound (runtime.advance steps))).map
      (fun actor : SourceConditionalModel.Actors (runtime.advance steps) => read actor.val)).support) :
    let initial := start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    type_of% (conditional_error (runtime.advance steps) (trajectory_nonunit runtime nonunit steps)
      (trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps) read key (trajectory_native runtime initial read (start_native runtime nonunit read samples budgets) steps) supported) := by
  dsimp only
  exact conditional_error (runtime.advance steps) (trajectory_nonunit runtime nonunit steps) _ read key
    (trajectory_native runtime _ read (start_native runtime nonunit read samples budgets) steps) supported

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
