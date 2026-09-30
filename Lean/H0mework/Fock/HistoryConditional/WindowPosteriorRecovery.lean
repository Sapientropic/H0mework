import H0mework.Fock.HistoryConditional.WindowPosteriorSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPosterior

open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem bias_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) (samples : Window runtime (maximumIndex runtime)) :
    ‖SourceConditionalVector.realizeModel runtime (model runtime nonunit samples) - decoder runtime read key‖ ^ 2 ≤
      ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
          SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
            (samples - recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) := by
  have restored : recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) +
      (samples - recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) = samples := by abel
  have paid := SourceWindowPrecision.error_bound runtime (maximumIndex runtime) nonunit 0 (decoder runtime read key)
    (samples - recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key))
  rw [restored] at paid
  have actual : SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples =
      SourceMinimumWindowError.readout runtime (maximumIndex runtime) nonunit 0 samples :=
    congrArg (fun map : Window runtime (maximumIndex runtime) →ₗ[ℂ] SourceJointClockGraph.Carrier => map samples)
      (SourceWindowPrecision.reader_original runtime (maximumIndex runtime) nonunit 0)
  rw [model_realization, actual, norm_sub_rev]
  exact paid

theorem support_from_samples (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (samples : Window runtime (maximumIndex runtime))
    (budget : ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
      SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
        SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
          (samples - recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) <
      SourcePosteriorStability.threshold runtime ^ 2) :
    SourcePosteriorStability.restoredSupport runtime (model runtime nonunit samples) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) key := by
  have paid := bias_bound runtime nonunit read key samples
  have positive := SourcePosteriorStability.threshold_positive runtime
  have small : ‖SourceConditionalVector.realizeModel runtime (model runtime nonunit samples) - decoder runtime read key‖ <
      SourcePosteriorStability.threshold runtime := by nlinarith
  exact SourceConditionalNativePosterior.support_restored runtime read key supported (model runtime nonunit samples) small

end
end SourceWindowPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
