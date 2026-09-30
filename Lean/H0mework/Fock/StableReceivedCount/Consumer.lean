import H0mework.Fock.StableReceivedCount.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem model_writeback (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    let oldError := SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
      (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples) -
        SourceConditionalNativePosterior.decoder runtime read key
    SourceConditionalVector.realizeModel runtime.tick.next
      (updatedModel runtime nonunit samples (decide (key = read runtime.tick.next.state))) -
      (if key = read runtime.tick.next.state then
        (contraction (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 : ℂ) • oldError
       else oldError) = SourceConditionalNativePosterior.decoder runtime.tick.next read key := by
  dsimp only
  have residual := residual_from_precision runtime nonunit samples read key budget
  rw [model_realization, ← residual]
  abel

theorem model_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => read actor.val)).support)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    let oldError := SourceReceivedConditionalStep.completeValue runtime (maximumIndex runtime) 0
      (SourceRationalWindowReadout.decode (inventoryBound runtime) (maximumIndex runtime).val samples) -
        SourceConditionalNativePosterior.decoder runtime read key
    (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
        SourceConditionalVector.realizeModel runtime.tick.next
          (updatedModel runtime nonunit samples (decide (key = read runtime.tick.next.state)))‖ ^ 2) =
      (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
          SourceConditionalNativePosterior.decoder runtime.tick.next read key‖ ^ 2) +
        (if key = read runtime.tick.next.state then
          (contraction (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 : ℝ)^2 * ‖oldError‖^2
         else ‖oldError‖^2) := by
  dsimp only
  rw [model_realization, SourceConditionalNativePosterior.error_decomposition runtime.tick.next read key supported,
    norm_sub_rev (SourceConditionalNativePosterior.decoder runtime.tick.next read key), residual_energy runtime nonunit samples read key budget]

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
