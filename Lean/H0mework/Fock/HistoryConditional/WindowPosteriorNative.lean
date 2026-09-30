import H0mework.Fock.HistoryConditional.WindowPosteriorRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPosterior

open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem actor_tail_zero (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (actor : Actors runtime) :
    residual runtime (maximumIndex runtime) 0 (SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) = 0 := by
  have included : actor.val + 1 ≤ cutoff runtime (maximumIndex runtime) 0 := by
    have bound := SourceCopyCurrentCoordinates.maximum_cutoff runtime
    have inside := actor.isLt
    change actor.val < inventoryBound runtime + 1 at inside
    have positive : 1 ≤ inventoryBound runtime := by
      rw [SourceCopyCurrentCoordinates.maximum_index_val] at nonunit
      omega
    nlinarith
  rw [SourceConditionalVector.realized_next, SourceConditionalVector.actor, SourceCopyNativeModelStep.source_value_next]
  change residual runtime (maximumIndex runtime) 0 (SourceCopyNativeModelStep.sourceValue (runtimeAt (actor.val + 1))) = 0
  apply (SourceCopyCurrentCoordinates.complete_fibre runtime (maximumIndex runtime) 0 _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyCurrentCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyCurrentCoordinates.residual_outside _ _ _ _ _ beyond, SourceCopyPhaseRecovery.native_hilbert,
      runtimeAt_state, if_neg (ne_of_gt (lt_of_le_of_lt included beyond))]
    rfl

theorem decoder_tail_zero (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) : residual runtime (maximumIndex runtime) 0 (decoder runtime read key) = 0 := by
  simp only [decoder, SourceConditionalNativePosterior.model, map_sum, map_smul,
    actor_tail_zero runtime nonunit, smul_zero, Finset.sum_const_zero]

theorem model_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) :
    model runtime nonunit (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) =
      SourceConditionalNativePosterior.model runtime read key := by
  have source := SourceCopyCurrentCoordinates.reconstruction runtime (maximumIndex runtime) 0 (decoder runtime read key)
  rw [decoder_tail_zero runtime nonunit read key, add_zero] at source
  have actual := congrArg (fun map : SourceOperatorObservationAcquisition.Window runtime (maximumIndex runtime) →ₗ[ℂ]
      SourceJointClockGraph.Carrier =>
        map (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)))
    (SourceWindowPrecision.reader_original runtime (maximumIndex runtime) nonunit 0)
  change SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0
    (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) =
      SourceMinimumWindowError.readout runtime (maximumIndex runtime) nonunit 0
        (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) at actual
  rw [SourceMinimumWindowError.readout_source, source] at actual
  rw [model, actual, decoder]
  exact SourceConditionalStream.project_realization runtime _

theorem support_from_precision (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (samples : SourceOperatorObservationAcquisition.Window runtime (maximumIndex runtime))
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (samples - recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key)) <
      SourcePosteriorStability.threshold runtime ^ 2) :
    SourcePosteriorStability.restoredSupport runtime (model runtime nonunit samples) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime) (fun actor => read actor.val) key := by
  apply support_from_samples runtime nonunit read key supported samples
  simpa only [decoder_tail_zero runtime nonunit read key, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] using budget

end
end SourceWindowPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
