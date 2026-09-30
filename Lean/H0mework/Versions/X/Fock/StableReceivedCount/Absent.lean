import H0mework.Versions.X.Fock.StableReceivedCount.Budget

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem absent_state (runtime : LivingRuntimeState process) (read : Nat → Key) (key : Key)
    (absent : key ∉ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    SourceConditionalNativeObservers.generate read (inventoryBound runtime) key = (0, fun _ => 0) := by
  apply SourceConditionalNativeObservers.generated_outside
  intro actor same
  exact absent ((PMF.mem_support_map_iff _ _ _).mpr
    ⟨actor, SourceUniformFibreVariance.source_positive _ _, same.symm⟩)

theorem absent_decoder (runtime : LivingRuntimeState process) (read : Nat → Key) (key : Key)
    (absent : key ∉ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    SourceConditionalNativePosterior.decoder runtime read key = 0 := by
  simp only [SourceConditionalNativePosterior.decoder, SourceConditionalNativePosterior.model,
    absent_state runtime read key absent, Rat.cast_zero, zero_smul, Finset.sum_const_zero, map_zero]

theorem count_zero_of_small (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (small : ‖SourceConditionalVector.realizeModel runtime
      (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples))‖ <
        SourcePosteriorStability.threshold runtime) :
    count (inventoryBound runtime) (maximumIndex runtime).val nonunit samples = 0 := by
  rw [count_source]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro actor inside
  have above := (Finset.mem_filter.mp inside).2
  have difference := SourcePosteriorStability.weights_difference runtime
    (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)) 0 actor
  have zero : SourcePosteriorReadback.readWeight runtime 0 actor = 0 := by
    simp [SourcePosteriorReadback.readWeight]
  rw [zero, ENNReal.toReal_zero, map_zero, sub_zero, sub_zero,
    abs_of_nonneg (ENNReal.toReal_nonneg (a := SourcePosteriorReadback.readWeight runtime
      (SourceWindowPosterior.model runtime nonunit (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)) actor))] at difference
  exact (not_lt_of_ge difference) (small.trans above)

theorem count_complete (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (read : Nat → Key) (key : Key)
    (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key)) < SourcePosteriorStability.threshold runtime ^ 2) :
    count (inventoryBound runtime) (maximumIndex runtime).val nonunit samples =
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 := by
  by_cases present : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support
  · exact count_from_precision runtime nonunit samples read key present budget
  · rw [absent_state runtime read key present]
    apply count_zero_of_small runtime nonunit samples
    have bound := SourceWindowPosterior.bias_bound runtime nonunit read key
      (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples)
    rw [SourceWindowPosterior.decoder_tail_zero runtime nonunit, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at bound
    rw [absent_decoder runtime read key present, sub_zero] at bound
    rw [absent_decoder runtime read key present] at budget
    have positive := SourcePosteriorStability.threshold_positive runtime
    nlinarith

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
