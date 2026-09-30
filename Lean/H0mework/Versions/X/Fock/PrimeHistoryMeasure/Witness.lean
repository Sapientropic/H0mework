import H0mework.Versions.X.Fock.PrimeHistoryMeasure.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionMeasure

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

variable (runtime : LivingRuntimeState process) (depth : Nat)

def newest : FieldSpace depth (inventoryBound (next runtime)) :=
  Actor.currentTransfer depth (inventoryBound (next runtime))
    (cotest (historyPMF (inventoryBound (next runtime))) (Fin.last (inventoryBound (next runtime))))

theorem newest_samples :
    Actor.currentPullback depth (inventoryBound (next runtime)) (newest runtime depth) =
      cotest (historyPMF (inventoryBound (next runtime))) (Fin.last (inventoryBound (next runtime))) :=
  actor_transfer_samples depth _ _

theorem newest_query :
    Recorded.query depth (inventoryBound (next runtime)) (Fin.last (inventoryBound (next runtime)))
      (newest runtime depth) = 1 := by
  have actual := congrArg (fun value : SourceWeightedRecovery.Space (historyPMF (inventoryBound (next runtime))) =>
    value (Fin.last (inventoryBound (next runtime)))) (newest_samples runtime depth)
  rw [Actor.currentPullback_at, cotest_at _ _ (SourceUniformFibreVariance.source_positive _ _)] at actual
  simpa only [SourceGeneratedRecordFrame.query_sample] using actual

theorem newest_actual_read :
    newest runtime depth (fieldPoint nativeStep (rawWords depth) ((next runtime).current.visit.current : Current)) = 1 := by
  rw [← new_source_read runtime depth]
  exact (SourceGeneratedRecordFrame.query_sample depth _ _ (newest runtime depth)).symm.trans (newest_query runtime depth)

theorem newest_norm : ‖newest runtime depth‖ = 1 / Real.sqrt (inventoryBound (next runtime) + 1 : ℝ) := by
  rw [newest, actor_transfer_norm, cotest_norm, SourceUniformFibreVariance.source_weight, Real.sqrt_div, Real.sqrt_one]
  norm_num

theorem newest_ne_zero : newest runtime depth ≠ 0 := by
  intro zero
  have actual := newest_query runtime depth
  rw [zero, map_zero] at actual
  norm_num at actual

theorem newest_lost_from_prior : recover runtime depth (newest runtime depth) = 0 := by
  apply (Actor.currentPullback depth (inventoryBound runtime)).injective
  change Actor.currentPullback depth (inventoryBound runtime)
    (restrict depth (retained runtime) (newest runtime depth)) = _
  rw [restrict_samples, newest_samples, SourceHistoryGrowth.restrict_new_cotest
    (retained runtime) _ (Nat.succ_le_of_lt (inventory_grows runtime)), map_zero]

theorem newest_in_remainder : newMaterial runtime depth (newest runtime depth) = newest runtime depth := by
  change remainder depth (retained runtime) (newest runtime depth) = _
  rw [remainder_eq]
  change newest runtime depth - preserve runtime depth (recover runtime depth (newest runtime depth)) = _
  rw [newest_lost_from_prior, map_zero, sub_zero]

theorem no_prior_only_restore :
    ¬ ∃ restore : FieldSpace depth (inventoryBound runtime) → FieldSpace depth (inventoryBound (next runtime)),
      ∀ value, restore (recover runtime depth value) = value := by
  rintro ⟨restore, recovers⟩
  have atZero := recovers 0
  rw [map_zero] at atZero
  have atNew := recovers (newest runtime depth)
  rw [newest_lost_from_prior, atZero] at atNew
  exact newest_ne_zero runtime depth atNew.symm

end
end SourceGeneratedAcquisitionMeasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
