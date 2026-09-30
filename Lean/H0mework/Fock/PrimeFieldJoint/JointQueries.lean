import H0mework.Fock.PrimeFieldJoint.JointSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionJoint

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure
open SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private theorem query_from_actor (depth bound : Nat)
    (value : SourceWeightedRecovery.Space (historyPMF bound)) (index : Fin (bound + 1)) :
    Recorded.query depth bound index (Actor.currentTransfer depth bound value) = value index := by
  have actual := congrArg (fun samples : SourceWeightedRecovery.Space (historyPMF bound) => samples index)
    (actor_transfer_samples depth bound value)
  rw [Actor.currentPullback_at] at actual
  simpa only [SourceGeneratedRecordFrame.query_sample] using actual

theorem density_query (runtime : LivingRuntimeState process) (index : Fin (inventoryBound runtime + 1)) :
    Recorded.query (depth runtime) (inventoryBound runtime) index (sourceDensity runtime) =
      (Real.sqrt (historyPMF (inventoryBound runtime) index).toReal : ℂ) := by
  change Recorded.query _ _ _ (Actor.currentTransfer _ _ (SourceHistoryWord.density _)) = _
  rw [query_from_actor, SourceHistoryWord.density_at]

theorem added_query (runtime : LivingRuntimeState process) (index : Fin (inventoryBound (next runtime) + 1)) :
    Recorded.query (depth (next runtime)) (inventoryBound (next runtime)) index (addedDensity runtime) =
      SourceHistoryGrowth.remainder (retained runtime) (SourceHistoryWord.density (inventoryBound (next runtime))) index :=
  query_from_actor _ _ _ index

theorem added_query_prior (runtime : LivingRuntimeState process) (index : Fin (inventoryBound runtime + 1)) :
    Recorded.query (depth (next runtime)) (inventoryBound (next runtime))
      (SourceHistoryGrowth.includeActor (retained runtime) index) (addedDensity runtime) = 0 := by
  rw [added_query, SourceHistoryGrowth.remainder_at_prior]

theorem added_query_new (runtime : LivingRuntimeState process)
    (index : Fin (inventoryBound (next runtime) + 1)) (new : inventoryBound runtime + 1 ≤ index.val) :
    Recorded.query (depth (next runtime)) (inventoryBound (next runtime)) index (addedDensity runtime) =
      (Real.sqrt (historyPMF (inventoryBound (next runtime)) index).toReal : ℂ) := by
  rw [added_query, SourceHistoryGrowth.remainder_at_new (retained runtime) _ index new, SourceHistoryWord.density_at]

theorem added_ne_zero (runtime : LivingRuntimeState process) : addedPacket runtime ≠ 0 := by
  intro vanished
  have actual := added_mass runtime
  rw [vanished, map_zero] at actual
  have realPart := congrArg Complex.re actual
  simp only [Complex.zero_re, Complex.ofReal_re] at realPart
  linarith only [realPart, (prior_mass_pos_lt_one runtime).2]

end
end SourceGeneratedAcquisitionJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
