import H0mework.Fock.PrimeHistoryMeasure.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionMeasure

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceGeneratedAtomicObservation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

variable (depth : Nat) {old fresh : Nat} (retained : old ≤ fresh)

theorem restrict_extend (value : FieldSpace depth old) :
    restrict depth retained (extend depth retained value) = value := by
  apply (Actor.currentPullback depth old).injective
  rw [restrict_samples, extend_samples, SourceHistoryGrowth.restrict_extend]

theorem extend_norm (value : FieldSpace depth old) :
    ‖extend depth retained value‖ = Real.sqrt (SourceHistoryGrowth.fraction old fresh) * ‖value‖ := by
  rw [← (Actor.currentPullback depth fresh).norm_map, extend_samples, SourceHistoryGrowth.extend_norm,
    (Actor.currentPullback depth old).norm_map]

theorem remainder_eq (value : FieldSpace depth fresh) :
    remainder depth retained value = value - extend depth retained (restrict depth retained value) := by
  apply (Actor.currentPullback depth fresh).injective
  rw [remainder_samples, map_sub, extend_samples, restrict_samples, SourceHistoryGrowth.remainder_eq]

theorem energy_decomposition (value : FieldSpace depth fresh) :
    ‖value‖ ^ 2 = SourceHistoryGrowth.fraction old fresh * ‖restrict depth retained value‖ ^ 2 +
      ‖remainder depth retained value‖ ^ 2 := by
  have original := SourceHistoryGrowth.energy_decomposition retained (Actor.currentPullback depth fresh value)
  rw [(Actor.currentPullback depth fresh).norm_map, ← restrict_samples depth retained,
    (Actor.currentPullback depth old).norm_map, ← remainder_samples depth retained,
    (Actor.currentPullback depth fresh).norm_map] at original
  exact original

theorem restriction_bound (value : FieldSpace depth fresh) :
    ‖restrict depth retained value‖ ≤ (Real.sqrt (SourceHistoryGrowth.fraction old fresh))⁻¹ * ‖value‖ := by
  have original := SourceHistoryGrowth.restriction_bound retained (Actor.currentPullback depth fresh value)
  rw [← restrict_samples depth retained, (Actor.currentPullback depth old).norm_map,
    (Actor.currentPullback depth fresh).norm_map] at original
  exact original

theorem restriction_norm :
    ‖restrict depth retained‖ = (Real.sqrt (SourceHistoryGrowth.fraction old fresh))⁻¹ := by
  apply le_antisymm
  · exact (restrict depth retained).opNorm_le_bound (by positivity) (restriction_bound depth retained)
  · let witness : FieldSpace depth old := Actor.currentTransfer depth old (cotest (historyPMF old) 0)
    have positive : 0 < ‖witness‖ := by
      rw [actor_transfer_norm, cotest_norm]
      exact Real.sqrt_pos.mpr (mass_positive _ _ (SourceUniformFibreVariance.source_positive old 0))
    have actual := (restrict depth retained).le_opNorm (extend depth retained witness)
    rw [restrict_extend, extend_norm] at actual
    have scaled : 1 * ‖witness‖ ≤
        (‖restrict depth retained‖ * Real.sqrt (SourceHistoryGrowth.fraction old fresh)) * ‖witness‖ := by
      simpa only [one_mul, mul_assoc] using actual
    have cancel := (mul_le_mul_iff_of_pos_right positive).mp scaled
    rw [← one_div]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (SourceHistoryGrowth.fraction_pos old fresh))).mpr cancel

theorem original_read_retained (index : Fin (old + 1)) :
    Actor.originalRead depth fresh (SourceHistoryGrowth.includeActor retained index) =
      Actor.originalRead depth old index := by
  rw [Actor.originalRead_actual, Actor.originalRead_actual]
  rfl

theorem query_retained (value : FieldSpace depth fresh) (index : Fin (old + 1)) :
    Recorded.query depth old index (restrict depth retained value) =
      Recorded.query depth fresh (SourceHistoryGrowth.includeActor retained index) value := by
  have actual := congrArg (fun samples : SourceWeightedRecovery.Space (historyPMF old) => samples index)
    (restrict_samples depth retained value)
  rw [Actor.currentPullback_at, SourceHistoryGrowth.restrict_at, Actor.currentPullback_at] at actual
  simpa only [SourceGeneratedRecordFrame.query_sample] using actual

end
end SourceGeneratedAcquisitionMeasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
