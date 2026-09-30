import H0mework.Fock.PrimeHistoryMeasure.Witness

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionMeasure

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

/-- Keep the dependent conclusion named so concrete seeds do not expand both history ledgers. -/
def RecoveryAt (runtime : LivingRuntimeState process) : Prop :=
    let old := inventoryBound runtime
    let fresh := inventoryBound (next runtime)
    let depth := completionDepth sourceOwner fresh + 2
    type_of% (inventory_grows runtime) ∧
    type_of% (prior_mass_original runtime) ∧ type_of% (prior_mass_pos_lt_one runtime) ∧
    type_of% (SourceHistoryGrowth.prior_mass (retained runtime)) ∧
    type_of% (SourceHistoryGrowth.prior_conditional_complete (retained runtime)) ∧
    (∀ value : FieldSpace depth old, type_of% (recover_preserve runtime depth value) ∧
      type_of% (extend_norm depth (retained runtime) value)) ∧
    type_of% (recovery_gain runtime depth) ∧ type_of% (recovery_gain_gt_one runtime depth) ∧
    (∀ value : FieldSpace depth fresh, type_of% (complete_energy runtime depth value) ∧
      type_of% (remainder_eq depth (retained runtime) value) ∧
      (∀ index : Fin (old + 1), type_of% (retained_query runtime depth value index))) ∧
    (∀ index : Fin (old + 1), type_of% (original_read_retained depth (retained runtime) index)) ∧
    type_of% (new_source_read runtime depth) ∧
    type_of% (newest_actual_read runtime depth) ∧ type_of% (newest_norm runtime depth) ∧
    type_of% (newest_lost_from_prior runtime depth) ∧ type_of% (newest_in_remainder runtime depth) ∧
    type_of% (no_prior_only_restore runtime depth) ∧
    type_of% (acquisition_consumed runtime) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave) ∧
    type_of% (acquisition_consumed (next runtime))

theorem sourceGeneratedAcquisitionMeasureRecovery (runtime : LivingRuntimeState process) : RecoveryAt runtime := by
  dsimp only [RecoveryAt]
  exact ⟨inventory_grows runtime, prior_mass_original runtime, prior_mass_pos_lt_one runtime,
    SourceHistoryGrowth.prior_mass (retained runtime), SourceHistoryGrowth.prior_conditional_complete (retained runtime),
    (fun value => ⟨recover_preserve runtime _ value, extend_norm _ (retained runtime) value⟩),
    recovery_gain runtime _, recovery_gain_gt_one runtime _,
    (fun value => ⟨complete_energy runtime _ value, remainder_eq _ (retained runtime) value,
      retained_query runtime _ value⟩), original_read_retained _ (retained runtime),
    new_source_read runtime _, newest_actual_read runtime _, newest_norm runtime _,
    newest_lost_from_prior runtime _, newest_in_remainder runtime _, no_prior_only_restore runtime _,
    acquisition_consumed runtime, coversAt_factorizes (next runtime) .particleWave,
    acquisition_consumed (next runtime)⟩

end
end SourceGeneratedAcquisitionMeasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
