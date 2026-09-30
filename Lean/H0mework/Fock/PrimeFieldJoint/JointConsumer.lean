import H0mework.Fock.PrimeFieldJoint.JointCofinal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedAcquisitionJoint

open SourceOwnedObservationHistory SourceGeneratedAcquisitionMeasure
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory.SourceShift
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

/-- Keep the complete dependent result named when specializing the original runtime seed. -/
def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    type_of% (whole_joint_closure round) ∧
    type_of% packet_tendsto ∧ type_of% hilbert_density_tendsto ∧
    type_of% (packet_update runtime) ∧ type_of% (packet_mass runtime) ∧ type_of% (added_mass runtime) ∧
    type_of% (added_ne_zero runtime) ∧
    (∀ value : FieldSpace (depth runtime) (inventoryBound runtime),
      type_of% (normalized_packet runtime value) ∧ type_of% (normalized_norm runtime value) ∧
      type_of% (first_joint (depth runtime) (inventoryBound runtime) value) ∧
      type_of% (mass_joint (depth runtime) (inventoryBound runtime) value) ∧
      type_of% (joint_norm_sq (depth runtime) (inventoryBound runtime) value)) ∧
    (∀ index : Fin (inventoryBound runtime + 1), type_of% (density_query runtime index) ∧
      type_of% (added_query_prior runtime index)) ∧
    (∀ index : Fin (inventoryBound (next runtime) + 1),
      type_of% (added_query runtime index) ∧
      (∀ new : inventoryBound runtime + 1 ≤ index.val, type_of% (added_query_new runtime index new))) ∧
    (∀ sourceWord : Nat →₀ ℂ,
      type_of% (realization_word round sourceWord) ∧ type_of% (realization_joint round sourceWord) ∧
      type_of% (source_round_after round sourceWord) ∧
      (∀ present : sourceWord.support.sup id ≤ inventoryBound runtime,
        type_of% (source_round_current round sourceWord present)) ∧
      type_of% (runtime_eq (sourceRound round sourceWord)) ∧
      type_of% (sourceGeneratedAcquisitionMeasureRecovery (sourceRound round sourceWord)) ∧
      type_of% (coversAt_factorizes (sourceRound round sourceWord) .particleWave)) ∧
    type_of% SourceMassCompletion.generated_limit_mass ∧
    type_of% SourceMassCompletion.generated_limit_ne_zero ∧
    type_of% SourceMassCompletion.generated_limit_fixed ∧
    type_of% (runtime_eq runtime) ∧
    type_of% (SourceMassCompletion.runtime_joint_completion_factorizes runtime.state (sourcePoint runtime.state)
      (packet runtime) (WithLp.toLp 2 ((0 : H), (1 : ℂ)))) ∧
    type_of% (sourceGeneratedAcquisitionMeasureRecovery runtime) ∧
    type_of% (coversAt_factorizes runtime .particleWave)

theorem sourceGeneratedAcquisitionJointRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨whole_joint_closure round, packet_tendsto, hilbert_density_tendsto,
    packet_update _, packet_mass _, added_mass _, added_ne_zero _,
    (fun value => ⟨normalized_packet _ value, normalized_norm _ value, first_joint _ _ value,
      mass_joint _ _ value, joint_norm_sq _ _ value⟩),
    (fun index => ⟨density_query _ index, added_query_prior _ index⟩),
    (fun index => ⟨added_query _ index, added_query_new _ index⟩),
    (fun sourceWord => ⟨realization_word round sourceWord, realization_joint round sourceWord,
      source_round_after round sourceWord, source_round_current round sourceWord,
      runtime_eq _, sourceGeneratedAcquisitionMeasureRecovery _, coversAt_factorizes _ .particleWave⟩),
    SourceMassCompletion.generated_limit_mass, SourceMassCompletion.generated_limit_ne_zero,
    SourceMassCompletion.generated_limit_fixed, runtime_eq _,
    SourceMassCompletion.runtime_joint_completion_factorizes _ _ _ _,
    sourceGeneratedAcquisitionMeasureRecovery _, coversAt_factorizes _ .particleWave⟩

end
end SourceGeneratedAcquisitionJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
