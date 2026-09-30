import H0mework.Fock.PrimeFieldJoint.BornDynamics

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedBornDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def BornLaws (runtime : LivingRuntimeState process) (oldDepth freshDepth : Nat) : Prop :=
    type_of% (target_source runtime freshDepth) ∧ type_of% (target_coordinate runtime freshDepth) ∧
    (∀ proposal : SourceJointFiniteDecoder.Space (inventoryBound runtime),
      type_of% (prior_loss runtime freshDepth proposal) ∧ type_of% (unit_prior_loss runtime freshDepth proposal)) ∧
    (∀ proposal : FieldSpace oldDepth (inventoryBound runtime), type_of% (original_prior_loss runtime oldDepth freshDepth proposal)) ∧
    type_of% (prior_residual_lower runtime freshDepth) ∧ type_of% (prior_residual_ne_zero runtime freshDepth) ∧
    type_of% (fresh_decode runtime freshDepth) ∧ type_of% (fresh_samples runtime freshDepth) ∧
    type_of% (fresh_residual_zero runtime freshDepth) ∧ type_of% (fresh_next_actual runtime freshDepth) ∧
    type_of% (target_actual_read runtime freshDepth) ∧
    type_of% (unit_newest_norm runtime freshDepth) ∧ type_of% (unit_coordinate runtime freshDepth) ∧
    type_of% (unit_prior_residual runtime freshDepth) ∧ type_of% (unit_fresh_decode runtime freshDepth) ∧
    type_of% (unit_fresh_residual runtime freshDepth) ∧ type_of% (actual_cost_drop runtime freshDepth) ∧
    type_of% (newest_actual_read runtime freshDepth) ∧ type_of% (newest_norm runtime freshDepth) ∧
    type_of% (newest_lost_from_prior runtime freshDepth) ∧ type_of% (newest_in_remainder runtime freshDepth) ∧
    type_of% (complete_energy runtime freshDepth (newest runtime freshDepth))

theorem born_laws (runtime : LivingRuntimeState process) (oldDepth freshDepth : Nat) : BornLaws runtime oldDepth freshDepth := by
  dsimp only [BornLaws]
  exact ⟨target_source runtime freshDepth, target_coordinate runtime freshDepth,
    (fun proposal => ⟨prior_loss runtime freshDepth proposal, unit_prior_loss runtime freshDepth proposal⟩),
    original_prior_loss runtime oldDepth freshDepth,
    prior_residual_lower runtime freshDepth, prior_residual_ne_zero runtime freshDepth,
    fresh_decode runtime freshDepth, fresh_samples runtime freshDepth, fresh_residual_zero runtime freshDepth,
    fresh_next_actual runtime freshDepth, target_actual_read runtime freshDepth,
    unit_newest_norm runtime freshDepth, unit_coordinate runtime freshDepth,
    unit_prior_residual runtime freshDepth, unit_fresh_decode runtime freshDepth, unit_fresh_residual runtime freshDepth,
    actual_cost_drop runtime freshDepth, newest_actual_read runtime freshDepth, newest_norm runtime freshDepth,
    newest_lost_from_prior runtime freshDepth, newest_in_remainder runtime freshDepth,
    complete_energy runtime freshDepth (newest runtime freshDepth)⟩

def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    BornLaws runtime (depth runtime) (depth (next runtime)) ∧
    type_of% (moving_cost_ge_one round) ∧ type_of% moving_cost_not_tendsto_zero ∧
    type_of% (acquired_cost_zero round) ∧
    type_of% (SourceGeneratedJointDecoderCofinal.sourceGeneratedJointDecoderCofinalRecovery round) ∧
    type_of% (runtime_eq runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime).tick.next .particleWave)

theorem sourceGeneratedBornDecoderRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨born_laws (roundRuntime round) (depth (roundRuntime round)) (depth (next (roundRuntime round))),
    moving_cost_ge_one round, moving_cost_not_tendsto_zero, acquired_cost_zero round,
    SourceGeneratedJointDecoderCofinal.sourceGeneratedJointDecoderCofinalRecovery round,
    runtime_eq (roundRuntime round), coversAt_factorizes (roundRuntime round) .particleWave,
    coversAt_factorizes (next (roundRuntime round)) .particleWave,
    coversAt_factorizes (next (roundRuntime round)).tick.next .particleWave⟩

end
end SourceGeneratedBornDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
