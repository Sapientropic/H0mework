import H0mework.Fock.PrimeFieldJoint.CofinalOriginal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointDecoderCofinal

open SourceJointDecoderCofinal SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedAcquisitionMeasure
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    type_of% (whole_image round) ∧
    (∀ target : SourceJointClockGraph.Carrier, type_of% (original_tendsto round target) ∧
      type_of% (estimate_tendsto round target) ∧ type_of% (residual_tendsto round target) ∧
      type_of% (cost_tendsto round target)) ∧
    (∀ sourceWord : Nat →₀ ℂ, ∀ future : Nat, ∀ reached : demand round sourceWord ≤ future,
      type_of% (source_exact round sourceWord future reached) ∧
      type_of% (source_word_exact round sourceWord future reached) ∧
      type_of% (original_word_exact round sourceWord future reached) ∧
      type_of% (source_residual_zero round sourceWord future reached) ∧
      type_of% (coversAt_factorizes (roundRuntime (round + future)) .particleWave) ∧
      type_of% (coversAt_factorizes (roundRuntime (round + future)).tick.next .particleWave)) ∧
    (∀ sourceWord : Nat →₀ ℂ, type_of% (source_round_after round sourceWord)) ∧
    type_of% (root_cost_tendsto round) ∧
    (∀ future : Nat, type_of% (SourceJointFiniteDecoder.finite_root_cost (inventoryBound (roundRuntime (round + future))))) ∧
    type_of% SourceJointClockDecoder.root_recovery_not_finite ∧
    type_of% (SourceGeneratedJointFiniteDecoder.sourceGeneratedJointFiniteDecoderRecovery round) ∧
    type_of% (runtime_eq runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave)

theorem sourceGeneratedJointDecoderCofinalRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨whole_image round,
    (fun target => ⟨original_tendsto round target, estimate_tendsto round target,
      residual_tendsto round target, cost_tendsto round target⟩),
    (fun sourceWord future reached => ⟨source_exact round sourceWord future reached,
      source_word_exact round sourceWord future reached, original_word_exact round sourceWord future reached,
      source_residual_zero round sourceWord future reached,
      coversAt_factorizes (roundRuntime (round + future)) .particleWave,
      coversAt_factorizes (roundRuntime (round + future)).tick.next .particleWave⟩),
    source_round_after round, root_cost_tendsto round,
    (fun future => SourceJointFiniteDecoder.finite_root_cost (inventoryBound (roundRuntime (round + future)))),
    SourceJointClockDecoder.root_recovery_not_finite,
    SourceGeneratedJointFiniteDecoder.sourceGeneratedJointFiniteDecoderRecovery round,
    runtime_eq (roundRuntime round), coversAt_factorizes (roundRuntime round) .particleWave,
    coversAt_factorizes (next (roundRuntime round)) .particleWave⟩

end
end SourceGeneratedJointDecoderCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
