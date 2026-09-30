import H0mework.Fock.SourceHistoryClock.DecoderFiniteComparison

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointFiniteDecoder

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedJointTime SourceGeneratedJointClockGraph
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

/-- Keep image laws symbolic when specializing them to a generated inventory. -/
def ImageLaws (depth bound fresh : Nat) (prior : bound ≤ fresh) : Prop :=
    (∀ target proposal : SourceJointClockGraph.Carrier,
      type_of% (SourceJointClockDecoder.error_decomposition target proposal) ∧
      type_of% (SourceJointClockDecoder.unique_minimum target proposal)) ∧
    (∀ target : SourceJointClockGraph.Carrier,
      type_of% (SourceJointFiniteDecoder.source_minimum bound target) ∧
      type_of% (source_minimum depth bound target) ∧
      type_of% (SourceJointFiniteDecoder.retained_full_residual bound target) ∧
      type_of% (SourceJointFiniteDecoder.residual_monotone prior target)) ∧
    (∀ target : SourceJointClockGraph.Carrier, ∀ proposal : FieldSpace depth bound,
      type_of% (error_decomposition depth bound target proposal) ∧ type_of% (minimum_fibre depth bound target proposal)) ∧
    (∀ value : SourceJointFiniteDecoder.Space bound,
      type_of% (SourceJointFiniteDecoder.source_energy bound value) ∧
      type_of% (SourceJointFiniteDecoder.decode_action bound value) ∧
      type_of% (SourceJointFiniteDecoder.action_normalized prior value)) ∧
    type_of% (SourceJointFiniteDecoder.source_closed_range bound) ∧
    (∀ value : NextSpace depth bound, type_of% (original_K depth bound value) ∧
      type_of% (next_residual_zero depth bound value)) ∧
    (∀ index : Fin (bound + 1), ∀ proposal : SourceJointClockGraph.Carrier,
      type_of% (SourceJointClockDecoder.native_next_minimum (runtimeAt index.val) proposal)) ∧
    type_of% SourceJointClockDecoder.root_recovery_not_finite ∧
    type_of% (SourceJointFiniteDecoder.finite_root_cost bound)

theorem image_laws (depth bound fresh : Nat) (prior : bound ≤ fresh) : ImageLaws depth bound fresh prior := by
  dsimp only [ImageLaws]
  exact ⟨(fun target proposal => ⟨SourceJointClockDecoder.error_decomposition target proposal,
      SourceJointClockDecoder.unique_minimum target proposal⟩),
    (fun target => ⟨SourceJointFiniteDecoder.source_minimum bound target, source_minimum depth bound target,
      SourceJointFiniteDecoder.retained_full_residual bound target,
      SourceJointFiniteDecoder.residual_monotone prior target⟩),
    (fun target proposal => ⟨error_decomposition depth bound target proposal, minimum_fibre depth bound target proposal⟩),
    (fun value => ⟨SourceJointFiniteDecoder.source_energy bound value, SourceJointFiniteDecoder.decode_action bound value,
      SourceJointFiniteDecoder.action_normalized prior value⟩),
    SourceJointFiniteDecoder.source_closed_range bound,
    (fun value => ⟨original_K depth bound value, next_residual_zero depth bound value⟩),
    (fun index proposal => SourceJointClockDecoder.native_next_minimum (runtimeAt index.val) proposal),
    SourceJointClockDecoder.root_recovery_not_finite, SourceJointFiniteDecoder.finite_root_cost bound⟩

def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    ImageLaws (SourceGeneratedAcquisitionJoint.depth runtime) (inventoryBound runtime)
      (inventoryBound (next runtime)) (retained runtime) ∧
    type_of% (SourceJointClockDecoder.native_next_cost runtime) ∧
    (∀ sourceWord : Nat →₀ ℂ, type_of% (SourceJointClockDecoder.finite_root_cost_strict sourceWord) ∧
      type_of% (source_round_after round sourceWord) ∧
      type_of% (coversAt_factorizes (sourceRound round sourceWord) .particleWave) ∧
      type_of% (coversAt_factorizes (sourceRound round sourceWord).tick.next .particleWave)) ∧
    type_of% (SourceGeneratedJointClockGraph.sourceGeneratedJointClockGraphRecovery round) ∧
    type_of% (runtime_eq runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave)

theorem sourceGeneratedJointFiniteDecoderRecovery (round : Nat) : RecoveryAt round := by
  let runtime := roundRuntime round
  dsimp only [RecoveryAt]
  exact ⟨image_laws (SourceGeneratedAcquisitionJoint.depth runtime) (inventoryBound runtime)
      (inventoryBound (next runtime)) (retained runtime),
    SourceJointClockDecoder.native_next_cost runtime,
    (fun sourceWord => ⟨SourceJointClockDecoder.finite_root_cost_strict sourceWord, source_round_after round sourceWord,
      coversAt_factorizes (sourceRound round sourceWord) .particleWave,
      coversAt_factorizes (sourceRound round sourceWord).tick.next .particleWave⟩),
    SourceGeneratedJointClockGraph.sourceGeneratedJointClockGraphRecovery round,
    runtime_eq runtime, coversAt_factorizes runtime .particleWave, coversAt_factorizes (next runtime) .particleWave⟩

end
end SourceGeneratedJointFiniteDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
