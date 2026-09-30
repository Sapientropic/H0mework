import H0mework.Fock.PrimeFieldJoint.ClockGraphField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointClockGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint
open SourceGeneratedJointTime SourceJointClockGraph
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def RecoveryAt (round : Nat) : Prop :=
    let runtime := roundRuntime round
    let bound := inventoryBound runtime
    let depth := SourceGeneratedAcquisitionJoint.depth runtime
    type_of% (whole_graph_closure round) ∧
    (∀ value : SourceJointClockGraph.Carrier, type_of% (recover_action value) ∧
      type_of% (reconstruction value) ∧ type_of% (residual_formula value) ∧
      type_of% (action_energy value) ∧ type_of% (retained_energy value) ∧ type_of% (action_range value)) ∧
    type_of% clock_unit_mem_closure ∧ type_of% clock_unit_not_finite ∧
    type_of% root_unit_recovery ∧ type_of% root_unit_not_in_range ∧ type_of% root_unit_energy_gain ∧
    type_of% action_not_norm_preserving ∧
    (∀ value : FieldSpace depth bound, type_of% (original_time_square depth bound value) ∧
      type_of% (original_field_norm depth bound value)) ∧
    (∀ value : NextSpace depth bound, type_of% (original_time_recovery depth bound value) ∧
      type_of% (next_residual_zero depth bound value)) ∧
    (∀ sourceWord : Nat →₀ ℂ, type_of% (realization_graph round sourceWord) ∧
      type_of% (source_round_after round sourceWord) ∧
      type_of% (native_next (sourceRound round sourceWord)) ∧
      type_of% (coversAt_factorizes (sourceRound round sourceWord) .particleWave) ∧
      type_of% (coversAt_factorizes (sourceRound round sourceWord).tick.next .particleWave)) ∧
    (∀ sourceWord : Nat →₀ ℤ, type_of% (native_realization_graph round sourceWord)) ∧
    (∀ index : Fin (bound + 1), type_of% (native_next (runtimeAt index.val))) ∧
    type_of% (native_next runtime) ∧
    type_of% (SourceGeneratedJointClock.sourceGeneratedJointClockRecovery round) ∧
    type_of% (runtime_eq runtime) ∧ type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes (next runtime) .particleWave)

theorem sourceGeneratedJointClockGraphRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨whole_graph_closure round,
    (fun value => ⟨recover_action value, reconstruction value, residual_formula value,
      action_energy value, retained_energy value, action_range value⟩),
    clock_unit_mem_closure, clock_unit_not_finite, root_unit_recovery, root_unit_not_in_range,
    root_unit_energy_gain, action_not_norm_preserving,
    (fun value => ⟨original_time_square _ _ value, original_field_norm _ _ value⟩),
    (fun value => ⟨original_time_recovery _ _ value, next_residual_zero _ _ value⟩),
    (fun sourceWord => ⟨realization_graph round sourceWord, source_round_after _ _,
      native_next _, coversAt_factorizes _ .particleWave, coversAt_factorizes _ .particleWave⟩),
    native_realization_graph round, (fun index => native_next (runtimeAt index.val)), native_next _,
    SourceGeneratedJointClock.sourceGeneratedJointClockRecovery round,
    runtime_eq _, coversAt_factorizes _ .particleWave, coversAt_factorizes _ .particleWave⟩

end
end SourceGeneratedJointClockGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
