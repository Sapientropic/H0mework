import H0mework.Versions.X.Fock.PrimeFieldCalculation.CalculationConditional

/-! The source-generated normal target and original conditional transfer consume the same action history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCalculation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

theorem source_calculation_consumed (bound : Nat) :
    let calculation := normal bound
    let target := calculation.targetRuntime
    (frontier bound).sourcePayload = runtimePayload 0 ∧
      (∀ stage : Fin ((frontier bound).stageCount + 1),
        (frontier bound).LocalOperationAt stage (frontier bound).sourcePayload ((frontier bound).history.stageAt stage)) ∧
      (∀ index actor : Fin (bound + 1), type_of% (recorded_coefficient_is_birth bound index actor)) ∧
      (∀ index candidate : Fin (bound + 1), type_of% (conditional_weight_is_birth bound index candidate)) ∧
      (∀ task : Fin (bound + 1) → ℂ, ∀ actor : Fin (bound + 1),
        type_of% (transfer_from_birth bound task actor) ∧ sourceAnswer bound task actor = task actor) ∧
      (∀ task : Fin (bound + 1) → ℂ, type_of% (residuals_zero sourceOwner bound task) ∧
        type_of% (original_actor_reconstructed sourceOwner bound task)) ∧
      recordedQuery bound (Fin.last bound) (Fin.last (windowBound sourceOwner bound)) = rawField target.state ∧
      type_of% (last_record_is_generated_birth bound) ∧
      type_of% calculation.target_factorizes ∧
      HEq (runtimeFacade.readoutAt target .particleWave)
        (target.tick.generated.projectionOutcome
          ((runtimeFacade.installationAt target .particleWave).embed
            (runtimeFacade.projectionAt target .particleWave))) ∧
      target.tick.next.current.visit.current = (runtimePayload (completionDepth sourceOwner bound + 1)).nativeWrite.target ∧
      type_of% (SourcePrimeHistoryRecovery.information_consumed bound) := by
  exact ⟨source_payload_is_original bound, (realization bound).operationAt,
    recorded_coefficient_is_birth bound, conditional_weight_is_birth bound,
    (fun task actor => ⟨transfer_from_birth bound task actor, source_answer_recovers bound task actor⟩),
    (fun task => ⟨residuals_zero sourceOwner bound task, original_actor_reconstructed sourceOwner bound task⟩),
    last_record_is_target bound, last_record_is_generated_birth bound, (normal bound).target_factorizes,
    (runtimeFacade.readoutAt_factorizes (normal bound).targetRuntime .particleWave).2.2.2.1,
    SourceOwnedObservationHistory.Installed.runtime_current_next (completionDepth sourceOwner bound + 1),
    SourcePrimeHistoryRecovery.information_consumed bound⟩

end
end SourcePrimeCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
