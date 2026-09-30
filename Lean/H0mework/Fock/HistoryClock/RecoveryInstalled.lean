import H0mework.Fock.SourceHistory.ConditionalActorInstalled
import H0mework.Fock.SourceHistory.ActorRecoveryTerminalRegression

/-! The actual clock task returns both source losses and complete reconstruction to its original occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.Installed

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedEmpiricalHilbert.Controls SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem clock_actor_information (decoder : Field (process := process) pulse → ℂ) :
    let runtime := runtimeAt 2
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    type_of% (Pulse.exact_clock_error decoder) ∧
      type_of% (Pulse.any_clock_decoder decoder) ∧
      type_of% Pulse.constant_one_attains ∧ type_of% Pulse.actor_loss_sixth ∧ type_of% Pulse.field_loss_half ∧
      type_of% Pulse.clock_not_field_task ∧
      type_of% (reconstruct_actor pulse runtimeSeed 2 (taskValue (historyPMF 2) Pulse.clockTask)) ∧
      (∀ index : Fin 3, type_of% (sample_factorizes runtimeSeed 2 index)) ∧
      (runtimePayload 2).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive 2, runtimePayload 2⟩ ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload 2).nativeWrite.target := by
  rcases runtime_actor_factorizes pulse 2 Pulse.clockTask decoder with
    ⟨_error, _lower, _attained, _conditional, _energy, restored, actors,
      sourceOccurrence, face, _installation, stageFacts, next⟩
  exact ⟨Pulse.exact_clock_error decoder, Pulse.any_clock_decoder decoder,
    Pulse.constant_one_attains, Pulse.actor_loss_sixth, Pulse.field_loss_half, Pulse.clock_not_field_task,
    restored, fun index => (actors index).2, sourceOccurrence, face, stageFacts.2.2.1, stageFacts.2.2.2, next⟩

end
end SourceWeightedRecovery.Runtime.Actor.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
