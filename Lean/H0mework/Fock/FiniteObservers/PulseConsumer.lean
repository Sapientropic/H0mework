import H0mework.Fock.FiniteObservers.Pulse

/-! The original pulse consumer receives the finite conditional decoder without losing either source residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservation.Pulse

open SourceGeneratedActionObservationHistory SourceWeightedRecovery
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem runtime_pulse_information (decoder : (Fin 1 → ZMod 2) → ℂ) :
    let runtime := runtimeAt 2
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    type_of% (finite_clock_error decoder) ∧ type_of% finite_mean_attains ∧ type_of% finite_mean_one ∧
      (∀ index : Fin 3, type_of% (FiniteRecurrence.Native.conditional_is_original pulse 0 runtimeSeed 2
        (fun _ => 0) pulse_source_law index)) ∧
      (∀ index : Fin 3, type_of% (FiniteRecurrence.Native.completeTransfer_finite pulse 0 runtimeSeed 2
        (fun _ => 0) pulse_source_law Runtime.Actor.Pulse.clockTask index)) ∧
      type_of% Runtime.Actor.Pulse.actor_loss_sixth ∧ type_of% Runtime.Actor.Pulse.field_loss_half ∧
      type_of% (Runtime.Actor.reconstruct_actor pulse runtimeSeed 2 (taskValue (historyPMF 2) Runtime.Actor.Pulse.clockTask)) ∧
      (∀ index : Fin 3, type_of% (sample_factorizes runtimeSeed 2 index)) ∧
      observe (Fin.last 2) 0 = pulse stage.next.state ∧
      (runtimePayload 2).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive 2, runtimePayload 2⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload 2).nativeWrite.target := by
  rcases Runtime.Actor.Installed.clock_actor_information
    (fun atom => decoder (FiniteRecurrence.Native.fieldRead pulse 0 atom)) with
    ⟨_oldError, _lower, _attained, actorLoss, fieldLoss, _lostTask, restored, actors,
      sourceOccurrence, face, ledger, nextCurrent, target⟩
  have installed := coversAt_factorizes (runtimeAt 2) .particleWave
  exact ⟨finite_clock_error decoder, finite_mean_attains, finite_mean_one,
    FiniteRecurrence.Native.conditional_is_original pulse 0 runtimeSeed 2 (fun _ => 0) pulse_source_law,
    FiniteRecurrence.Native.completeTransfer_finite pulse 0 runtimeSeed 2 (fun _ => 0) pulse_source_law Runtime.Actor.Pulse.clockTask,
    actorLoss, fieldLoss, restored, actors, rfl, sourceOccurrence, face, installed.2.2.2.1,
    ledger, nextCurrent, target⟩

end
end SourceFiniteObservation.Pulse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
