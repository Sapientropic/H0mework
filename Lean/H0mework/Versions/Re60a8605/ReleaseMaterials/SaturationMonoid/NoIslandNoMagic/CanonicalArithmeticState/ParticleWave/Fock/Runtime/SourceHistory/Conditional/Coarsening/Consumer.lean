import H0mework.Fock.ClockCoarsening.Runtime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Regression.SourceHistory.ConditionalCoarsening

/-! The original canonical root consumes the generated mixture, both clock residuals and its literal next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePulseCoarsening

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert.Controls
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceConditionalTransfer SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem information_factorizes (bound : Nat) (decoder : Field (process := process) pulse → ℂ) :
    let runtime := runtimeAt bound
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let value := taskValue (historyPMF bound) (clockTask bound)
    type_of% (generatedMixture_is_full bound) ∧ type_of% (mixture_actual_next bound) ∧
      type_of% forget_not_injective ∧
      type_of% (actor_cost bound) ∧ type_of% (field_cost bound) ∧
      type_of% (next_field_error bound decoder) ∧ type_of% (clock_coarsening_loss bound) ∧
      type_of% (positive_coarsening_loss bound) ∧ type_of% singleton_no_loss ∧
      Runtime.Actor.rawError pulse runtimeSeed bound (clockTask bound) decoder =
        (bound : ℝ) * (bound - 1) / 12 + (bound : ℝ) / 4 +
          SourceConditionalRecovery.decoderError pulse runtimeSeed bound
            (SourceGeneratedEmpiricalHilbert.transfer pulse runtimeSeed bound
              (Runtime.Actor.actorTransfer pulse runtimeSeed bound value)) decoder ∧
      type_of% (Runtime.Actor.reconstruct_actor pulse runtimeSeed bound value) ∧
      (∀ index : Fin (bound + 1), type_of% (sample_factorizes runtimeSeed bound index)) ∧
      ((history runtimeSeed bound).stageAt (Fin.last bound)).next = stage.next ∧
      (runtimePayload bound).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive bound, runtimePayload bound⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload bound).nativeWrite.target := by
  rcases Runtime.Actor.Installed.runtime_actor_factorizes pulse bound (clockTask bound) decoder with
    ⟨error, _lower, _attains, _conditional, _energy, restored, actors,
      sourceOccurrence, face, installation, stageFacts, next⟩
  rw [actor_cost, field_cost] at error
  exact ⟨generatedMixture_is_full bound, mixture_actual_next bound, forget_not_injective,
    actor_cost bound, field_cost bound, next_field_error bound decoder, clock_coarsening_loss bound,
    positive_coarsening_loss bound, singleton_no_loss, error, restored,
    fun index => (actors index).2, rfl, sourceOccurrence, face, installation,
    stageFacts.2.2.1, stageFacts.2.2.2, next⟩

end
end SourcePulseCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
