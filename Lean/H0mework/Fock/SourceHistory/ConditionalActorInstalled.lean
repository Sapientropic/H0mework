import H0mework.Probability.EmpiricalRecovery.ActorConditional
import H0mework.Fock.SourceHistory.ConditionalRecovery

/-! The original field consumer receives its source actor projection together with the missing earlier residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.Installed

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B)

theorem runtime_actor_factorizes (bound : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field (process := process) read → ℂ) :
    let runtime := runtimeAt bound
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let value := taskValue (historyPMF bound) task
    rawError read runtimeSeed bound task decoder =
        ‖actorResidual read runtimeSeed bound value‖ ^ 2 +
          ‖SourceGeneratedEmpiricalHilbert.residual read runtimeSeed bound (actorTransfer read runtimeSeed bound value)‖ ^ 2 +
            SourceConditionalRecovery.decoderError read runtimeSeed bound
              (SourceGeneratedEmpiricalHilbert.transfer read runtimeSeed bound (actorTransfer read runtimeSeed bound value)) decoder ∧
      type_of% (rawError_lower_bound read runtimeSeed bound task decoder) ∧
      type_of% (rawError_attains read runtimeSeed bound task) ∧
      (∀ atom : Field (process := process) read, type_of% (completeTransfer_is_conditional read runtimeSeed bound task atom)) ∧
      type_of% (complete_residual_energy read runtimeSeed bound value) ∧
      type_of% (reconstruct_actor read runtimeSeed bound value) ∧
      (∀ index : Fin (bound + 1),
        let actor := (history runtimeSeed bound).stageAt index
        actor.next.current.visit.current = (runtimePayload index.val).nativeWrite.target ∧
          (process.toAnswerNextCausalWorld.emitted (ULift.up (sample runtimeSeed bound index)) =
              ULift.up actor.activated.generated ∧
            actor.activated.generated.occurrence =
              (runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
                (runtimeAt index.val).current.visit.current ∧
            HEq actor.wholeLedgerWriteBack
              ((runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
                (runtimeAt index.val).current.visit.current) ∧
            actor.next.current = actor.activated.nextCurrent)) ∧
      (runtimePayload bound).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive bound, runtimePayload bound⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) ∧
      stage.next.current.visit.current = (runtimePayload bound).nativeWrite.target := by
  rcases SourceConditionalRecovery.Installed.runtime_recovery_factorizes read bound
    (actorTransfer read runtimeSeed bound (taskValue (historyPMF bound) task)) decoder with
    ⟨fieldError, _lower, _attains, _model, _conditional, actors, _reconstructed,
      sourceOccurrence, face, installation, stageFacts, next⟩
  refine ⟨(rawError_before_field read runtimeSeed bound task decoder).trans
      ((congrArg (‖actorResidual read runtimeSeed bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·) fieldError).trans
        (add_assoc _ _ _).symm),
    rawError_lower_bound read runtimeSeed bound task decoder, rawError_attains read runtimeSeed bound task,
    completeTransfer_is_conditional read runtimeSeed bound task, complete_residual_energy read runtimeSeed bound _,
    reconstruct_actor read runtimeSeed bound _, ?_, sourceOccurrence, face, installation, stageFacts, next⟩
  intro index
  exact (actors index).2

end
end SourceWeightedRecovery.Runtime.Actor.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
