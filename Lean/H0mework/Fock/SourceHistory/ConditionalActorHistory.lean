import H0mework.Fock.SourceHistory.ActorRecoveryHistoryRegression
import H0mework.Fock.SourceHistory.ConditionalHistoryInstalled

/-! The old terminal-history consumer retains the initial actor residual and restores the complete source task. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Installed

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B)

theorem runtime_actor_history_factorizes (bound depth : Nat) (task : Fin (bound + 1) → ℂ)
    (decoder : Field (process := process) read → ℂ) :
    let runtime := runtimeAt (depth + bound)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let value := taskValue (historyPMF bound) task
    let retained := SourceGeneratedEmpiricalHilbert.retainedHistory read runtimeSeed bound (depth + 1)
      (actorTransfer read runtimeSeed bound value)
    rawTerminalError read runtimeSeed bound depth task decoder =
        ‖actorResidual read runtimeSeed bound value‖ ^ 2 +
          SourceGeneratedEmpiricalHilbert.inventoryEnergy read runtimeSeed bound (depth + 1) retained.2 +
            SourceConditionalRecovery.decoderError read (runtimeSeed.advance depth) bound retained.1 decoder ∧
      type_of% (complete_error_lower_bound read runtimeSeed bound depth task decoder) ∧
      type_of% (complete_error_attains read runtimeSeed bound depth task) ∧
      type_of% (complete_source_restored read runtimeSeed bound (depth + 1) value) ∧
      (∀ tick : Fin (depth + 1), ∀ index : Fin (bound + 1),
        type_of% (sample_factorizes (runtimeSeed.advance tick.val) bound index)) ∧
      fieldSample read (runtimeSeed.advance (depth + 1)) bound (Fin.last bound) = fieldPoint read stage.next.state ∧
      (runtimePayload (depth + bound)).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive (depth + bound), runtimePayload (depth + bound)⟩ ∧
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
      stage.next.current.visit.current = (runtimePayload (depth + bound)).nativeWrite.target := by
  rcases SourceConditionalRecovery.History.Installed.runtime_terminal_factorizes read bound depth
    (actorTransfer read runtimeSeed bound (taskValue (historyPMF bound) task)) decoder with
    ⟨fieldError, _lower, _attained, _conditional, _model, actors, fieldRestored, terminal,
      sourceOccurrence, face, installation, stageFacts, next⟩
  have restored := (congrArg (fun current => actorPullback read runtimeSeed bound current +
      actorResidual read runtimeSeed bound (taskValue (historyPMF bound) task)) fieldRestored).trans
    (IsometricRetainedTransfer.pullback_transfer_add_residual (actorPullback read runtimeSeed bound)
      (taskValue (historyPMF bound) task))
  exact ⟨(rawTerminalError_before_field read runtimeSeed bound depth task decoder).trans
      ((congrArg (‖actorResidual read runtimeSeed bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·) fieldError).trans
        (add_assoc _ _ _).symm),
    complete_error_lower_bound read runtimeSeed bound depth task decoder,
    complete_error_attains read runtimeSeed bound depth task, restored, actors,
    terminal, sourceOccurrence, face, installation, stageFacts, next⟩

end
end SourceWeightedRecovery.Runtime.Actor.History.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
