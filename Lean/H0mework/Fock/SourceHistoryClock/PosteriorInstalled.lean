import H0mework.Fock.SourceHistory.ClockPosteriorRegression
import H0mework.Fock.SourceHistoryClock.RecoveryInstalled

/-! The original next frame supplies complete posterior recovery and the exact original dependent material. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Clock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem runtime_posterior_factorizes (bound depth : Nat) (signal : Fin (bound + 1) → ℂ) :
    let runtime := runtimeAt (depth + bound)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    (∀ index : Fin (bound + 1), posterior bound depth index = PMF.pure index) ∧
      (∀ index : Fin (bound + 1),
        optimalDecoder (historyPMF bound) (observe bound depth) signal (observe bound depth index) = signal index) ∧
      error (historyPMF bound) (observe bound depth) signal (optimalDecoder (historyPMF bound) (observe bound depth) signal) = 0 ∧
      residual (historyPMF bound) (observe bound depth) (taskValue (historyPMF bound) signal) = 0 ∧
      (∀ index candidate : Fin (bound + 1), candidate ∈ (posterior bound depth index).support →
        HEq ((history runtimeSeed bound).stageAt candidate) ((history runtimeSeed bound).stageAt index)) ∧
      observe bound depth (Fin.last bound) = SourceClockFrame.coordinates 0
        (SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock stage.next) ∧
      (∀ index : Fin (bound + 1), type_of% (sample_factorizes runtimeSeed bound index) ∧
        type_of% (sample_factorizes (runtimeSeed.advance depth) bound index)) ∧
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
  rcases SourceWeightedRecovery.Runtime.Actor.History.Installed.clock_recovery_factorizes bound depth with
    ⟨_clock, _cost, actualModel, _point, _effect, _frame, actors,
      sourceOccurrence, face, installation, stageFacts, next⟩
  exact ⟨posterior_is_original bound depth, optimum_recovers bound depth signal,
    optimum_cost_zero bound depth signal, source_residual_zero bound depth signal, posterior_same_material bound depth,
    congrArg (SourceClockFrame.coordinates 0) actualModel, actors,
    sourceOccurrence, face, installation, stageFacts, next⟩

end
end SourceWeightedRecovery.Runtime.Actor.History.Clock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
