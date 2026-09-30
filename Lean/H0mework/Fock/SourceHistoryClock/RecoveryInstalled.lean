import H0mework.Fock.SourceHistory.ConditionalActorHistory
import H0mework.Fock.SourceHistoryClock.FrameInstalled

/-! Actual clock recovery consumes the old source frame and the literal terminal clock occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Installed

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedEmpiricalHilbert.Controls SourceGeneratedScalarCofinalTopology.NativeProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem clock_recovery_factorizes (bound depth : Nat) :
    let runtime := runtimeAt (depth + bound)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    (∀ index : Fin (bound + 1), Clock.decode depth (Clock.observe bound depth index) = Clock.task bound index) ∧
      error (historyPMF bound) (Clock.observe bound depth) (Clock.task bound) (Clock.decode depth) = 0 ∧
      Clock.futureModel bound depth (Fin.last bound) =
        SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock stage.next ∧
      SourceClockFrame.frame 0 (SourceClockModel.Fock.point 0) = (1, 0) ∧
      SourceClockFrame.frame 0 (SourceClockFrame.effect 0) = (0, 1) ∧
      (SourceClockFrame.frame 0).symm (SourceClockFrame.frame 0 (Clock.futureModel bound depth (Fin.last bound))) =
        Clock.futureModel bound depth (Fin.last bound) ∧
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
  rcases SourceClockFrame.runtime_frame_factorizes 0 (Clock.futureModel bound depth (Fin.last bound)) with
    ⟨pointFrame, effectFrame, frameRestored, _action, _inverse, _reverse, _effect, _native, _clock,
      _hidden, _notNative, _actors, _sourceOccurrence, _face, _installation, _stageFacts, _next⟩
  rcases SourceClockModel.Fock.runtime_clock_model_factorizes (depth + bound)
    (SourceClockModel.Fock.point (depth + bound)) (Clock.futureModel bound depth (Fin.last bound)) with
    ⟨native, _clockRead, _targetRead, _increment, _mass, _nextMass, _fibre, _actors,
      sourceOccurrence, face, installation, stageFacts, next⟩
  have actual := (Clock.futureModel_source bound depth (Fin.last bound)).trans
    ((congrArg SourceClockModel.Fock.point (by omega : bound + (depth + 1) = depth + bound + 1)).trans
      (SourceClockModel.Fock.point_next (depth + bound)).symm)
  exact ⟨Clock.recovers_actor bound depth, Clock.exact_recovery_cost bound depth, actual.trans native,
    pointFrame, effectFrame, frameRestored,
    fun index => ⟨sample_factorizes runtimeSeed bound index, sample_factorizes (runtimeSeed.advance depth) bound index⟩,
    sourceOccurrence, face, installation, stageFacts, next⟩

end
end SourceWeightedRecovery.Runtime.Actor.History.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
