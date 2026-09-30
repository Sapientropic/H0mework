import H0mework.Versions.X.Fock.SourceHistoryClock.Fock

/-! The original one-clock model consumes its generated mass and the existing native occurrence factorization. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockModel.Fock

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOwnedObservationHistory.Installed

noncomputable section

theorem runtime_clock_model_factorizes (depth : Nat) (left right : Model) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    action (point depth) = SourceOperationNative.Observed.modelPoint (process := process) rawClock stage.next ∧
      clockRead (action (point depth)) = rawClock stage.next.state ∧
      clockRead (action (point depth)) = (scanIndex (runtimePayload depth).nativeWrite.target : ℤ) ∧
      clockRead (action (point depth)) = clockRead (point depth) + massRead (point depth) ∧
      massRead (point depth) = 1 ∧
      massRead (action (point depth)) = 1 ∧
      (left = right ↔ massRead left = massRead right ∧ clockRead left = clockRead right) ∧
      (∀ index : Fin (SourceOwnedObservationHistory.NativeWindow.bound runtime.current.visit.current + 1),
        SourceOwnedObservationHistory.NativeWindow.point runtime.current.visit.current index =
          (runtimeAt index.val).current.visit.current ∧
          SourceOwnedObservationHistory.NativeWindow.imagePoint runtime.current.visit.current index =
            ((materialHistory depth).stageAt index).next.current.visit.current ∧
          clockRead (point index.val) = (scanIndex (runtimeAt index.val).current.visit.current : ℤ)) ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, runtimePayload depth⟩ ∧
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
      stage.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  have native := SourceOperationNative.Observed.model_factorizes (process := process) rawClock (runtimeAt depth)
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  have nextRead : clockRead (action (point depth)) = rawClock (runtimeAt depth).tick.next.state :=
    (congrArg clockRead native.1).trans native.2.1
  exact ⟨native.1, nextRead, clock_native_target depth, clockRead_action (point depth), mass_current depth,
    (massRead_action (point depth)).trans (mass_current depth), model_ext_iff left right,
    (fun index => ⟨(window_actor_factorizes depth index).1, (window_actor_factorizes depth index).2.1,
      clock_current index.val⟩),
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    native.2.2.2, runtime_current_next depth⟩

end
end SourceClockModel.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
