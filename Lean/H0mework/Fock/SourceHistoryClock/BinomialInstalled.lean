import H0mework.Fock.SourceHistory.ClockBinomialRegression
import H0mework.Fock.SourceHistoryClock.FrameInstalled

/-! The past point and two actual steps are consumed at the current owning the second step. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOwnedObservationHistory.Installed

noncomputable section

theorem runtime_frame_factorizes (depth : Nat) (value : Model) :
    let runtime := runtimeAt (depth + 1)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    (Frame.frame depth).symm (Frame.frame depth value) = value ∧
      (forgetClock value = 0 ↔ value = secondRead value • Frame.secondEffect depth) ∧
      type_of% (Controls.original_relation_resolved depth) ∧
      Frame.effect depth = Fock.point (depth + 1) - Fock.point depth ∧
      Frame.secondEffect depth =
        SourceOperationNative.Observed.modelPoint (process := process) rawSecond stage.next -
          (2 : ℤ) • Fock.point (depth + 1) + Fock.point depth ∧
      action (Fock.point (depth + 1)) =
        SourceOperationNative.Observed.modelPoint (process := process) rawSecond stage.next ∧
      squareRead (SourceOperationNative.Observed.modelPoint (process := process) rawSecond stage.next) =
        ((depth + 2 : Nat) : ℤ) ^ 2 ∧
      (∀ index : Fin (SourceOwnedObservationHistory.NativeWindow.bound runtime.current.visit.current + 1),
        type_of% (window_actor_factorizes (depth + 1) index)) ∧
      (runtimePayload (depth + 1)).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive (depth + 1), runtimePayload (depth + 1)⟩ ∧
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
      stage.next.current.visit.current = (runtimePayload (depth + 1)).nativeWrite.target := by
  have native := SourceOperationNative.Observed.model_factorizes (process := process) rawSecond (runtimeAt (depth + 1))
  have installed := coversAt_factorizes (runtimeAt (depth + 1)) .particleWave
  exact ⟨(Frame.frame depth).symm_apply_apply value, forgotten_direction depth value,
    Controls.original_relation_resolved depth, effect_is_actual depth, secondEffect_is_actual depth,
    native.1, Fock.square_point (depth + 2), window_actor_factorizes (depth + 1),
    (runtimePayload (depth + 1)).sourceOccurrence_eq, runtimeReadout_is_particleWave (depth + 1),
    installed.2.2.2.1, native.2.2.2, runtime_current_next (depth + 1)⟩

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
