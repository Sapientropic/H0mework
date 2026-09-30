import H0mework.Fock.SourceHistory.ClockFrameRegression
import H0mework.Fock.SourceHistoryClock.Installed

/-! The original runtime's point and actual one-step effect generate and consume the complete model frame. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockFrame

open SourceClockModel SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem effect_is_native_next (depth : Nat) :
    effect depth = Fock.point (depth + 1) - Fock.point depth := by
  rw [effect, Fock.point_next]

theorem runtime_frame_factorizes (depth : Nat) (value : Model) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    frame depth (Fock.point depth) = (1, 0) ∧
      frame depth (effect depth) = (0, 1) ∧
      (frame depth).symm (frame depth value) = value ∧
      action value = value + massRead value • effect depth ∧
      inverse depth (action value) = value ∧
      action (inverse depth value) = value ∧
      effect depth = Fock.point (depth + 1) - Fock.point depth ∧
      action (Fock.point depth) = SourceOperationNative.Observed.modelPoint (process := process) rawClock stage.next ∧
      clockRead (action (Fock.point depth)) = (scanIndex (runtimePayload depth).nativeWrite.target : ℤ) ∧
      inverse 0 (Fock.point 0) = projection (SourceClockModel.Controls.hiddenWord 0) ∧
      (∀ nativeDepth : Nat, inverse 0 (Fock.point 0) ≠ Fock.point nativeDepth) ∧
      (∀ index : Fin (SourceOwnedObservationHistory.NativeWindow.bound runtime.current.visit.current + 1),
        SourceOwnedObservationHistory.NativeWindow.point runtime.current.visit.current index =
          (runtimeAt index.val).current.visit.current ∧
          SourceOwnedObservationHistory.NativeWindow.imagePoint runtime.current.visit.current index =
            ((materialHistory depth).stageAt index).next.current.visit.current ∧
          effect index.val = Fock.point (index.val + 1) - Fock.point index.val) ∧
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
  exact ⟨coordinates_point depth, coordinates_effect depth, (frame depth).symm_apply_apply value,
    action_formula depth value, inverse_action depth value, action_inverse depth value,
    effect_is_native_next depth, native.1, Fock.clock_native_target depth,
    Controls.inverse_is_hidden_word, Controls.inverse_is_not_native,
    (fun index => ⟨(window_actor_factorizes depth index).1, (window_actor_factorizes depth index).2.1,
      effect_is_native_next index.val⟩),
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    native.2.2.2, runtime_current_next depth⟩

end
end SourceClockFrame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
