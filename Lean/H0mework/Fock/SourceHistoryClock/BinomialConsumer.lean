import H0mework.Fock.SourceHistoryClock.BinomialRecovery
import H0mework.Fock.SourceHistoryClock.PosteriorSquare

/-! The original square consumer reads the new moment at its literal next, keeping the old posterior and lost direction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceWeightedRecovery

noncomputable section

theorem original_square_information (depth : Nat) :
    let runtime := runtimeAt (depth + 2)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    error (historyPMF 2) (futureModel 2 depth) (Runtime.Actor.History.Clock.sourceSquare 2)
        (fun value => (pastSquare (depth + 1) value : ℂ)) = 0 ∧
      type_of% (Runtime.Actor.History.Clock.no_linear_square_readout depth) ∧
      (∀ index : Fin 3, forgetClock (futureModel 2 depth index) = Runtime.Actor.History.Clock.futureModel 2 depth index) ∧
      (∀ index : Fin 3, Runtime.Actor.History.Clock.posterior 2 depth index = PMF.pure index) ∧
      (∀ index candidate : Fin 3, candidate ∈ (Runtime.Actor.History.Clock.posterior 2 depth index).support →
        HEq ((history runtimeSeed 2).stageAt candidate) ((history runtimeSeed 2).stageAt index)) ∧
      futureModel 2 depth (Fin.last 2) =
        SourceOperationNative.Observed.modelPoint (process := process) rawSecond stage.next ∧
      type_of% (Controls.original_relation_resolved (depth + 1)) ∧
      (∀ value : Model, forgetClock value = 0 ↔ value = secondRead value • Frame.secondEffect (depth + 1)) ∧
      (Frame.frame (depth + 1)).symm (Frame.frame (depth + 1) (futureModel 2 depth (Fin.last 2))) =
        futureModel 2 depth (Fin.last 2) ∧
      Frame.secondEffect (depth + 1) =
        SourceOperationNative.Observed.modelPoint (process := process) rawSecond stage.next -
          (2 : ℤ) • Fock.point (depth + 2) + Fock.point (depth + 1) ∧
      (∀ index : Fin 3, type_of% (sample_factorizes runtimeSeed 2 index) ∧
        type_of% (sample_factorizes (runtimeSeed.advance depth) 2 index)) ∧
      (∀ index : Fin (SourceOwnedObservationHistory.NativeWindow.bound runtime.current.visit.current + 1),
        type_of% (SourceOwnedObservationHistory.Installed.window_actor_factorizes (depth + 2) index)) ∧
      (runtimePayload (depth + 2)).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive (depth + 2), runtimePayload (depth + 2)⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload (depth + 2)).nativeWrite.target := by
  rcases runtime_frame_factorizes (depth + 1) (futureModel 2 depth (Fin.last 2)) with
    ⟨reconstructed, _fibre, relation, _firstEffect, secondEffect, _action, _square,
      fullHistory, sourceOccurrence, face, installation, stageFacts, next⟩
  rcases Runtime.Actor.History.Clock.square_posterior_information depth with
    ⟨_originalCost, oldLinearObstruction, posterior, material, actors, _occurrence, _face, _ledger, _next, _target⟩
  have actualQuery : futureModel 2 depth (Fin.last 2) =
      SourceOperationNative.Observed.modelPoint (process := process) rawSecond
        (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (depth + 2))).next :=
    (futureModel_source 2 depth (Fin.last 2)).trans
      (congrArg Fock.point (by omega : 2 + (depth + 1) = depth + 3))
  exact ⟨exact_square_cost 2 depth, oldLinearObstruction, forget_futureModel 2 depth,
    posterior, material, actualQuery, relation, forgotten_direction (depth + 1),
    reconstructed, secondEffect, actors, fullHistory, sourceOccurrence, face, installation,
    stageFacts.2.2.1, stageFacts.2.2.2, next⟩

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
