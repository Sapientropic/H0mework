import H0mework.Fock.SourceHistoryClock.BinomialPrefixDecoder
import H0mework.Fock.SourceHistoryClock.BinomialConsumer

/-! Finite raw past reads generate the original next window and square task at the same installed occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Prefix

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem runtime_finite_information (depth : Nat) :
    let runtime := runtimeAt (depth + 3)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    next (currentSamples (depth + 1)) = samples (depth + 1) ∧
      next (currentSamples (depth + 1)) =
        ![(currentSamples (depth + 1)) 1, (currentSamples (depth + 1)) 2,
          (currentSamples (depth + 1)) 0 - 3 * (currentSamples (depth + 1)) 1 + 3 * (currentSamples (depth + 1)) 2] ∧
      next (currentSamples (depth + 1)) (Fin.last 2) = rawSecond stage.next.state ∧
      type_of% (exact_finite_cost (depth + 1)) ∧
      (∀ index : Fin 3, decode (depth + 1) (currentSamples (depth + 1)) index =
        Runtime.Actor.History.Clock.sourceSquare 2 index) ∧
      (∀ value : Model, recover (window value) = value) ∧
      (∀ value : Model, short value = 0 ↔ value = massRead value • hidden) ∧
      hidden = projection hiddenWord ∧
      type_of% no_short_next ∧
      (∀ index : Fin 3, Runtime.Actor.History.Clock.posterior 2 (depth + 1) index = PMF.pure index) ∧
      (∀ index candidate : Fin 3, candidate ∈ (Runtime.Actor.History.Clock.posterior 2 (depth + 1) index).support →
        HEq ((history runtimeSeed 2).stageAt candidate) ((history runtimeSeed 2).stageAt index)) ∧
      (∀ index : Fin 3, type_of% (sample_factorizes runtimeSeed 2 index) ∧
        type_of% (sample_factorizes (runtimeSeed.advance (depth + 1)) 2 index)) ∧
      (∀ index : Fin (SourceOwnedObservationHistory.NativeWindow.bound runtime.current.visit.current + 1),
        type_of% (SourceOwnedObservationHistory.Installed.window_actor_factorizes (depth + 3) index)) ∧
      (runtimePayload (depth + 3)).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive (depth + 3), runtimePayload (depth + 3)⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload (depth + 3)).nativeWrite.target := by
  rcases original_square_information (depth + 1) with
    ⟨_oldCost, _oldLinear, _forget, posterior, material, query, _relation, _fibre, _frame, _effect,
      actors, fullHistory, sourceOccurrence, face, installation, ledger, nextCurrent, target⟩
  have last : next (currentSamples (depth + 1)) (Fin.last 2) =
      rawSecond (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (depth + 3))).next.state := by
    rw [next_samples, samples_are_actual, query]
    exact SourceOperationNative.Observed.modelPoint_read (process := process) rawSecond
      (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (depth + 3))).next
  exact ⟨next_samples (depth + 1), next_apply (currentSamples (depth + 1)), last,
    exact_finite_cost (depth + 1), decode_actual (depth + 1), recover_window, short_fibre,
    hidden_is_source, no_short_next, posterior, material, actors, fullHistory,
    sourceOccurrence, face, installation, ledger, nextCurrent, target⟩

end
end SourceBinomialClock.Prefix
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
