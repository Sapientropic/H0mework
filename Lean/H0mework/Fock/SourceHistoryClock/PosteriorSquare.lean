import H0mework.Fock.SourceHistoryClock.PosteriorInstalled

/-! The original nonlinear source task is recovered without claiming a nonexistent linear old-model readout. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History.Clock

open SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem square_posterior_information (depth : Nat) :
    let runtime := runtimeAt (depth + 2)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    error (historyPMF 2) (observe 2 depth) (sourceSquare 2)
        (optimalDecoder (historyPMF 2) (observe 2 depth) (sourceSquare 2)) = 0 ∧
      type_of% (no_linear_square_readout depth) ∧
      (∀ index : Fin 3, posterior 2 depth index = PMF.pure index) ∧
      (∀ index candidate : Fin 3, candidate ∈ (posterior 2 depth index).support →
        HEq ((history runtimeSeed 2).stageAt candidate) ((history runtimeSeed 2).stageAt index)) ∧
      (∀ index : Fin 3, type_of% (sample_factorizes runtimeSeed 2 index) ∧
        type_of% (sample_factorizes (runtimeSeed.advance depth) 2 index)) ∧
      (runtimePayload (depth + 2)).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive (depth + 2), runtimePayload (depth + 2)⟩ ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload (depth + 2)).nativeWrite.target := by
  rcases runtime_posterior_factorizes 2 depth (sourceSquare 2) with
    ⟨posterior, _decoded, recovered, _residual, material, _query, actors,
      sourceOccurrence, face, _installation, stageFacts, next⟩
  exact ⟨recovered, no_linear_square_readout depth, posterior, material, actors,
    sourceOccurrence, face, stageFacts.2.2.1, stageFacts.2.2.2, next⟩

end
end SourceWeightedRecovery.Runtime.Actor.History.Clock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
