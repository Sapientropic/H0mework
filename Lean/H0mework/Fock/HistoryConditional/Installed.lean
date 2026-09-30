import H0mework.Fock.HistoryConditional.Source

/-! The current source query retains full conditional stage provenance and recombines the original history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalHistory.Fock

open SourceGeneratedRuntimeHistoryProbability SourceObservationInvariantControls
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem runtime_conditional_factorizes (depth : Nat) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    query depth = parity runtime.state ∧
      Fin.last depth ∈ (conditional depth).support ∧
      (observed depth).bindOnSupport (Runtime.conditional (process := process) runtimeSeed depth parity) = historyPMF depth ∧
      (observed depth).bindOnSupport
        (fun value supported =>
          (Runtime.conditional (process := process) runtimeSeed depth parity value supported).map (sample runtimeSeed depth)) =
        statePMF runtimeSeed depth ∧
      (∀ index : Fin (depth + 1), index ∈ (conditional depth).support →
        let actor := (history runtimeSeed depth).stageAt index
        parity (sample runtimeSeed depth index) = query depth ∧
          (process.toAnswerNextCausalWorld.emitted (ULift.up (sample runtimeSeed depth index)) =
              ULift.up actor.activated.generated ∧
            actor.activated.generated.occurrence =
              (runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
                (runtimeAt index.val).current.visit.current ∧
            HEq actor.wholeLedgerWriteBack
              ((runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
                (runtimeAt index.val).current.visit.current) ∧
            actor.next.current = actor.activated.nextCurrent)) ∧
      (∀ index : Fin (depth + 1),
        sample runtimeSeed depth index = (runtimeAt index.val).state ∧
          ((history runtimeSeed depth).stageAt index).next.current.visit.current =
            (runtimePayload index.val).nativeWrite.target) ∧
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
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  exact ⟨rfl, current_supported depth, recombine_indices depth, recombine_states depth,
    (fun index member => Runtime.conditional_index_factorizes (process := process) runtimeSeed depth parity
      (query depth) (query_supported depth) index member),
    (fun index => ⟨rfl, runtime_current_next index.val⟩),
    (runtimePayload depth).sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes, runtime_current_next depth⟩

end
end SourceConditionalHistory.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
