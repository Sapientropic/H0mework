import H0mework.Versions.X.Fock.HistoryModel.SourceWord.NativeAlignment.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordNativeAlignment

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation
open CanonicalUnitArithmeticRoot (Current)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

/-- The installed particle-wave payload already carries this native observation. -/
def nativeObservation {current : Current}
    {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
    {active : 1 ≤ scanIndex current}
    (payload : RootGeneratedParticleWaveCurrentAt current occurrence active) : ZMod 2 :=
  SourceWordObservedCode.observe payload.nativeWrite.target

theorem payload_native_observe (depth index : Nat) :
    nativeObservation (runtimePayload index) =
      SourceWordObservedCode.readAt depth [] index := rfl

theorem generated_native_observed_law (depth : Nat) :
    SourceWordObservedCode.postWordLaw (runtimeAt depth) [] =
      (historyPMF (inventoryBound (runtimeAt depth))).map
        (fun actor : SourceConditionalModel.Actors (runtimeAt depth) =>
          nativeObservation (runtimePayload actor.val)) := by
  rw [SourceWordObservedCode.post_word_law]
  rfl

theorem installed_face (depth : Nat) :
    let runtime := runtimeAt depth
    let payload := runtimePayload depth
    nativeObservation payload = SourceWordObservedCode.readAt depth [] depth ∧
      runtimeFacade.readoutAt runtime .particleWave =
        .inl ⟨runtimeActive depth, payload⟩ ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      runtime.tick.nextCurrent =
        runtimeFacade.process.stateAt (runtimeFacade.process.successor runtime.state) := by
  dsimp only
  rcases coversAt_factorizes (runtimeAt depth) .particleWave with
    ⟨_, _, ledger, _, next⟩
  exact ⟨payload_native_observe depth depth,
    runtimeReadout_is_particleWave depth, ledger, next⟩

end
end SourceWordNativeAlignment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
