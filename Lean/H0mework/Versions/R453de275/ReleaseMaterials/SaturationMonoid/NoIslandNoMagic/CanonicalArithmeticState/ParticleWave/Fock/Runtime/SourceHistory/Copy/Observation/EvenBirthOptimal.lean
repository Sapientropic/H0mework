import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Copy.Observation.EvenBirth
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Receiver.EvenBirthOptimal

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordEvenBirthOptimal

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- At each new even-to-odd material birth, the original Copy consumer charges
the strictly positive optimal G recovery gain to the same posterior, row and next. -/
theorem original_copy_consumes_optimal_gain (depth : Nat) (enough : 2 ≤ depth)
    (even : Even depth) :
    let runtime := runtimeAt (depth + 1)
    let word := SourceWordEvenBirth.newWord depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    SourceCopyObservation.CurrentAt runtime ∧
      runtime = (runtimeAt depth).tick.next ∧
      ((runtimeAt depth).tick.next.current.visit.current : Current) ≠
        ((runtimeAt (depth + 1)).tick.next.current.visit.current : Current) ∧
      (∀ actor : Actors runtime,
        SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) 0)
            (SourceWordObservedCode.table runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) word 0)
            (SourceWordObservedCode.sourceQuery runtime word actor)) =
          SourceConditionalHistory.conditional
            (historyPMF (inventoryBound runtime))
            (SourceWordFutureBit.futureRead runtime word)
            (SourceWordFutureBit.futureRead runtime word actor)
            (SourceWeightedRecovery.observed_supported _ _ actor
              (SourceUniformFibreVariance.source_positive _ actor))) ∧
      0 < SourceConditionalInformationLoss.amount runtime
        (fineRead depth) forget ∧
      0 < SourceWordFieldCode.gGap runtime word (fineRead depth) forget ∧
      SourceWordCodeRisk.risk runtime word
          (SourceWordEvenBirth.oldCode depth) (oldBest depth) =
        SourceWordCodeRisk.risk runtime word
          (SourceWordObservedCode.encodeObserved runtime word) (freshBest depth) +
        SourceWordFieldCode.gGap runtime word (fineRead depth) forget ∧
      SourceWordCodeRisk.risk runtime word
          (SourceWordObservedCode.encodeObserved runtime word) (freshBest depth) <
        SourceWordCodeRisk.risk runtime word
          (SourceWordEvenBirth.oldCode depth) (oldBest depth) ∧
      ((depth + 1 : Nat) : ℝ) / ((depth + 2 : Nat) : ℝ) ≤
        SourceWordCodeRisk.risk runtime word
          (SourceWordEvenBirth.oldCode depth) (oldBest depth) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent := by
  dsimp only
  have paid := SourceWordEvenBirth.original_copy_consumes_even_birth
    depth enough even (oldBest depth)
  dsimp only at paid
  rcases paid with ⟨current, successor, distinct, posterior, _, _, _, _, lower,
    wholeLedger, nextCurrent⟩
  exact ⟨current, successor, distinct, (fun actor => (posterior actor).2.2),
    information_loss_pos depth even, gain_pos depth even,
    exact_gain depth even, strict_gain depth even, lower,
    wholeLedger, nextCurrent⟩

end
end SourceWordEvenBirthOptimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
