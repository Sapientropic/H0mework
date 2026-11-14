import H0mework.Versions.R453de275.Fock.HistoryCopy.Consumer
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.Model.Family.Words.Dynamic.Hilbert.SourceWord.ObservedCode.Future.Growth.Receiver.EvenBirth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordEvenBirth

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
noncomputable section

/-- Each fresh even-to-odd birth is a different actual material occurrence. The
original receiver reads its full posterior at the generated next inventory,
while its old future code pays the physical G loss on the new task. -/
theorem original_copy_consumes_even_birth (depth : Nat) (enough : 2 ≤ depth)
    (even : Even depth) (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    let runtime := runtimeAt (depth + 1)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    SourceCopyObservation.CurrentAt runtime ∧
      runtime = (runtimeAt depth).tick.next ∧
      ((runtimeAt depth).tick.next.current.visit.current : Current) ≠
        ((runtimeAt (depth + 1)).tick.next.current.visit.current : Current) ∧
      (∀ actor : Actors runtime,
        SourceWordObservedCode.sourceQuery runtime (oldWord depth) actor = 0 ∧
        SourceWordObservedCode.sourceQuery runtime (newWord depth) actor =
          SourceWordObservedCode.readAt (depth + 1) [] actor.val ∧
        SourcePosteriorReadback.readWeight runtime
          (SourceCountedPosterior.model runtime
            (SourceRetainedReceiver.trajectory_nonunit runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) 0)
            (SourceWordObservedCode.table runtime
              (SourceWordFutureBitGrowth.nextNonunit depth) (newWord depth) 0)
            (SourceWordObservedCode.sourceQuery runtime (newWord depth) actor)) =
          SourceConditionalHistory.conditional
            (historyPMF (inventoryBound runtime))
            (SourceWordFutureBit.futureRead runtime (newWord depth))
            (SourceWordFutureBit.futureRead runtime (newWord depth) actor)
            (SourceWeightedRecovery.observed_supported _ _ actor
              (SourceUniformFibreVariance.source_positive _ actor))) ∧
      (∀ decode : FutureResponse depth → FutureResponse depth,
        ¬ ∀ actor : Actors runtime,
          decode (SourceWordFutureBit.futureRead runtime (oldWord depth) actor) =
            SourceWordFutureBit.futureRead runtime (newWord depth) actor) ∧
      type_of% (SourceWordFutureBit.future_information runtime (newWord depth)) ∧
      type_of% (SourceWordCodeRisk.risk_account runtime (newWord depth)
        (oldCode depth) decoder) ∧
      0 < SourceWordCodeRisk.risk runtime (newWord depth) (oldCode depth) decoder ∧
      ((depth + 1 : Nat) : ℝ) / ((depth + 2 : Nat) : ℝ) ≤
        SourceWordCodeRisk.risk runtime (newWord depth) (oldCode depth) decoder ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent := by
  dsimp only
  have risk := oldCode_original_G_risk depth even decoder
  have positiveRatio : 0 < ((depth + 1 : Nat) : ℝ) / ((depth + 2 : Nat) : ℝ) := by
    have numerator : (0 : ℝ) < ((depth + 1 : Nat) : ℝ) := by positivity
    have denominator : (0 : ℝ) < ((depth + 2 : Nat) : ℝ) := by positivity
    exact div_pos numerator denominator
  exact ⟨SourceCopyObservation.current_consumed (runtimeAt (depth + 1)),
    (SourceWordFutureBitGrowth.next_runtime depth).symm,
    old_new_material_distinct depth,
    (fun actor => ⟨old_query_zero depth even actor,
      new_query_native depth even actor,
      SourceWordFutureBit.counted_future_posterior (runtimeAt (depth + 1))
        (SourceWordFutureBitGrowth.nextNonunit depth) (newWord depth) actor⟩),
    old_future_cannot_recover_new depth even,
    SourceWordFutureBit.future_information (runtimeAt (depth + 1)) (newWord depth),
    SourceWordCodeRisk.risk_account (runtimeAt (depth + 1)) (newWord depth)
      (oldCode depth) decoder,
    positiveRatio.trans_le risk, risk,
    (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtimeAt (depth + 1))).factorizes.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate
      (runtimeAt (depth + 1))).factorizes.2.2.2⟩

end
end SourceWordEvenBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
