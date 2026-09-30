import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Posterior
import H0mework.Versions.X.Fock.SourceHistory.CountedMerge.Information

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordNativeAlignment

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open SourceGeneratedAcquisitionContinuation
open SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem native_read (depth index : Nat) :
    SourceWordObservedCode.readAt depth [] index = forgetClock (clockRead 0 index) := by
  rw [SourceWordObservedCode.readAt, SourceWordObservedCode.observe,
    Fock.actualWord, List.foldl_nil]
  have nextIndex : scanIndex (nativeStep ((runtimeAt index).current.visit.current : Current)) =
      index + 2 := by
    have step : scanIndex (nativeStep ((runtimeAt index).current.visit.current : Current)) =
        scanIndex ((runtimeAt index).current.visit.current : Current) + 1 :=
      scanIndex_next _
    have current : scanIndex ((runtimeAt index).current.visit.current : Current) =
        index + 1 := runtimeAt_scanIndex index
    omega
  rw [nextIndex, SourceConditionalNativeMerge.clock_factor]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide]
  simp

theorem native_read_fun (depth : Nat) :
    SourceWordObservedCode.readAt depth [] = forgetClock ∘ clockRead 0 := by
  funext index
  exact native_read depth index

theorem native_word_risk_eq_original_gap (runtime : LivingRuntimeState process) :
    SourceWordCodeRisk.risk runtime [] (SourceWordObservedCode.encodeObserved runtime [])
      (SourceConditionalNativePosterior.decoder runtime (forgetClock ∘ clockRead 0)) =
        SourceConditionalMergeLoss.gap runtime (clockRead 0) forgetClock := by
  have fineZero :
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalNativePosterior.decoder runtime (clockRead 0)
            (clockRead 0 actor.val)‖ ^ 2) = 0 := by
    simpa only [SourceConditionalMergeLoss.clock_fine] using
      SourceConditionalNativeObservers.error_zero runtime
  have loss := SourceConditionalMergeLoss.loss runtime (clockRead 0) forgetClock
  rw [SourceConditionalMergeLoss.decoder_original, fineZero, zero_add] at loss
  have nativeLoss :
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalNativePosterior.decoder runtime (forgetClock ∘ clockRead 0)
            (forgetClock (clockRead 0 actor.val))‖ ^ 2) =
        SourceConditionalMergeLoss.gap runtime (clockRead 0) forgetClock := by
    rw [SourceConditionalMergeLoss.gap, SourceConditionalMergeLoss.decoder_original]
    exact loss
  calc
    _ = ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) [] actor -
          SourceConditionalNativePosterior.decoder runtime (forgetClock ∘ clockRead 0)
            (SourceWordCodeRisk.query runtime []
              (SourceWordObservedCode.encodeObserved runtime []) actor)‖ ^ 2 :=
      SourceWordCodeRisk.risk_eq runtime []
        (SourceWordObservedCode.encodeObserved runtime []) _
    _ = ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalNativePosterior.decoder runtime (forgetClock ∘ clockRead 0)
            (forgetClock (clockRead 0 actor.val))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro actor _
      have imageNil : SourceCompiledGWord.image runtime (inventoryBound runtime + 1) [] actor =
          SourceConditionalVector.realizeModel runtime (nextRead runtime actor) := by
        rw [SourceCompiledGWord.image_original, SourceCompiledGWord.effect_nil]
        simpa only [Function.comp_apply, ContinuousLinearMap.id_apply] using
          SourceConditionalInventory.values_original runtime actor
      rw [imageNil, SourceWordObservedCode.query_actual,
        SourceWordObservedCode.source_query_read, native_read]
    _ = _ := nativeLoss

theorem native_gap_full_account (runtime : LivingRuntimeState process) :
    let query := SourceWordCodeRisk.query runtime []
      (SourceWordObservedCode.encodeObserved runtime [])
    let decoder := SourceConditionalNativePosterior.decoder runtime
      (forgetClock ∘ clockRead 0)
    SourceConditionalMergeLoss.gap runtime (clockRead 0) forgetClock =
      SourceConditionalInventory.cost (inventoryBound runtime) query /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile
        (([] : List (Fock.Letter (inventoryBound runtime + 1))).map
          SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ‖SourceWeightedRecovery.residual (historyPMF (inventoryBound runtime)) query
          (SourceWeightedRecovery.taskValue (historyPMF (inventoryBound runtime))
            (SourceJointClockGraph.clock ∘ SourceConditionalInventory.values
              (inventoryBound runtime)))‖ ^ 2 +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceCompiledGWord.effect (inventoryBound runtime + 1) []
          (SourceVectorMoment.mean
            (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
              query (query actor)
              (SourceWeightedRecovery.observed_supported _ _ actor
                (SourceUniformFibreVariance.source_positive _ actor)))
            (SourceConditionalInventory.values (inventoryBound runtime))) -
          decoder (query actor)‖ ^ 2 := by
  dsimp only
  rw [← native_word_risk_eq_original_gap runtime]
  exact SourceWordCodeRisk.risk_account runtime []
    (SourceWordObservedCode.encodeObserved runtime [])
    (SourceConditionalNativePosterior.decoder runtime (forgetClock ∘ clockRead 0))

theorem original_gap_code_lower (runtime : LivingRuntimeState process) :
    ((inventoryBound runtime + 1 : ℝ) - Fintype.card (ZMod 2)) /
      (inventoryBound runtime + 1 : ℝ) ≤
        SourceConditionalMergeLoss.gap runtime (clockRead 0) forgetClock := by
  have info := SourceWordObservedCode.observed_information_risk runtime []
    (SourceConditionalNativePosterior.decoder runtime (forgetClock ∘ clockRead 0))
  rw [native_word_risk_eq_original_gap] at info
  have hEnt := SourceWordCodeRisk.entropy_nonnegative runtime []
    (SourceWordObservedCode.encodeObserved runtime [])
  rw [SourceWordObservedCode.query_source] at hEnt
  have hExp : 0 ≤
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
        (inventoryBound runtime) (SourceWordObservedCode.sourceQuery runtime [])) - 1) / 12 := by
    have h := Real.add_one_le_exp (2 * SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound runtime) (SourceWordObservedCode.sourceQuery runtime []))
    nlinarith
  have hSlope : 0 ≤
      ((SourceCopyWordAffine.compile (([] : List (Fock.Letter (inventoryBound runtime + 1))).map
        SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hSlope hExp]

theorem original_gap_half_at_three :
    (1 / 2 : ℝ) ≤ SourceConditionalMergeLoss.gap (runtimeAt 3)
      (clockRead 0) forgetClock := by
  have paid := original_gap_code_lower (runtimeAt 3)
  have hCard : Fintype.card (ZMod 2) = 2 := by decide
  have hN : inventoryBound (runtimeAt 3) = 3 := by
    rw [inventory_bound, runtimeAt_state]
  have hMargin :
      ((inventoryBound (runtimeAt 3) + 1 : ℝ) - Fintype.card (ZMod 2)) /
        (inventoryBound (runtimeAt 3) + 1 : ℝ) = 1 / 2 := by
    rw [hN, hCard]
    norm_num
  rw [hMargin] at paid
  exact paid

theorem original_next_gap_three_fifths :
    (3 / 5 : ℝ) ≤ SourceConditionalMergeLoss.gap (runtimeAt 3).tick.next
      (clockRead 0) forgetClock := by
  have paid := original_gap_code_lower (runtimeAt 3).tick.next
  have hCard : Fintype.card (ZMod 2) = 2 := by decide
  have hN : inventoryBound (runtimeAt 3).tick.next = 4 := by
    rw [SourceActualImageStep.next_bound, inventory_bound, runtimeAt_state]
  have hMargin :
      ((inventoryBound (runtimeAt 3).tick.next + 1 : ℝ) - Fintype.card (ZMod 2)) /
        (inventoryBound (runtimeAt 3).tick.next + 1 : ℝ) = 3 / 5 := by
    rw [hN, hCard]
    norm_num
  rw [hMargin] at paid
  exact paid

end
end SourceWordNativeAlignment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
