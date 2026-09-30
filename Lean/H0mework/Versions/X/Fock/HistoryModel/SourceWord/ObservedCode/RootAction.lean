import H0mework.Versions.X.Fock.HistoryModel.SourceWord.NativeAlignment.Ledger
import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Posterior
import H0mework.Fock.HistoryConditional.WordAffineEquation
import H0mework.Versions.X.Fock.HistoryConditional.CopyWordSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordActedRow

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem row_action_read (depth : Nat) (word : List (Fock.Letter (depth + 1)))
    (index : Nat) :
    SourceWordObservedCode.readAt depth word index =
      SourceWordObservedCode.observe
        (Fock.actualWord (depth + 1) word
          (runtimePayload index).nativeWrite.target) := rfl

theorem post_word_row_law (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    SourceWordObservedCode.postWordLaw runtime word =
      (historyPMF (inventoryBound runtime)).map
        (fun actor : Actors runtime =>
          SourceWordObservedCode.observe
            (Fock.actualWord (inventoryBound runtime + 1) word
              (runtimePayload actor.val).nativeWrite.target)) := by
  rw [SourceWordObservedCode.post_word_law]
  rfl

theorem counted_row_posterior (runtime : LivingRuntimeState process)
    (nonunit : (SourceCopyCurrentCoordinates.maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map
      (fun actor : Actors runtime =>
        SourceWordObservedCode.observe
          (Fock.actualWord (inventoryBound runtime + 1) word
            (runtimePayload actor.val).nativeWrite.target))).support) :
    SourcePosteriorReadback.readWeight runtime
      (SourceCountedPosterior.model runtime
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
        (SourceWordObservedCode.table runtime nonunit word 0) key) =
      (fun actor => SourceConditionalHistory.conditional
        (historyPMF (inventoryBound runtime))
        (fun index : Actors runtime =>
          SourceWordObservedCode.observe
            (Fock.actualWord (inventoryBound runtime + 1) word
              (runtimePayload index.val).nativeWrite.target))
        key supported actor) := by
  have queryEq : SourceWordObservedCode.sourceQuery runtime word =
      (fun actor : Actors runtime =>
        SourceWordObservedCode.observe
          (Fock.actualWord (inventoryBound runtime + 1) word
            (runtimePayload actor.val).nativeWrite.target)) := by
    funext actor
    exact (SourceWordObservedCode.source_query_read runtime word actor).trans
      (row_action_read (inventoryBound runtime) word actor.val)
  have supportedQuery : key ∈ ((historyPMF (inventoryBound runtime)).map
      (SourceWordObservedCode.sourceQuery runtime word)).support := by
    simpa only [queryEq] using supported
  simpa only [queryEq] using
    (SourceWordObservedCode.counted_complete_posterior runtime nonunit word key supportedQuery)

theorem row_information_risk (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    ((inventoryBound runtime + 1 : ℝ) - Fintype.card (ZMod 2)) /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ((Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
          (inventoryBound runtime) (fun actor : Actors runtime =>
            SourceWordObservedCode.observe
              (Fock.actualWord (inventoryBound runtime + 1) word
                (runtimePayload actor.val).nativeWrite.target))) - 1) / 12) ≤
      SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) decoder := by
  have queryEq : SourceWordObservedCode.sourceQuery runtime word =
      (fun actor : Actors runtime =>
        SourceWordObservedCode.observe
          (Fock.actualWord (inventoryBound runtime + 1) word
            (runtimePayload actor.val).nativeWrite.target)) := by
    funext actor
    exact (SourceWordObservedCode.source_query_read runtime word actor).trans
      (row_action_read (inventoryBound runtime) word actor.val)
  simpa only [queryEq] using
    (SourceWordObservedCode.observed_information_risk runtime word decoder)

theorem word_scan_affine (depth : Nat) (word : List (Fock.Letter depth))
    (state : Nat) :
    scanIndex (Fock.actualWord depth word (finiteVisit state).current) =
      (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 * (state + 1) +
        (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).2 := by
  rw [SourceCopyNativeWord.run_original]
  rw [finiteVisit_current]
  simp only [scanIndex, UnitHistory.cardinalShadow_generate]
  exact SourceCopyWordAffine.equation _ _

theorem word_native_order_equation (depth : Nat) (word : List (Fock.Letter depth))
    (state : Nat) :
    scanIndex (Fock.actualWord depth word (nativeStep (finiteVisit state).current)) =
      scanIndex (Fock.actualWord depth word (finiteVisit state).current) +
        (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 := by
  have source : nativeStep (finiteVisit state).current = (finiteVisit (state + 1)).current := by
    rw [finiteVisit_current, finiteVisit_current]
    rfl
  rw [source, word_scan_affine, word_scan_affine]
  rw [Nat.mul_succ]
  omega

theorem word_commutes_native_iff_unit_slope (depth : Nat)
    (word : List (Fock.Letter depth)) (state : Nat) :
    Fock.actualWord depth word (nativeStep (finiteVisit state).current) =
        nativeStep (Fock.actualWord depth word (finiteVisit state).current) ↔
      (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 = 1 := by
  constructor
  · intro same
    have observed := congrArg scanIndex same
    rw [word_native_order_equation, scanIndex_next] at observed
    omega
  · intro slope
    apply UnitHistory.eq_of_cardinalShadow_eq
    change scanIndex (Fock.actualWord depth word (nativeStep (finiteVisit state).current)) =
      scanIndex (nativeStep (Fock.actualWord depth word (finiteVisit state).current))
    rw [word_native_order_equation, scanIndex_next, slope]

theorem native_letter_commutes (depth state : Nat) :
    Fock.actualWord depth [(.inl () : Fock.Letter depth)]
        (nativeStep (finiteVisit state).current) =
      nativeStep (Fock.actualWord depth [(.inl () : Fock.Letter depth)]
        (finiteVisit state).current) := by
  exact (word_commutes_native_iff_unit_slope depth [(.inl ())] state).mpr rfl

theorem actual_copy_one_does_not_commute (state : Nat) :
    Fock.actualWord (inventoryBound (runtimeAt 3) + 1)
        [SourceWordDynamicNext.copyOne] (nativeStep (finiteVisit state).current) ≠
      nativeStep (Fock.actualWord (inventoryBound (runtimeAt 3) + 1)
        [SourceWordDynamicNext.copyOne] (finiteVisit state).current) := by
  intro same
  have unit := (word_commutes_native_iff_unit_slope _
    [SourceWordDynamicNext.copyOne] state).mp same
  exact (Nat.ne_of_gt SourceWordDynamicNext.copyOne_slope) unit

theorem actual_copy_one_observation_order_clash :
    SourceWordObservedCode.readAt 3 [SourceWordDynamicNext.copyOne] 0 ≠
      SourceWordNativeAlignment.nativeObservation
        (runtimePayload (SourceCopyNativeWord.run
          ([SourceWordDynamicNext.copyOne].map SourceCopyNativeWord.encode) 0)) := by
  decide

end
end SourceWordActedRow
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
