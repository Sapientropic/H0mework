import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.RiskBirth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

/-- The original source posterior is acted on by the word's generated physical G operator. -/
def gBest (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1))) (key : ZMod 2) :
    SourceJointClockGraph.Carrier :=
  SourceCompiledGWord.effect (inventoryBound runtime + 1) word
    (SourceConditionalNativePosterior.decoder runtime
      (SourceWordObservedCode.readAt (inventoryBound runtime) word) key)

theorem gBest_conditional_mean (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1))) (actor : Actors runtime) :
    SourceVectorMoment.mean
      (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
        (SourceWordObservedCode.sourceQuery runtime word)
        (SourceWordObservedCode.sourceQuery runtime word actor)
        (SourceWeightedRecovery.observed_supported _ _ actor
          (SourceUniformFibreVariance.source_positive _ actor)))
      (SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word) =
        gBest runtime word (SourceWordObservedCode.sourceQuery runtime word actor) := by
  have query : SourceWordObservedCode.sourceQuery runtime word =
      fun actor : Actors runtime =>
        SourceWordObservedCode.readAt (inventoryBound runtime) word actor.val := by
    funext actor
    exact SourceWordObservedCode.source_query_read runtime word actor
  rw [query]
  exact SourceCompiledGWord.conditional_decoder runtime
    (inventoryBound runtime + 1) word
    (SourceWordObservedCode.readAt (inventoryBound runtime) word)
    (SourceWordObservedCode.readAt (inventoryBound runtime) word actor.val)
    (SourceWeightedRecovery.observed_supported _ _ actor
      (SourceUniformFibreVariance.source_positive _ actor))

theorem gBest_effect_mean (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1))) (actor : Actors runtime) :
    SourceCompiledGWord.effect (inventoryBound runtime + 1) word
      (SourceVectorMoment.mean
        (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
          (SourceWordObservedCode.sourceQuery runtime word)
          (SourceWordObservedCode.sourceQuery runtime word actor)
          (SourceWeightedRecovery.observed_supported _ _ actor
            (SourceUniformFibreVariance.source_positive _ actor)))
        (SourceConditionalInventory.values (inventoryBound runtime))) =
      gBest runtime word (SourceWordObservedCode.sourceQuery runtime word actor) := by
  rw [← SourceCompiledGWord.mean_effect]
  simpa only [SourceCompiledGWord.image_original, Function.comp_apply] using
    gBest_conditional_mean runtime word actor

/-- The G-space decoder bias is the exact unpaid part of the original risk. -/
theorem gBest_risk_decomposition (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    SourceWordCodeRisk.risk runtime word
      (SourceWordObservedCode.encodeObserved runtime word) decoder =
    SourceWordCodeRisk.risk runtime word
      (SourceWordObservedCode.encodeObserved runtime word) (gBest runtime word) +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖gBest runtime word (SourceWordObservedCode.sourceQuery runtime word actor) -
          decoder (SourceWordObservedCode.sourceQuery runtime word actor)‖ ^ 2 := by
  have arbitrary := SourceWordCodeRisk.risk_account runtime word
    (SourceWordObservedCode.encodeObserved runtime word) decoder
  have optimal := SourceWordCodeRisk.risk_account runtime word
    (SourceWordObservedCode.encodeObserved runtime word) (gBest runtime word)
  rw [SourceWordObservedCode.query_source] at arbitrary optimal
  simp_rw [gBest_effect_mean] at arbitrary optimal
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero] at optimal
  rw [arbitrary, optimal]

theorem gBest_risk_le (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    SourceWordCodeRisk.risk runtime word
      (SourceWordObservedCode.encodeObserved runtime word) (gBest runtime word) ≤
      SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) decoder := by
  rw [gBest_risk_decomposition runtime word decoder]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

def gTotal (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1))) : ℝ :=
  ((inventoryBound runtime + 1 : Nat) : ℝ) *
    SourceWordCodeRisk.risk runtime word
      (SourceWordObservedCode.encodeObserved runtime word) (gBest runtime word)

theorem gBest_count_decomposition (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    ((inventoryBound runtime + 1 : Nat) : ℝ) *
      SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) decoder =
      gTotal runtime word +
        ∑ actor : Actors runtime,
          ‖gBest runtime word (SourceWordObservedCode.sourceQuery runtime word actor) -
            decoder (SourceWordObservedCode.sourceQuery runtime word actor)‖ ^ 2 := by
  have paid := congrArg
    (fun amount : ℝ => ((inventoryBound runtime + 1 : Nat) : ℝ) * amount)
    (gBest_risk_decomposition runtime word decoder)
  rw [mul_add, SourceConditionalInventory.sum_count] at paid
  exact paid

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
