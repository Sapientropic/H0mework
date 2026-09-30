import H0mework.Versions.X.Fock.HistoryModel.SourceWord.CodeRisk

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordObservedCode

open SourceGeneratedActionWords SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def observe (current : Current) : ZMod 2 := scanIndex current

def sourceQuery (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) : ZMod 2 :=
  observe (SourceWordMinimalCode.executed runtime word actor)

def readAt (depth : Nat) (word : List (Fock.Letter (depth + 1)))
    (index : Nat) : ZMod 2 :=
  observe (Fock.actualWord (depth + 1) word
    (nativeStep ((runtimeAt index).current.visit.current : Current)))

theorem source_query_read (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    sourceQuery runtime word actor = readAt (inventoryBound runtime) word actor.val := by
  rfl

def postWordLaw (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) : PMF (ZMod 2) :=
  ((((Fock.sourceLaw (inventoryBound runtime)).map nativeStep).map
    (Fock.actualWord (inventoryBound runtime + 1) word)).map observe)

theorem post_word_law (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    postWordLaw runtime word =
      (historyPMF (inventoryBound runtime)).map (sourceQuery runtime word) := by
  unfold postWordLaw sourceQuery SourceWordMinimalCode.executed
  rw [Fock.nativeLaw_next]
  rw [PMF.map_comp]
  have composed := PMF.map_comp
    (fun actor : Actors runtime =>
      (((history runtimeSeed (inventoryBound runtime)).stageAt actor).next.current.visit.current : Current))
    (historyPMF (inventoryBound runtime))
    (fun current : Current => observe (Fock.actualWord (inventoryBound runtime + 1) word current))
  exact composed.trans (by rfl)

def encodeObserved (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    SourceWordMinimalCode.WordImage runtime word → ZMod 2 :=
  fun code => sourceQuery runtime word ((SourceWordMinimalCode.wordEquiv runtime word).symm code)

theorem query_actual (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (actor : Actors runtime) :
    SourceWordCodeRisk.query runtime word (encodeObserved runtime word) actor =
      sourceQuery runtime word actor := by
  simp only [SourceWordCodeRisk.query, encodeObserved, Equiv.symm_apply_apply]

theorem query_source (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    SourceWordCodeRisk.query runtime word (encodeObserved runtime word) =
      sourceQuery runtime word := by
  funext actor
  exact query_actual runtime word actor

theorem post_word_code_law (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    postWordLaw runtime word =
      (historyPMF (inventoryBound runtime)).map
        (SourceWordCodeRisk.query runtime word (encodeObserved runtime word)) := by
  rw [post_word_law, query_source]

theorem observed_information_risk (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    ((inventoryBound runtime + 1 : ℝ) - Fintype.card (ZMod 2)) /
        (inventoryBound runtime + 1 : ℝ) +
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 *
        ((Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
          (inventoryBound runtime) (sourceQuery runtime word)) - 1) / 12) ≤
      SourceWordCodeRisk.risk runtime word (encodeObserved runtime word) decoder := by
  simpa only [query_source] using
    (SourceWordCodeRisk.code_information_risk runtime word (encodeObserved runtime word) decoder)

theorem actual_observed_short_risk
    (word : List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    0 < SourceWordCodeRisk.risk (runtimeAt 3) word
      (encodeObserved (runtimeAt 3) word) decoder := by
  apply SourceWordCodeRisk.deficit_positive
  rw [inventory_bound, runtimeAt_state]
  decide

theorem actual_observed_half_risk
    (word : List (Fock.Letter (inventoryBound (runtimeAt 3) + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    (1 / 2 : ℝ) ≤ SourceWordCodeRisk.risk (runtimeAt 3) word
      (encodeObserved (runtimeAt 3) word) decoder := by
  have h := observed_information_risk (runtimeAt 3) word decoder
  have hEnt := SourceWordCodeRisk.entropy_nonnegative (runtimeAt 3) word
    (encodeObserved (runtimeAt 3) word)
  rw [query_source] at hEnt
  have hExp : 0 ≤
      (Real.exp (2 * SourceUniformFibreInformation.conditionalEntropy
        (inventoryBound (runtimeAt 3)) (sourceQuery (runtimeAt 3) word)) - 1) / 12 := by
    have h := Real.add_one_le_exp (2 * SourceUniformFibreInformation.conditionalEntropy
      (inventoryBound (runtimeAt 3)) (sourceQuery (runtimeAt 3) word))
    nlinarith
  have hSlope : 0 ≤
      ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 : ℝ) ^ 2 :=
    sq_nonneg _
  have hCard : Fintype.card (ZMod 2) = 2 := by decide
  have hN : inventoryBound (runtimeAt 3) = 3 := by
    rw [inventory_bound, runtimeAt_state]
  have hMargin :
      ((inventoryBound (runtimeAt 3) + 1 : ℝ) - Fintype.card (ZMod 2)) /
        (inventoryBound (runtimeAt 3) + 1 : ℝ) = 1 / 2 := by
    rw [hN, hCard]
    norm_num
  rw [hMargin] at h
  nlinarith [mul_nonneg hSlope hExp]

end
end SourceWordObservedCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
