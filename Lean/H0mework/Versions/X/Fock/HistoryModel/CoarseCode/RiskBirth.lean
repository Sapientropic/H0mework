import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.BirthRecovery
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.GImageBirth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem original_acted_g_risk_count (runtime : LivingRuntimeState process)
    (word : List (Letter (inventoryBound runtime + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    ((inventoryBound runtime + 1 : Nat) : ℝ) *
      SourceWordCodeRisk.risk runtime word
        (SourceWordObservedCode.encodeObserved runtime word) decoder =
      ∑ actor : Actors runtime,
        ‖SourceCompiledGWord.image runtime (inventoryBound runtime + 1) word actor -
          decoder (SourceWordObservedCode.sourceQuery runtime word actor)‖ ^ 2 := by
  rw [SourceWordCodeRisk.risk_eq]
  simp only [SourceWordObservedCode.query_actual]
  exact SourceConditionalInventory.sum_count _ _

theorem original_acted_g_risk_native_birth (depth : Nat)
    (word : List (Letter (depth + 1)))
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    ((depth + 2 : Nat) : ℝ) *
        SourceWordCodeRisk.risk (runtimeAt (depth + 1))
          (SourceWordFutureBitGrowth.nextWordAt depth word)
          (SourceWordObservedCode.encodeObserved (runtimeAt (depth + 1))
            (SourceWordFutureBitGrowth.nextWordAt depth word)) decoder =
      ((depth + 1 : Nat) : ℝ) *
        SourceWordCodeRisk.risk (runtimeAt depth)
          (SourceWordFutureBitGrowth.oldWordAt depth word)
          (SourceWordObservedCode.encodeObserved (runtimeAt depth)
            (SourceWordFutureBitGrowth.oldWordAt depth word)) decoder +
      ‖SourceCompiledGWord.image (runtimeAt (depth + 1))
          (inventoryBound (runtimeAt (depth + 1)) + 1)
          (SourceWordFutureBitGrowth.nextWordAt depth word)
          (Fin.last (inventoryBound (runtimeAt (depth + 1)))) -
        decoder (SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
          (SourceWordFutureBitGrowth.nextWordAt depth word)
          (Fin.last (inventoryBound (runtimeAt (depth + 1)))))‖ ^ 2 := by
  have nextCount := original_acted_g_risk_count (runtimeAt (depth + 1))
    (SourceWordFutureBitGrowth.nextWordAt depth word) decoder
  have oldCount := original_acted_g_risk_count (runtimeAt depth)
    (SourceWordFutureBitGrowth.oldWordAt depth word) decoder
  have hnextBound : ((depth + 2 : Nat) : ℝ) =
      ((inventoryBound (runtimeAt (depth + 1)) + 1 : Nat) : ℝ) := by
    simp only [SourceConditionalInventory.runtime_bound]
  have holdBound : ((depth + 1 : Nat) : ℝ) =
      ((inventoryBound (runtimeAt depth) + 1 : Nat) : ℝ) := by
    simp only [SourceConditionalInventory.runtime_bound]
  rw [hnextBound, holdBound]
  rw [nextCount, oldCount]
  rw [Fin.sum_univ_castSucc]
  rw [SourceCompiledGWord.old_actor_error_sum_native_birth]

theorem actual_copy_g_risk_native_birth
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier) :
    (5 : ℝ) * SourceWordCodeRisk.risk (runtimeAt 4)
        (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
        (SourceWordObservedCode.encodeObserved (runtimeAt 4)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])) decoder =
      (4 : ℝ) * SourceWordCodeRisk.risk (runtimeAt 3)
        (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])
        (SourceWordObservedCode.encodeObserved (runtimeAt 3)
          (SourceWordFutureBitGrowth.oldWordAt 3 [SourceWordDynamicNext.copyOne])) decoder +
      ‖SourceCompiledGWord.image (runtimeAt 4)
          (inventoryBound (runtimeAt 4) + 1)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
          (Fin.last (inventoryBound (runtimeAt 4))) -
        decoder (SourceWordObservedCode.sourceQuery (runtimeAt 4)
          (SourceWordFutureBitGrowth.nextWordAt 3 [SourceWordDynamicNext.copyOne])
          (Fin.last (inventoryBound (runtimeAt 4))))‖ ^ 2 := by
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using
    original_acted_g_risk_native_birth 3 [SourceWordDynamicNext.copyOne] decoder

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
