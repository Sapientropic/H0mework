import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.OptimalRiskBirth.Source
import H0mework.Versions.X.Fock.HistoryConditional.NativeBirthInnovation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFieldCode

open SourceGeneratedActionWords.Fock
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem gBest_native_birth (depth : Nat) (word : List (Letter (depth + 1)))
    (key : ZMod 2) :
    gBest (runtimeAt (depth + 1)) (SourceWordFutureBitGrowth.nextWordAt depth word) key =
      if key = SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
          (SourceWordFutureBitGrowth.oldWordAt depth word)
          (inventoryBound (runtimeAt depth) + 1) then
        gBest (runtimeAt depth) (SourceWordFutureBitGrowth.oldWordAt depth word) key +
          ((((SourceConditionalNativeObservers.generate
            (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
              (SourceWordFutureBitGrowth.oldWordAt depth word))
            (inventoryBound (runtimeAt depth)) key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) •
            (SourceCompiledGWord.effect (inventoryBound (runtimeAt depth) + 1)
              (SourceWordFutureBitGrowth.oldWordAt depth word)
              (SourceConditionalInventory.born (inventoryBound (runtimeAt depth))) -
              gBest (runtimeAt depth) (SourceWordFutureBitGrowth.oldWordAt depth word) key)
      else gBest (runtimeAt depth) (SourceWordFutureBitGrowth.oldWordAt depth word) key := by
  have sameRead :
      SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth + 1)))
          (SourceWordFutureBitGrowth.nextWordAt depth word) =
        SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
          (SourceWordFutureBitGrowth.oldWordAt depth word) := by
    funext index
    exact SourceWordFutureBitGrowth.old_next_read_at depth word index
  unfold gBest
  rw [SourceCompiledGWord.effect_native_birth depth word, sameRead,
    SourceWordFutureBitGrowth.next_runtime,
    SourceConditionalNativeBirth.decoder_next]
  by_cases selected : key = SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      (SourceWordFutureBitGrowth.oldWordAt depth word)
      (inventoryBound (runtimeAt depth) + 1)
  · simp only [if_pos selected, map_add, map_smul, map_sub, Rat.cast_natCast]
  · simp only [if_neg selected]

theorem gBorn_native_birth (depth : Nat) (word : List (Letter (depth + 1))) :
    SourceCompiledGWord.image (runtimeAt (depth + 1))
      (inventoryBound (runtimeAt (depth + 1)) + 1)
      (SourceWordFutureBitGrowth.nextWordAt depth word)
      (Fin.last (inventoryBound (runtimeAt (depth + 1)))) =
    SourceCompiledGWord.effect (inventoryBound (runtimeAt depth) + 1)
      (SourceWordFutureBitGrowth.oldWordAt depth word)
      (SourceConditionalInventory.born (inventoryBound (runtimeAt depth))) := by
  rw [SourceCompiledGWord.image_original,
    SourceCompiledGWord.effect_native_birth depth word]
  simp only [Function.comp_apply, SourceConditionalInventory.born]
  rw [SourceCompiledGWord.inventory_bound_native_birth depth]

theorem gBornKey_native_birth (depth : Nat) (word : List (Letter (depth + 1))) :
    SourceWordObservedCode.sourceQuery (runtimeAt (depth + 1))
      (SourceWordFutureBitGrowth.nextWordAt depth word)
      (Fin.last (inventoryBound (runtimeAt (depth + 1)))) =
    SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      (SourceWordFutureBitGrowth.oldWordAt depth word)
      (inventoryBound (runtimeAt depth) + 1) := by
  rw [SourceWordObservedCode.source_query_read, Fin.val_last,
    SourceWordFutureBitGrowth.old_next_read_at,
    SourceCompiledGWord.inventory_bound_native_birth]

theorem gBest_native_birth_bias (depth : Nat) (word : List (Letter (depth + 1))) :
    (∑ actor : Actors (runtimeAt depth),
      ‖gBest (runtimeAt depth) (SourceWordFutureBitGrowth.oldWordAt depth word)
          (SourceWordObservedCode.sourceQuery (runtimeAt depth)
            (SourceWordFutureBitGrowth.oldWordAt depth word) actor) -
        gBest (runtimeAt (depth + 1)) (SourceWordFutureBitGrowth.nextWordAt depth word)
          (SourceWordObservedCode.sourceQuery (runtimeAt depth)
            (SourceWordFutureBitGrowth.oldWordAt depth word) actor)‖ ^ 2) =
    ((SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (SourceWordFutureBitGrowth.oldWordAt depth word))
      (inventoryBound (runtimeAt depth))
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (SourceWordFutureBitGrowth.oldWordAt depth word)
        (inventoryBound (runtimeAt depth) + 1))).1 : ℝ) *
      ‖gBest (runtimeAt depth) (SourceWordFutureBitGrowth.oldWordAt depth word)
          (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
            (SourceWordFutureBitGrowth.oldWordAt depth word)
            (inventoryBound (runtimeAt depth) + 1)) -
        gBest (runtimeAt (depth + 1)) (SourceWordFutureBitGrowth.nextWordAt depth word)
          (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
            (SourceWordFutureBitGrowth.oldWordAt depth word)
            (inventoryBound (runtimeAt depth) + 1))‖ ^ 2 := by
  let read := SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
    (SourceWordFutureBitGrowth.oldWordAt depth word)
  let bornKey := read (inventoryBound (runtimeAt depth) + 1)
  have count := congrArg (fun value : Nat => (value : ℝ))
    (SourceConditionalNativePosterior.count_sum read
      (inventoryBound (runtimeAt depth)) bornKey)
  push_cast at count
  rw [count, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceWordObservedCode.source_query_read]
  by_cases same : read actor.val = bornKey
  · dsimp only [read, bornKey] at same
    dsimp only [read, bornKey]
    simp only [if_pos same, one_mul]
    rw [same]
  · dsimp only [read, bornKey] at same
    rw [gBest_native_birth depth word
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (SourceWordFutureBitGrowth.oldWordAt depth word) actor.val), if_neg same,
      sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), if_neg same, zero_mul]

private theorem gTotal_native_birth_split (depth : Nat) (word : List (Letter (depth + 1))) :
    let oldWord := SourceWordFutureBitGrowth.oldWordAt depth word
    let nextWord := SourceWordFutureBitGrowth.nextWordAt depth word
    let bornKey := SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      oldWord (inventoryBound (runtimeAt depth) + 1)
    let count := (SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth)) oldWord)
      (inventoryBound (runtimeAt depth)) bornKey).1
    gTotal (runtimeAt (depth + 1)) nextWord =
      gTotal (runtimeAt depth) oldWord +
        (count : ℝ) *
          ‖gBest (runtimeAt depth) oldWord bornKey -
            gBest (runtimeAt (depth + 1)) nextWord bornKey‖ ^ 2 +
        ‖SourceCompiledGWord.image (runtimeAt (depth + 1))
            (inventoryBound (runtimeAt (depth + 1)) + 1) nextWord
            (Fin.last (inventoryBound (runtimeAt (depth + 1)))) -
          gBest (runtimeAt (depth + 1)) nextWord bornKey‖ ^ 2 := by
  dsimp only
  have birth := original_acted_g_risk_native_birth depth word
    (gBest (runtimeAt (depth + 1)) (SourceWordFutureBitGrowth.nextWordAt depth word))
  have decomp := gBest_count_decomposition (runtimeAt depth)
    (SourceWordFutureBitGrowth.oldWordAt depth word)
    (gBest (runtimeAt (depth + 1)) (SourceWordFutureBitGrowth.nextWordAt depth word))
  rw [gBest_native_birth_bias depth word] at decomp
  rw [gBornKey_native_birth depth word] at birth
  simp only [SourceConditionalInventory.runtime_bound] at decomp
  calc
    gTotal (runtimeAt (depth + 1))
        (SourceWordFutureBitGrowth.nextWordAt depth word) =
      ((depth + 1 : Nat) : ℝ) *
        SourceWordCodeRisk.risk (runtimeAt depth)
          (SourceWordFutureBitGrowth.oldWordAt depth word)
          (SourceWordObservedCode.encodeObserved (runtimeAt depth)
            (SourceWordFutureBitGrowth.oldWordAt depth word))
          (gBest (runtimeAt (depth + 1))
            (SourceWordFutureBitGrowth.nextWordAt depth word)) +
      ‖SourceCompiledGWord.image (runtimeAt (depth + 1))
          (inventoryBound (runtimeAt (depth + 1)) + 1)
          (SourceWordFutureBitGrowth.nextWordAt depth word)
          (Fin.last (inventoryBound (runtimeAt (depth + 1)))) -
        gBest (runtimeAt (depth + 1))
          (SourceWordFutureBitGrowth.nextWordAt depth word)
          (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
            (SourceWordFutureBitGrowth.oldWordAt depth word)
            (inventoryBound (runtimeAt depth) + 1))‖ ^ 2 := by
        simpa only [gTotal, SourceConditionalInventory.runtime_bound,
          Nat.add_assoc, Nat.reduceAdd] using birth
    _ = _ := by
      rw [decomp]
      simp only [SourceConditionalInventory.runtime_bound]

/-- Reoptimizing the original acted G decoder costs exactly the born fibre's
    Hilbert innovation, with count read from the same source history. -/
theorem gTotal_native_birth (depth : Nat) (word : List (Letter (depth + 1))) :
    let oldWord := SourceWordFutureBitGrowth.oldWordAt depth word
    let nextWord := SourceWordFutureBitGrowth.nextWordAt depth word
    let bornKey := SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      oldWord (inventoryBound (runtimeAt depth) + 1)
    let count := (SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth)) oldWord)
      (inventoryBound (runtimeAt depth)) bornKey).1
    gTotal (runtimeAt (depth + 1)) nextWord =
      gTotal (runtimeAt depth) oldWord +
        (count : ℝ) / (count + 1) *
          ‖SourceCompiledGWord.image (runtimeAt (depth + 1))
              (inventoryBound (runtimeAt (depth + 1)) + 1) nextWord
              (Fin.last (inventoryBound (runtimeAt (depth + 1)))) -
            gBest (runtimeAt depth) oldWord bornKey‖ ^ 2 := by
  dsimp only
  have split := gTotal_native_birth_split depth word
  dsimp only at split
  have update := gBest_native_birth depth word
    (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
      (SourceWordFutureBitGrowth.oldWordAt depth word)
      (inventoryBound (runtimeAt depth) + 1))
  rw [if_pos rfl] at update
  rw [update] at split
  rw [gBorn_native_birth] at split ⊢
  simp only [Rat.cast_natCast] at split
  have energy := SourceConditionalNativeBirth.mean_update_energy
    (SourceConditionalNativeObservers.generate
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (SourceWordFutureBitGrowth.oldWordAt depth word))
      (inventoryBound (runtimeAt depth))
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (SourceWordFutureBitGrowth.oldWordAt depth word)
        (inventoryBound (runtimeAt depth) + 1))).1
    (gBest (runtimeAt depth) (SourceWordFutureBitGrowth.oldWordAt depth word)
      (SourceWordObservedCode.readAt (inventoryBound (runtimeAt depth))
        (SourceWordFutureBitGrowth.oldWordAt depth word)
        (inventoryBound (runtimeAt depth) + 1)))
    (SourceCompiledGWord.effect (inventoryBound (runtimeAt depth) + 1)
      (SourceWordFutureBitGrowth.oldWordAt depth word)
      (SourceConditionalInventory.born (inventoryBound (runtimeAt depth))))
  linarith only [split, energy]

end
end SourceWordFieldCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
