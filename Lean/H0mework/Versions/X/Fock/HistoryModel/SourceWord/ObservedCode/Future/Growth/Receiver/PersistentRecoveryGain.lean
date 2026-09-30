import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.Receiver.PersistentMaterial
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRefinement

/-!
# Exact physical G recovery gain at every later source visit

The original d2 and d3 letters are read at each generated inventory. For
the same transported d3 G task and actual history weights, replacing the
erased old code with the source-retained new code lowers optimal risk by
the strictly positive conditional G gap.
-/

set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordPersistentRecoveryGain

open SourceGeneratedActionWords
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

open SourceWordPersistentMaterial

noncomputable section

def fineRead (offset : Nat) : Nat → ZMod 2 :=
  SourceWordObservedCode.readAt (inventoryBound (runtimeAt (depth offset)))
    (freshWord offset)

def forget : ZMod 2 → ZMod 2 := fun _ => 0

theorem fine_diff (offset : Nat) : fineRead offset 0 ≠ fineRead offset 1 := by
  have h := fresh_word_separates offset
  simpa only [SourceWordObservedCode.source_query_read, fineRead,
    actorZero, actorOne] using h

theorem gain_pos (offset : Nat) :
    0 < SourceWordFieldCode.gGap (runtimeAt (depth offset))
      (freshWord offset) (fineRead offset) forget := by
  have sourceGap : 0 < SourceConditionalMergeLoss.gap
      (runtimeAt (depth offset)) (fineRead offset) forget := by
    apply SourceConditionalMergeLoss.gap_positive_of_collision
      (runtimeAt (depth offset)) (fineRead offset) forget
      (actorZero offset) (actorOne offset)
    · rfl
    · exact fine_diff offset
  have nonzero : SourceWordFieldCode.gGap (runtimeAt (depth offset))
      (freshWord offset) (fineRead offset) forget ≠ 0 := by
    intro zero
    exact (ne_of_gt sourceGap) ((SourceWordFieldCode.gGap_zero_iff_source_gap
      (runtimeAt (depth offset)) (freshWord offset) (fineRead offset) forget).mp zero)
  exact lt_of_le_of_ne
    (SourceWordFieldCode.gGap_nonnegative
      (runtimeAt (depth offset)) (freshWord offset) (fineRead offset) forget)
    (Ne.symm nonzero)

theorem info_pos (offset : Nat) :
    0 < SourceConditionalInformationLoss.amount
      (runtimeAt (depth offset)) (fineRead offset) forget := by
  apply (SourceConditionalInformationLoss.amount_positive_iff_gap
    (runtimeAt (depth offset)) (fineRead offset) forget).mpr
  apply SourceConditionalMergeLoss.gap_positive_of_collision
    (runtimeAt (depth offset)) (fineRead offset) forget
    (actorZero offset) (actorOne offset)
  · rfl
  · exact fine_diff offset

def oldCode (offset : Nat) :
    SourceWordMinimalCode.WordImage
      (runtimeAt (depth offset)) (freshWord offset) → ZMod 2 :=
  fun code => SourceWordObservedCode.sourceQuery
    (runtimeAt (depth offset)) (oldWord offset)
    ((SourceWordMinimalCode.wordEquiv
      (runtimeAt (depth offset)) (freshWord offset)).symm code)

theorem oldCode_query (offset : Nat)
    (actor : Actors (runtimeAt (depth offset))) :
    SourceWordCodeRisk.query (runtimeAt (depth offset))
      (freshWord offset) (oldCode offset) actor = 0 := by
  simpa only [SourceWordCodeRisk.query, oldCode,
    Equiv.symm_apply_apply] using old_word_zero offset actor

def coarseDecoder (offset : Nat) : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gCoarseMean (runtimeAt (depth offset))
    (freshWord offset) (fineRead offset) forget

def fineDecoder (offset : Nat) : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gFineMean (runtimeAt (depth offset))
    (freshWord offset) (fineRead offset)

theorem bit_risk_eq_gRisk_of_query_eq
    (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (encode : SourceWordMinimalCode.WordImage runtime word → ZMod 2)
    (read : Nat → ZMod 2)
    (decoder : ZMod 2 → SourceJointClockGraph.Carrier)
    (query_eq : ∀ actor : Actors runtime,
      SourceWordCodeRisk.query runtime word encode actor = read actor.val) :
    SourceWordCodeRisk.risk runtime word encode decoder =
      SourceWordFieldCode.gRisk runtime word read decoder := by
  rw [SourceWordCodeRisk.risk_eq]
  unfold SourceWordFieldCode.gRisk
  apply Finset.sum_congr rfl
  intro actor _
  rw [query_eq actor]
  rfl

theorem fine_risk_eq (offset : Nat) :
    SourceWordCodeRisk.risk (runtimeAt (depth offset)) (freshWord offset)
      (SourceWordObservedCode.encodeObserved
        (runtimeAt (depth offset)) (freshWord offset))
      (fineDecoder offset) =
    SourceWordFieldCode.gRisk (runtimeAt (depth offset)) (freshWord offset)
      (fineRead offset) (fineDecoder offset) := by
  apply bit_risk_eq_gRisk_of_query_eq
  intro actor
  rw [SourceWordObservedCode.query_actual]
  rfl

theorem coarse_risk_eq (offset : Nat) :
    SourceWordCodeRisk.risk (runtimeAt (depth offset)) (freshWord offset)
      (oldCode offset) (coarseDecoder offset) =
    SourceWordFieldCode.gRisk (runtimeAt (depth offset)) (freshWord offset)
      (forget ∘ fineRead offset) (coarseDecoder offset) := by
  apply bit_risk_eq_gRisk_of_query_eq
  intro actor
  rw [oldCode_query]
  rfl

theorem actual_gain (offset : Nat) :
    SourceWordCodeRisk.risk (runtimeAt (depth offset)) (freshWord offset)
      (oldCode offset) (coarseDecoder offset) =
    SourceWordCodeRisk.risk (runtimeAt (depth offset)) (freshWord offset)
      (SourceWordObservedCode.encodeObserved
        (runtimeAt (depth offset)) (freshWord offset))
      (fineDecoder offset) +
    SourceWordFieldCode.gGap (runtimeAt (depth offset))
      (freshWord offset) (fineRead offset) forget := by
  rw [coarse_risk_eq, fine_risk_eq]
  exact SourceWordFieldCode.gRisk_refinement
    (runtimeAt (depth offset)) (freshWord offset) (fineRead offset) forget

theorem actual_gain_strict (offset : Nat) :
    SourceWordCodeRisk.risk (runtimeAt (depth offset)) (freshWord offset)
      (SourceWordObservedCode.encodeObserved
        (runtimeAt (depth offset)) (freshWord offset))
      (fineDecoder offset) <
    SourceWordCodeRisk.risk (runtimeAt (depth offset)) (freshWord offset)
      (oldCode offset) (coarseDecoder offset) := by
  rw [actual_gain]
  exact lt_add_of_pos_right _ (gain_pos offset)

theorem nonunitAt (offset : Nat) :
    (SourceCopyCurrentCoordinates.maximumIndex
      (runtimeAt (depth offset))).val ≠ 0 := by
  have same : depth offset = (2 + offset) + 1 := by
    dsimp [depth]
    omega
  rw [same]
  exact SourceWordFutureBitGrowth.nextNonunit (2 + offset)


end
end SourceWordPersistentRecoveryGain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
