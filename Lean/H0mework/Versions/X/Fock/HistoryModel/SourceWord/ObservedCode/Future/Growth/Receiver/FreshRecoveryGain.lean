import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Future.Growth.NoFreeBirth
import H0mework.Versions.X.Fock.HistoryModel.CoarseCode.ActionRefinement

/-!
# The newly legal material bit strictly improves the original physical G recovery

At d3 the transported old letter reads zero, while the new material letter
separates two original actors. Both codes are applied to the same new-letter
G task and the same source history weights. The existing conditional
refinement equation gives an exact positive optimal-risk difference.
-/

set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordFreshRecoveryGain

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime

noncomputable section

def freshRead : Nat → ZMod 2 :=
  SourceWordObservedCode.readAt (inventoryBound (runtimeAt 3))
    (SourceWordFreshReceiver.freshWord 3)

def forget : ZMod 2 → ZMod 2 := fun _ => 0

theorem fine_diff : freshRead 0 ≠ freshRead 1 := by
  have h := SourceWordFutureBitGrowth.freshAtThree_separates
  simp only [SourceWordObservedCode.source_query_read] at h
  exact h

theorem gain_pos :
    0 < SourceWordFieldCode.gGap (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) freshRead forget := by
  have sourceGap : 0 < SourceConditionalMergeLoss.gap (runtimeAt 3)
      freshRead forget := by
    apply SourceConditionalMergeLoss.gap_positive_of_collision
      (runtimeAt 3) freshRead forget
      (⟨0, by decide⟩ : Actors (runtimeAt 3))
      (⟨1, by decide⟩ : Actors (runtimeAt 3))
    · rfl
    · exact fine_diff
  have nonzero : SourceWordFieldCode.gGap (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) freshRead forget ≠ 0 := by
    intro zero
    exact (ne_of_gt sourceGap) ((SourceWordFieldCode.gGap_zero_iff_source_gap
      (runtimeAt 3) (SourceWordFreshReceiver.freshWord 3) freshRead forget).mp zero)
  exact lt_of_le_of_ne
    (SourceWordFieldCode.gGap_nonnegative (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) freshRead forget)
    (Ne.symm nonzero)

theorem info_pos :
    0 < SourceConditionalInformationLoss.amount (runtimeAt 3) freshRead forget := by
  apply (SourceConditionalInformationLoss.amount_positive_iff_gap
    (runtimeAt 3) freshRead forget).mpr
  apply SourceConditionalMergeLoss.gap_positive_of_collision
    (runtimeAt 3) freshRead forget
    (⟨0, by decide⟩ : Actors (runtimeAt 3))
    (⟨1, by decide⟩ : Actors (runtimeAt 3))
  · rfl
  · exact fine_diff

def coarseDecoder : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gCoarseMean (runtimeAt 3)
    (SourceWordFreshReceiver.freshWord 3) freshRead forget

def fineDecoder : ZMod 2 → SourceJointClockGraph.Carrier :=
  SourceWordFieldCode.gFineMean (runtimeAt 3)
    (SourceWordFreshReceiver.freshWord 3) freshRead

theorem fine_risk_eq :
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      (SourceWordObservedCode.encodeObserved (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3)) fineDecoder =
    SourceWordFieldCode.gRisk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) freshRead fineDecoder := by
  rw [SourceWordCodeRisk.risk_eq]
  unfold SourceWordFieldCode.gRisk
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceWordObservedCode.query_actual]
  rfl

theorem coarse_risk_eq :
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      SourceWordFutureBitGrowth.carriedCode coarseDecoder =
    SourceWordFieldCode.gRisk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) (forget ∘ freshRead) coarseDecoder := by
  rw [SourceWordCodeRisk.risk_eq]
  unfold SourceWordFieldCode.gRisk
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceWordFutureBitGrowth.carriedCode_query]
  rfl

theorem actual_gain :
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      SourceWordFutureBitGrowth.carriedCode coarseDecoder =
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      (SourceWordObservedCode.encodeObserved (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3)) fineDecoder +
    SourceWordFieldCode.gGap (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3) freshRead forget := by
  rw [coarse_risk_eq, fine_risk_eq]
  exact SourceWordFieldCode.gRisk_refinement
    (runtimeAt 3) (SourceWordFreshReceiver.freshWord 3) freshRead forget

theorem actual_gain_strict :
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      (SourceWordObservedCode.encodeObserved (runtimeAt 3)
        (SourceWordFreshReceiver.freshWord 3)) fineDecoder <
    SourceWordCodeRisk.risk (runtimeAt 3)
      (SourceWordFreshReceiver.freshWord 3)
      SourceWordFutureBitGrowth.carriedCode coarseDecoder := by
  rw [actual_gain]
  exact lt_add_of_pos_right _ gain_pos

end
end SourceWordFreshRecoveryGain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
