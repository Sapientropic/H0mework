import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition

/-!
# Exact finite recognition threshold

A fair stage recognizes an emitted paid replay exactly when the replay depth
is below that stage.  Hence `depth + 1` is the least recognition stage,
recognition persists thereafter, and every earlier stage has a concrete paid
occurrence/K counterexample.

This is a source-relative threshold law, not a global stopping schedule or a
completed observer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition

/-- Relational occurrence recognition at one finite stage. -/
def CanonicalPaidReplayFairOccurrenceRecognizesAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Prop :=
  ∀ candidate :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage replay →
      candidate = replay

/-- Relational actual-service authority recognition at one finite stage. -/
def CanonicalPaidReplayFairAuthorityRecognizesAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Prop :=
  ∀ candidate :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage replay →
      candidate.2.authorityK = replay.2.authorityK

/-- Canonical paid candidate immediately after the replay's own depth. -/
def canonicalPaidReplayFairPrethresholdCandidate
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    (replay.1 + 1)

/-- Every stage at or before the replay depth receives a concrete paid kernel
candidate.  The candidate keeps its actual Payment and canonical-next seams. -/
theorem canonicalPaidReplayFairBeforeThreshold_generatesKernel
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (stageLeDepth : stage ≤ replay.1) :
    let candidate := canonicalPaidReplayFairPrethresholdCandidate replay
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage replay ∧
      candidate ≠ replay ∧
      candidate.2.authorityK ≠ replay.2.authorityK ∧
      type_of% candidate.2.paidStep_consumes_exactPayment ∧
      type_of% candidate.2.paymentNext_isCanonicalTarget := by
  let candidate := canonicalPaidReplayFairPrethresholdCandidate replay
  have visibleEquality :
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            candidate =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage replay := by
    funext bit
    have replayDepthNe : replay.1 ≠ bit.1 := by omega
    have candidateDepthNe : replay.1 + 1 ≠ bit.1 := by omega
    simp [candidate, canonicalPaidReplayFairPrethresholdCandidate,
      canonicalPaidReplayFairFiniteArchiveReadoutAt,
      contributionCapacityPostSettlementPaidReplayAt, replayDepthNe,
      candidateDepthNe]
  have occurrenceNe : candidate ≠ replay := by
    intro occurrenceEquality
    have depthEquality := congrArg Sigma.fst occurrenceEquality
    change replay.1 + 1 = replay.1 at depthEquality
    omega
  have authorityNe : candidate.2.authorityK ≠ replay.2.authorityK := by
    intro authorityEquality
    exact occurrenceNe
      (canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
        authorityEquality)
  exact
    ⟨visibleEquality,
      occurrenceNe,
      authorityNe,
      candidate.2.paidStep_consumes_exactPayment,
      candidate.2.paymentNext_isCanonicalTarget⟩

/-- Complete occurrence-recognition threshold. -/
theorem canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex stage
        replay ↔ replay.1 < stage := by
  constructor
  · intro recognizes
    by_contra depthNotLt
    have stageLeDepth : stage ≤ replay.1 := by omega
    let candidate := canonicalPaidReplayFairPrethresholdCandidate replay
    have kernel :=
      canonicalPaidReplayFairBeforeThreshold_generatesKernel oldVisit
        sourceIndex stage replay stageLeDepth
    exact kernel.2.1 (recognizes candidate kernel.1)
  · intro depthLt candidate archiveEquality
    have bitEquality := congrFun archiveEquality ⟨replay.1, depthLt⟩
    have depthEquality : candidate.1 = replay.1 := by
      simpa [canonicalPaidReplayFairFiniteArchiveReadoutAt] using bitEquality
    exact canonicalPaidReplay_eq_of_depth_eq candidate replay depthEquality

/-- Complete actual-service K-recognition threshold. -/
theorem canonicalPaidReplayFairAuthorityRecognitionThreshold_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex stage
        replay ↔ replay.1 < stage := by
  constructor
  · intro recognizes
    by_contra depthNotLt
    have stageLeDepth : stage ≤ replay.1 := by omega
    let candidate := canonicalPaidReplayFairPrethresholdCandidate replay
    have kernel :=
      canonicalPaidReplayFairBeforeThreshold_generatesKernel oldVisit
        sourceIndex stage replay stageLeDepth
    exact kernel.2.2.1 (recognizes candidate kernel.1)
  · intro depthLt candidate archiveEquality
    have occurrenceEquality :=
      (canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact oldVisit
        sourceIndex stage replay).2 depthLt candidate archiveEquality
    exact congrArg (fun paidReplay => paidReplay.2.authorityK)
      occurrenceEquality

/-- Complete stage classification for occurrence and actual-service K. -/
theorem canonicalPaidReplayFairRecognitionThreshold_exact
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    (CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex stage
        replay ↔ replay.1 < stage) ∧
      (CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex stage
        replay ↔ replay.1 < stage) :=
  ⟨canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact oldVisit
      sourceIndex stage replay,
    canonicalPaidReplayFairAuthorityRecognitionThreshold_exact oldVisit
      sourceIndex stage replay⟩

/-- `depth + 1` is the exact first occurrence-recognition stage. -/
theorem canonicalPaidReplayFairOccurrenceRecognitionStage_least_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex stage
        replay ↔ replay.1 + 1 ≤ stage := by
  rw [canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact]
  omega

/-- `depth + 1` is also the exact first K-recognition stage. -/
theorem canonicalPaidReplayFairAuthorityRecognitionStage_least_iff
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex stage
        replay ↔ replay.1 + 1 ≤ stage := by
  rw [canonicalPaidReplayFairAuthorityRecognitionThreshold_exact]
  omega

/-- The generated kernel directly refutes both recognition predicates before
the threshold. -/
theorem canonicalPaidReplayFairBeforeThreshold_notRecognizes
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (stageLeDepth : stage ≤ replay.1) :
    ¬ CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
        stage replay ∧
      ¬ CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
        stage replay := by
  let candidate := canonicalPaidReplayFairPrethresholdCandidate replay
  have kernel :=
    canonicalPaidReplayFairBeforeThreshold_generatesKernel oldVisit
      sourceIndex stage replay stageLeDepth
  exact
    ⟨fun recognizes => kernel.2.1 (recognizes candidate kernel.1),
      fun recognizes => kernel.2.2.1 (recognizes candidate kernel.1)⟩

/-- `depth + 1` is the exact least occurrence and K recognition stage. -/
theorem canonicalPaidReplayFairRecognitionStage_minimal
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
        (replay.1 + 1) replay ∧
      CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
        (replay.1 + 1) replay ∧
      (∀ stage,
        CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
              stage replay →
          replay.1 + 1 ≤ stage) ∧
      (∀ stage,
        CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
              stage replay →
          replay.1 + 1 ≤ stage) := by
  have exactAtSuccessor :=
    canonicalPaidReplayFairRecognitionThreshold_exact oldVisit sourceIndex
      (replay.1 + 1) replay
  exact
    ⟨exactAtSuccessor.1.2 (by omega),
      exactAtSuccessor.2.2 (by omega),
      fun stage recognizes => by
        have depthLt :=
          (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit
            sourceIndex stage replay).1.1 recognizes
        omega,
      fun stage recognizes => by
        have depthLt :=
          (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit
            sourceIndex stage replay).2.1 recognizes
        omega⟩

theorem canonicalPaidReplayFairOccurrenceRecognition_persistent
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {stage later : Nat} (stageLeLater : stage ≤ later)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex stage
        replay →
      CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex later
        replay := by
  intro recognizes
  have depthLtStage :=
    (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit sourceIndex
      stage replay).1.1 recognizes
  apply
    (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit sourceIndex
      later replay).1.2
  omega

theorem canonicalPaidReplayFairAuthorityRecognition_persistent
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {stage later : Nat} (stageLeLater : stage ≤ later)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex stage
        replay →
      CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex later
        replay := by
  intro recognizes
  have depthLtStage :=
    (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit sourceIndex
      stage replay).2.1 recognizes
  apply
    (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit sourceIndex
      later replay).2.2
  omega

/-- Every fixed stage has an internally generated replay which it cannot
recognize, with the exact prethreshold paid kernel retained. -/
theorem canonicalPaidReplayFairEveryStage_hasUnrecognizedReplay
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    ∃ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      ∃ stageLeDepth : stage ≤ replay.1,
        ¬ CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
            stage replay ∧
          ¬ CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
            stage replay ∧
          type_of%
            (canonicalPaidReplayFairBeforeThreshold_generatesKernel oldVisit
              sourceIndex stage replay stageLeDepth) := by
  let replay :=
    contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex stage
  have stageLeDepth : stage ≤ replay.1 := by
    simp [replay, contributionCapacityPostSettlementPaidReplayAt]
  have notRecognizes :=
    canonicalPaidReplayFairBeforeThreshold_notRecognizes oldVisit sourceIndex
      stage replay stageLeDepth
  exact
    ⟨replay,
      stageLeDepth,
      notRecognizes.1,
      notRecognizes.2,
      canonicalPaidReplayFairBeforeThreshold_generatesKernel oldVisit
        sourceIndex stage replay stageLeDepth⟩

theorem canonicalPaidReplayFair_noUniformFiniteRecognitionStage
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (¬ ∃ stage,
      ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
        CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
          stage replay) ∧
      (¬ ∃ stage,
        ∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
          CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
            stage replay) := by
  constructor
  · rintro ⟨stage, recognizesEvery⟩
    rcases canonicalPaidReplayFairEveryStage_hasUnrecognizedReplay oldVisit
        sourceIndex stage with ⟨replay, _, occurrenceNot, _⟩
    exact occurrenceNot (recognizesEvery replay)
  · rintro ⟨stage, recognizesEvery⟩
    rcases canonicalPaidReplayFairEveryStage_hasUnrecognizedReplay oldVisit
        sourceIndex stage with ⟨replay, _, _, authorityNot, _⟩
    exact authorityNot (recognizesEvery replay)

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairBeforeThreshold_generatesKernel
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairRecognitionThreshold_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairOccurrenceRecognitionStage_least_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairAuthorityRecognitionStage_least_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairRecognitionStage_minimal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairOccurrenceRecognition_persistent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFair_noUniformFiniteRecognitionStage
