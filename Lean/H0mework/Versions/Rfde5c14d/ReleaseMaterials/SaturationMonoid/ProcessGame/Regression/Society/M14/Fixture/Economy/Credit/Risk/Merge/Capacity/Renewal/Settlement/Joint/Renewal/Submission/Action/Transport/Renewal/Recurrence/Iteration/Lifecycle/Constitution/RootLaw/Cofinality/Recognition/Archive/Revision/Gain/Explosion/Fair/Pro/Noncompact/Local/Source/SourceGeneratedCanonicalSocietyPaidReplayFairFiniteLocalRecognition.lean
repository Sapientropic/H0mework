import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

/-!
# Source-relative finite recognition

Every already emitted paid replay generates a finite fair stage whose fibre at
that replay is a singleton for both occurrence and actual-service authority.
The same stage remains globally open: its canonical later pair is still
invisible there and is separated only by the successor witness.

The recognition stage is computed from the exact emitted replay and a query
bound.  It is not a preinstalled stopping schedule or a completed observer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

/-- Exact finite stage generated from an emitted replay and a requested lower
bound. -/
def canonicalPaidReplayFairRecognitionStage
    {oldVisit : OldVisit} {sourceIndex : Nat} (requestedStage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Nat :=
  max requestedStage replay.1 + 1

theorem canonicalPaidReplayFairRecognitionStage_bounds
    {oldVisit : OldVisit} {sourceIndex : Nat} (requestedStage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    requestedStage <
        canonicalPaidReplayFairRecognitionStage requestedStage replay ∧
      replay.1 <
        canonicalPaidReplayFairRecognitionStage requestedStage replay := by
  unfold canonicalPaidReplayFairRecognitionStage
  omega

/-- Exact occurrence fibre at the source-relative finite stage. -/
theorem canonicalPaidReplayFairRecognitionStage_occurrenceFibre_exact
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (replay candidate :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    let stage :=
      canonicalPaidReplayFairRecognitionStage requestedStage replay
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage replay ↔
      candidate = replay := by
  dsimp only [canonicalPaidReplayFairRecognitionStage]
  constructor
  · intro archiveEquality
    have replayDepthLt :
        replay.1 < max requestedStage replay.1 + 1 := by
      omega
    have bitEquality :=
      congrFun archiveEquality ⟨replay.1, replayDepthLt⟩
    have depthEquality : candidate.1 = replay.1 := by
      simpa [canonicalPaidReplayFairFiniteArchiveReadoutAt] using bitEquality
    exact canonicalPaidReplay_eq_of_depth_eq candidate replay depthEquality
  · intro occurrenceEquality
    subst candidate
    rfl

/-- The same singleton fibre classifies actual-service K exactly. -/
theorem canonicalPaidReplayFairRecognitionStage_authorityKFibre_exact
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (replay candidate :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    let stage :=
      canonicalPaidReplayFairRecognitionStage requestedStage replay
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          candidate =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage replay ↔
      candidate.2.authorityK = replay.2.authorityK := by
  constructor
  · intro archiveEquality
    have occurrenceEquality :=
      (canonicalPaidReplayFairRecognitionStage_occurrenceFibre_exact oldVisit
        sourceIndex requestedStage replay candidate).1 archiveEquality
    exact congrArg (fun paidReplay => paidReplay.2.authorityK)
      occurrenceEquality
  · intro authorityEquality
    have occurrenceEquality :=
      canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
        authorityEquality
    exact
      (canonicalPaidReplayFairRecognitionStage_occurrenceFibre_exact oldVisit
        sourceIndex requestedStage replay candidate).2 occurrenceEquality

/-- Every emitted replay inhabits its own exact depth-indexed source-witness
fibre. -/
theorem canonicalPaidReplayFairOwnStageWitness_nonempty
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    Nonempty
      (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex replay.1 replay) := by
  cases replay with
  | mk replayDepth replayProof =>
      cases replayProof
      exact
        ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex replayDepth⟩

/-- Maximum local-recognition producer: the replay has an exact finite
singleton fibre, while the very same stage still has a later authority
kernel and a source-generated successor separation. -/
theorem canonicalPaidReplayFairLocallyRecognizableGloballyOpen
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    let stage :=
      canonicalPaidReplayFairRecognitionStage requestedStage replay
    let laterPair :=
      canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        stage
    requestedStage < stage ∧
      replay.1 < stage ∧
      (∀ candidate :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage candidate =
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage replay ↔
          candidate = replay)) ∧
      (∀ candidate :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage candidate =
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage replay ↔
          candidate.2.authorityK = replay.2.authorityK)) ∧
      type_of% replay.2.paidStep_consumes_exactPayment ∧
      type_of% replay.2.paymentNext_isCanonicalTarget ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex replay.1 replay) ∧
      replay.1 < laterPair.left.1 ∧
      replay.1 < laterPair.right.1 ∧
      laterPair.left ≠ laterPair.right ∧
      laterPair.left.2.authorityK ≠ laterPair.right.2.authorityK ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            laterPair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage laterPair.right ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            (stage + 1) laterPair.left ≠
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (stage + 1) laterPair.right := by
  let stage := canonicalPaidReplayFairRecognitionStage requestedStage replay
  let laterPair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex stage
  have bounds :=
    canonicalPaidReplayFairRecognitionStage_bounds requestedStage replay
  have leftLater : replay.1 < laterPair.left.1 := by
    change replay.1 < stage
    exact bounds.2
  have rightLater : replay.1 < laterPair.right.1 := by
    change replay.1 < stage + 1
    omega
  exact
    ⟨bounds.1,
      bounds.2,
      canonicalPaidReplayFairRecognitionStage_occurrenceFibre_exact oldVisit
        sourceIndex requestedStage replay,
      canonicalPaidReplayFairRecognitionStage_authorityKFibre_exact oldVisit
        sourceIndex requestedStage replay,
      replay.2.paidStep_consumes_exactPayment,
      replay.2.paymentNext_isCanonicalTarget,
      canonicalPaidReplayFairOwnStageWitness_nonempty oldVisit sourceIndex
        replay,
      leftLater,
      rightLater,
      laterPair.occurrence_ne,
      laterPair.authority_ne,
      canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
        sourceIndex stage,
      canonicalPaidReplayFairFiniteArchive_successorSeparatesCurrentPair
        oldVisit sourceIndex stage⟩

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition.canonicalPaidReplayFairRecognitionStage_occurrenceFibre_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition.canonicalPaidReplayFairRecognitionStage_authorityKFibre_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition.canonicalPaidReplayFairOwnStageWitness_nonempty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition.canonicalPaidReplayFairLocallyRecognizableGloballyOpen
