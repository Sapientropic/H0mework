import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Stratification.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

/-!
# Exact successor recognition flux

The transition from stage `n` to `n+1` removes exactly the depth-`n` paid
replay from the unresolved tail.  That replay gains a persistent singleton
occurrence/K fibre through its source witness, while the successor tail stays
unbounded and K-diverse.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteFibreStratification

/-- The unique paid replay leaving the unresolved tail at this successor. -/
def canonicalPaidReplayFairEscapingReplayAt
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex stage

/-- Exact tail update: one escaping replay plus the successor tail. -/
theorem canonicalPaidReplayFairTail_successor_split
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    CanonicalPaidReplayFairTailAt stage replay ↔
      replay =
          canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex stage ∨
        CanonicalPaidReplayFairTailAt (stage + 1) replay := by
  constructor
  · intro tail
    by_cases depthEquality : replay.1 = stage
    · left
      apply canonicalPaidReplay_eq_of_depth_eq
      simpa [canonicalPaidReplayFairEscapingReplayAt,
        contributionCapacityPostSettlementPaidReplayAt] using depthEquality
    · right
      unfold CanonicalPaidReplayFairTailAt at tail ⊢
      omega
  · rintro (occurrenceEquality | successorTail)
    · subst replay
      unfold CanonicalPaidReplayFairTailAt
      simp [canonicalPaidReplayFairEscapingReplayAt,
        contributionCapacityPostSettlementPaidReplayAt]
    · unfold CanonicalPaidReplayFairTailAt at successorTail ⊢
      omega

theorem canonicalPaidReplayFairTail_successor_branches_disjoint
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    ¬ (replay =
          canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex stage ∧
        CanonicalPaidReplayFairTailAt (stage + 1) replay) := by
  rintro ⟨occurrenceEquality, successorTail⟩
  subst replay
  unfold CanonicalPaidReplayFairTailAt at successorTail
  change stage + 1 ≤ stage at successorTail
  omega

/-- Exact characterization of the unique occurrence crossing the recognition
frontier in this step. -/
theorem canonicalPaidReplayFairTail_uniqueEscaper
    (oldVisit : OldVisit) (sourceIndex stage : Nat)
    (replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    (CanonicalPaidReplayFairTailAt stage replay ∧
        ¬ CanonicalPaidReplayFairTailAt (stage + 1) replay) ↔
      replay =
        canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex stage := by
  constructor
  · rintro ⟨tail, successorNot⟩
    rcases
        (canonicalPaidReplayFairTail_successor_split oldVisit sourceIndex stage
          replay).1 tail with occurrenceEquality | successorTail
    · exact occurrenceEquality
    · exact (successorNot successorTail).elim
  · intro occurrenceEquality
    subst replay
    constructor
    · unfold CanonicalPaidReplayFairTailAt
      simp [canonicalPaidReplayFairEscapingReplayAt,
        contributionCapacityPostSettlementPaidReplayAt]
    · unfold CanonicalPaidReplayFairTailAt
      change ¬ stage + 1 ≤ stage
      omega

/-- Maximum source-native recognition-flux package. -/
theorem canonicalPaidReplayFairSuccessorRecognitionFlux
    (oldVisit : OldVisit) (sourceIndex stage : Nat) :
    let escaping :=
      canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex stage
    let currentPair :=
      canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        stage
    let remainingPair :=
      canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        (stage + 1)
    (∀ replay,
      CanonicalPaidReplayFairTailAt stage replay ↔
        replay = escaping ∨
          CanonicalPaidReplayFairTailAt (stage + 1) replay) ∧
      (∀ replay,
        ¬ (replay = escaping ∧
          CanonicalPaidReplayFairTailAt (stage + 1) replay)) ∧
      (∀ replay,
        (CanonicalPaidReplayFairTailAt stage replay ∧
            ¬ CanonicalPaidReplayFairTailAt (stage + 1) replay) ↔
          replay = escaping) ∧
      ¬ CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
        stage escaping ∧
      CanonicalPaidReplayFairOccurrenceRecognizesAt oldVisit sourceIndex
        (stage + 1) escaping ∧
      ¬ CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
        stage escaping ∧
      CanonicalPaidReplayFairAuthorityRecognizesAt oldVisit sourceIndex
        (stage + 1) escaping ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex stage escaping) ∧
      type_of% escaping.2.paidStep_consumes_exactPayment ∧
      type_of% escaping.2.paymentNext_isCanonicalTarget ∧
      currentPair.left = escaping ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            currentPair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage currentPair.right ∧
      currentPair.left ≠ currentPair.right ∧
      currentPair.left.2.authorityK ≠ currentPair.right.2.authorityK ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            (stage + 1) currentPair.left ≠
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (stage + 1) currentPair.right ∧
      CanonicalPaidReplayFairTailAt (stage + 1) remainingPair.left ∧
      CanonicalPaidReplayFairTailAt (stage + 1) remainingPair.right ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            (stage + 1) remainingPair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (stage + 1) remainingPair.right ∧
      remainingPair.left ≠ remainingPair.right ∧
      remainingPair.left.2.authorityK ≠
        remainingPair.right.2.authorityK ∧
      Function.Injective
        (fun offset =>
          (canonicalPaidReplayFairTailOccurrenceAt oldVisit sourceIndex
            (stage + 1) offset).1.2.authorityK) := by
  let escaping :=
    canonicalPaidReplayFairEscapingReplayAt oldVisit sourceIndex stage
  let currentPair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex stage
  let remainingPair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      (stage + 1)
  have escapingDepth : escaping.1 = stage := by
    rfl
  have occurrenceAtSuccessor :=
    (canonicalPaidReplayFairOccurrenceRecognitionThreshold_exact oldVisit
      sourceIndex (stage + 1) escaping).2 (by omega)
  have authorityAtSuccessor :=
    (canonicalPaidReplayFairAuthorityRecognitionThreshold_exact oldVisit
      sourceIndex (stage + 1) escaping).2 (by omega)
  have occurrenceNotCurrent :=
    (canonicalPaidReplayFairBeforeThreshold_notRecognizes oldVisit sourceIndex
      stage escaping (by omega)).1
  have authorityNotCurrent :=
    (canonicalPaidReplayFairBeforeThreshold_notRecognizes oldVisit sourceIndex
      stage escaping (by omega)).2
  have remainingLeftTail :
      CanonicalPaidReplayFairTailAt (stage + 1) remainingPair.left := by
    unfold CanonicalPaidReplayFairTailAt
    change stage + 1 ≤ stage + 1
    omega
  have remainingRightTail :
      CanonicalPaidReplayFairTailAt (stage + 1) remainingPair.right := by
    unfold CanonicalPaidReplayFairTailAt
    change stage + 1 ≤ stage + 1 + 1
    omega
  exact
    ⟨canonicalPaidReplayFairTail_successor_split oldVisit sourceIndex stage,
      canonicalPaidReplayFairTail_successor_branches_disjoint oldVisit
        sourceIndex stage,
      canonicalPaidReplayFairTail_uniqueEscaper oldVisit sourceIndex stage,
      occurrenceNotCurrent,
      occurrenceAtSuccessor,
      authorityNotCurrent,
      authorityAtSuccessor,
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex stage⟩,
      escaping.2.paidStep_consumes_exactPayment,
      escaping.2.paymentNext_isCanonicalTarget,
      rfl,
      canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
        sourceIndex stage,
      currentPair.occurrence_ne,
      currentPair.authority_ne,
      canonicalPaidReplayFairFiniteArchive_successorSeparatesCurrentPair
        oldVisit sourceIndex stage,
      remainingLeftTail,
      remainingRightTail,
      canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
        sourceIndex (stage + 1),
      remainingPair.occurrence_ne,
      remainingPair.authority_ne,
      canonicalPaidReplayFairTailAuthorityK_injective oldVisit sourceIndex
        (stage + 1)⟩

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux.canonicalPaidReplayFairTail_successor_split
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux.canonicalPaidReplayFairTail_uniqueEscaper
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux.canonicalPaidReplayFairSuccessorRecognitionFlux
