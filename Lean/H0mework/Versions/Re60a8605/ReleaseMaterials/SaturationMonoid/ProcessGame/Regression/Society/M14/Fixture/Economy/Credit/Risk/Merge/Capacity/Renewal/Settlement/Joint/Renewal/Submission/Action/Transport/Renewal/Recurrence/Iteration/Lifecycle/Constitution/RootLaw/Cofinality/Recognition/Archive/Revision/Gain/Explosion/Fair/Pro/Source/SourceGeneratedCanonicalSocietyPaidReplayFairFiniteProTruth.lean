import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower

/-!
# Jointly faithful finite-stage pro-truth

No finite fair archive is authority-complete, but the coherent family is
jointly faithful: two paid replays, and equivalently their actual-service
authorities, agree exactly when every finite stage reads them equally.

This file quantifies over finite stages.  It constructs no product archive,
omega observer, registry or terminal truth object.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower

/-- Paid replay occurrence is determined by its exact temporal depth. -/
theorem canonicalPaidReplay_eq_of_depth_eq
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
    (depthEquality : left.1 = right.1) :
    left = right := by
  cases left with
  | mk leftDepth leftReplay =>
      cases right with
      | mk rightDepth rightReplay =>
          simp only at depthEquality
          subst rightDepth
          cases leftReplay
          cases rightReplay
          rfl

/-- Actual-service K is injective on the existing paid-replay family. -/
theorem canonicalPaidReplay_authorityK_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective
      (fun replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex =>
        replay.2.authorityK) := by
  intro left right authorityEquality
  have currentEquality :=
    periodicActualServiceExitOccurrenceAt_injective authorityEquality
  change
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex left.1 =
      contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex right.1 at currentEquality
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt at currentEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  apply canonicalPaidReplay_eq_of_depth_eq left right
  omega

/-- Joint occurrence faithfulness without assembling the stages into one
completed observer. -/
theorem canonicalPaidReplayFairFiniteStages_occurrence_eq_iff
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    left = right ↔
      ∀ stage,
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage left =
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage right := by
  constructor
  · intro occurrenceEquality
    subst right
    intro stage
    rfl
  · intro everyStageEquality
    by_contra occurrenceNe
    rcases canonicalPaidReplayFairFiniteArchive_eventuallySeparates oldVisit
        sourceIndex left right occurrenceNe with
      ⟨stage, separates⟩
    exact separates (everyStageEquality stage)

/-- Joint authority faithfulness is equivalent to the same finite-stage
family. -/
theorem canonicalPaidReplayFairFiniteStages_authorityK_eq_iff
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    left.2.authorityK = right.2.authorityK ↔
      ∀ stage,
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage left =
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage right := by
  constructor
  · intro authorityEquality
    have occurrenceEquality :=
      canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
        authorityEquality
    exact
      (canonicalPaidReplayFairFiniteStages_occurrence_eq_iff oldVisit
        sourceIndex left right).1 occurrenceEquality
  · intro everyStageEquality
    have occurrenceEquality :=
      (canonicalPaidReplayFairFiniteStages_occurrence_eq_iff oldVisit
        sourceIndex left right).2 everyStageEquality
    exact congrArg (fun replay => replay.2.authorityK) occurrenceEquality

/-- Exact fibre constraint for occurrences: difference is witnessed at one
finite stage, while equality forces equality at all finite stages. -/
theorem canonicalPaidReplayFairFiniteStages_occurrence_ne_iff
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    left ≠ right ↔
      ∃ stage,
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage left ≠
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage right := by
  constructor
  · exact
      canonicalPaidReplayFairFiniteArchive_eventuallySeparates oldVisit
        sourceIndex left right
  · rintro ⟨stage, separates⟩ occurrenceEquality
    subst right
    exact separates rfl

/-- Exact fibre constraint for authority K. -/
theorem canonicalPaidReplayFairFiniteStages_authorityK_ne_iff
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    left.2.authorityK ≠ right.2.authorityK ↔
      ∃ stage,
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage left ≠
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage right := by
  constructor
  · intro authorityNe
    apply
      (canonicalPaidReplayFairFiniteStages_occurrence_ne_iff oldVisit
        sourceIndex left right).1
    intro occurrenceEquality
    exact authorityNe
      (congrArg (fun replay => replay.2.authorityK) occurrenceEquality)
  · rintro ⟨stage, separates⟩ authorityEquality
    have occurrenceEquality :=
      canonicalPaidReplay_authorityK_injective oldVisit sourceIndex
        authorityEquality
    subst right
    exact separates rfl

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalPaidReplay_authorityK_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalPaidReplayFairFiniteStages_occurrence_eq_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalPaidReplayFairFiniteStages_authorityK_eq_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalPaidReplayFairFiniteStages_occurrence_ne_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalPaidReplayFairFiniteStages_authorityK_ne_iff
