import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower

/-!
# Proof-carrying finite-stage pro-truth

Every individual finite stage remains non-faithful, while the coherent open
family jointly determines occurrence and actual-service authority.  The mouth
contains only finite-stage quantification and does not install a terminal
observer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteProTruth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth

/-- Maximum pro-truth mouth: every component is incomplete, but equality and
difference of occurrences/K are exactly classified by the coherent family. -/
theorem canonicalPaidReplayFairFiniteProTruth_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    type_of%
        (canonicalPaidReplayFairFiniteWitnessTower_directConsumer oldVisit
          sourceIndex) ∧
      Function.Injective
        (fun replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex => replay.2.authorityK) ∧
      (∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        (left = right ↔
          ∀ stage,
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                  stage left =
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                sourceIndex stage right)) ∧
      (∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        (left.2.authorityK = right.2.authorityK ↔
          ∀ stage,
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                  stage left =
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                sourceIndex stage right)) ∧
      (∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        (left ≠ right ↔
          ∃ stage,
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                  stage left ≠
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                sourceIndex stage right)) ∧
      (∀ left right :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        (left.2.authorityK ≠ right.2.authorityK ↔
          ∃ stage,
            canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
                  stage left ≠
              canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit
                sourceIndex stage right)) ∧
      (∀ stage,
        type_of%
          (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
            sourceIndex stage)) :=
  ⟨canonicalPaidReplayFairFiniteWitnessTower_directConsumer oldVisit
      sourceIndex,
    canonicalPaidReplay_authorityK_injective oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteStages_occurrence_eq_iff oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteStages_authorityK_eq_iff oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteStages_occurrence_ne_iff oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteStages_authorityK_ne_iff oldVisit sourceIndex,
    canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
      sourceIndex⟩

/-- The constitutional point consumes jointly faithful pro-truth while
retaining the entire fair tower and prior explosion as one exact conjunct. -/
theorem canonicalCofinalPaidReplayFairFiniteProTruth_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFairFiniteWitnessTower_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFairFiniteProTruth_directConsumer oldVisit
          sourceIndex) :=
  ⟨canonicalCofinalPaidReplayFairFiniteWitnessTower_directConsumer point,
    canonicalPaidReplayFairFiniteProTruth_directConsumer oldVisit sourceIndex⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteProTruth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalPaidReplayFairFiniteProTruth_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteProTruth.canonicalCofinalPaidReplayFairFiniteProTruth_directConsumer
