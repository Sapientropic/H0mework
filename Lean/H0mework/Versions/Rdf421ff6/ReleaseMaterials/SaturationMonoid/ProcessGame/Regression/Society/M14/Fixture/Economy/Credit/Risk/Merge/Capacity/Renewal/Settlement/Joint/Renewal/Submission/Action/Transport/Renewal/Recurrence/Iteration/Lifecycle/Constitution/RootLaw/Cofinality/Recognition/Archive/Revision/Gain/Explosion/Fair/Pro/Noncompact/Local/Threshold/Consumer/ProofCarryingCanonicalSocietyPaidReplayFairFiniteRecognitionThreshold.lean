import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteLocallyRecognizableProTruth

/-!
# Proof-carrying exact recognition threshold

The maximal mouth classifies every finite stage against every emitted replay,
proves the exact least and persistent recognition stage, and simultaneously
retains a paid counterexample at every fixed stage.  Local recognizability and
global openness remain one theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteLocallyRecognizableProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold

/-- Maximum exact-threshold mouth. -/
theorem canonicalPaidReplayFairFiniteRecognitionThreshold_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    type_of%
        (canonicalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
          oldVisit sourceIndex) ∧
      (∀ stage
        (replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
          (canonicalPaidReplayFairRecognitionThreshold_exact oldVisit
            sourceIndex stage replay)) ∧
      (∀ stage
        (replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
            (canonicalPaidReplayFairOccurrenceRecognitionStage_least_iff
              oldVisit sourceIndex stage replay) ∧
          type_of%
            (canonicalPaidReplayFairAuthorityRecognitionStage_least_iff
              oldVisit sourceIndex stage replay)) ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        type_of%
          (canonicalPaidReplayFairRecognitionStage_minimal oldVisit
            sourceIndex replay)) ∧
      (∀ {stage later : Nat} (stageLeLater : stage ≤ later)
        (replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
            (canonicalPaidReplayFairOccurrenceRecognition_persistent oldVisit
              sourceIndex stageLeLater replay) ∧
          type_of%
            (canonicalPaidReplayFairAuthorityRecognition_persistent oldVisit
              sourceIndex stageLeLater replay)) ∧
      (∀ stage,
        type_of%
          (canonicalPaidReplayFairEveryStage_hasUnrecognizedReplay oldVisit
            sourceIndex stage)) ∧
      type_of%
        (canonicalPaidReplayFair_noUniformFiniteRecognitionStage oldVisit
          sourceIndex) ∧
      (∀ stage,
        type_of%
          (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
            sourceIndex stage)) := by
  exact
    ⟨canonicalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
        oldVisit sourceIndex,
      canonicalPaidReplayFairRecognitionThreshold_exact oldVisit sourceIndex,
      fun stage replay =>
        ⟨canonicalPaidReplayFairOccurrenceRecognitionStage_least_iff
            oldVisit sourceIndex stage replay,
          canonicalPaidReplayFairAuthorityRecognitionStage_least_iff oldVisit
            sourceIndex stage replay⟩,
      canonicalPaidReplayFairRecognitionStage_minimal oldVisit sourceIndex,
      fun stageLeLater replay =>
        ⟨canonicalPaidReplayFairOccurrenceRecognition_persistent oldVisit
            sourceIndex stageLeLater replay,
          canonicalPaidReplayFairAuthorityRecognition_persistent oldVisit
            sourceIndex stageLeLater replay⟩,
      canonicalPaidReplayFairEveryStage_hasUnrecognizedReplay oldVisit
        sourceIndex,
      canonicalPaidReplayFair_noUniformFiniteRecognitionStage oldVisit
        sourceIndex,
      canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
        sourceIndex⟩

/-- The same constitutional point retains its `m`-relative local certificates
and consumes the exact threshold classification without a second observer. -/
theorem canonicalCofinalPaidReplayFairFiniteRecognitionThreshold_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFairFiniteRecognitionThreshold_directConsumer
          oldVisit sourceIndex) :=
  ⟨canonicalCofinalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
      point,
    canonicalPaidReplayFairFiniteRecognitionThreshold_directConsumer oldVisit
      sourceIndex⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalPaidReplayFairFiniteRecognitionThreshold_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteRecognitionThreshold.canonicalCofinalPaidReplayFairFiniteRecognitionThreshold_directConsumer
