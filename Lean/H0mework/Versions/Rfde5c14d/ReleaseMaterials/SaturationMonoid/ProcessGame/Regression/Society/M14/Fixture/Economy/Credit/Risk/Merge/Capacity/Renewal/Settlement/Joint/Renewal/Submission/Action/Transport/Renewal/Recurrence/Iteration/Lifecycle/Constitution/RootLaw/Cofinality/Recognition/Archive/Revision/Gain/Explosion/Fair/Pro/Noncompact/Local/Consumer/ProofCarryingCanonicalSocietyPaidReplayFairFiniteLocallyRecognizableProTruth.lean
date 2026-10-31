import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

/-!
# Proof-carrying locally recognizable, globally open pro-truth

Every emitted paid replay has a finite singleton recognition fibre.  The same
finite stage remains globally incomplete, and the prior finite-subfamily
noncompact pro-truth is retained as one exact conjunct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteLocallyRecognizableProTruth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteLocalRecognition
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

/-- Maximum local/global mouth: finite source-relative recognition and finite
global incompleteness hold at the same computed stage. -/
theorem canonicalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    type_of%
        (canonicalPaidReplayFairFiniteNoncompactProTruth_directConsumer
          oldVisit sourceIndex) ∧
      (∀ (requestedStage : Nat)
        (replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex),
        type_of%
            (canonicalPaidReplayFairLocallyRecognizableGloballyOpen oldVisit
              sourceIndex requestedStage replay) ∧
          type_of%
            (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
              sourceIndex
              (canonicalPaidReplayFairRecognitionStage requestedStage
                replay))) := by
  constructor
  · exact
      canonicalPaidReplayFairFiniteNoncompactProTruth_directConsumer oldVisit
        sourceIndex
  · intro requestedStage replay
    exact
      ⟨canonicalPaidReplayFairLocallyRecognizableGloballyOpen oldVisit
          sourceIndex requestedStage replay,
        canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex
          (canonicalPaidReplayFairRecognitionStage requestedStage replay)⟩

/-- The constitutional point uses its own `m` as every replay's requested
recognition lower bound, while retaining the old cofinal noncompact mouth. -/
theorem canonicalCofinalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFairFiniteNoncompactProTruth_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
          oldVisit sourceIndex) ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        type_of%
            (canonicalPaidReplayFairLocallyRecognizableGloballyOpen oldVisit
              sourceIndex m replay) ∧
          type_of%
            (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
              sourceIndex
              (canonicalPaidReplayFairRecognitionStage m replay))) := by
  exact
    ⟨canonicalCofinalPaidReplayFairFiniteNoncompactProTruth_directConsumer
        point,
      canonicalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
        oldVisit sourceIndex,
      fun replay =>
        ⟨canonicalPaidReplayFairLocallyRecognizableGloballyOpen oldVisit
            sourceIndex m replay,
          canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
            sourceIndex
            (canonicalPaidReplayFairRecognitionStage m replay)⟩⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteLocallyRecognizableProTruth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteLocallyRecognizableProTruth.canonicalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteLocallyRecognizableProTruth.canonicalCofinalPaidReplayFairFiniteLocallyRecognizableProTruth_directConsumer
