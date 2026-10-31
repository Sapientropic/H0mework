import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteProTruth

/-!
# Proof-carrying irreducible finite-stage pro-truth

All finite stages jointly determine occurrence and actual-service authority,
yet every finite subfamily has one cofinal paid kernel invisible to all of its
members.  The strongest mouth keeps each cutoff stage's complete no-section,
witness and immediate-repair consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteProTruth
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

/-- Exact noncompactness mouth: the open family is jointly faithful, no finite
subfamily is, and every finite query receives one later paid kernel together
with the full consumer at its computed cutoff. -/
theorem canonicalPaidReplayFairFiniteNoncompactProTruth_directConsumer
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    type_of%
        (canonicalPaidReplayFairFiniteProTruth_directConsumer oldVisit
          sourceIndex) ∧
      (∀ stages : Finset Nat,
        ¬ CanonicalPaidReplayFairFiniteSubfamilyOccurrenceFaithfulAt
            oldVisit sourceIndex stages ∧
          ¬ CanonicalPaidReplayFairFiniteSubfamilyAuthorityFaithfulAt
            oldVisit sourceIndex stages) ∧
      (∀ (requestedStage : Nat) (stages : Finset Nat),
        type_of%
          (canonicalPaidReplayFairFiniteSubfamilyKernel oldVisit sourceIndex
            requestedStage stages)) ∧
      (∀ (requestedStage : Nat) (stages : Finset Nat),
        type_of%
          (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
            sourceIndex
            (canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage
              stages))) := by
  exact
    ⟨canonicalPaidReplayFairFiniteProTruth_directConsumer oldVisit
        sourceIndex,
      fun stages =>
        ⟨canonicalPaidReplayFairFiniteSubfamily_notOccurrenceFaithful
            oldVisit sourceIndex stages,
          canonicalPaidReplayFairFiniteSubfamily_notAuthorityFaithful oldVisit
            sourceIndex stages⟩,
      canonicalPaidReplayFairFiniteSubfamilyKernel oldVisit sourceIndex,
      fun requestedStage stages =>
        canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex
          (canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage
            stages)⟩

/-- A constitutional point uses its own `m` as the lower bound for every
finite subfamily query.  The old cofinal pro-truth mouth remains exact. -/
theorem canonicalCofinalPaidReplayFairFiniteNoncompactProTruth_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFairFiniteProTruth_directConsumer point) ∧
      type_of%
        (canonicalPaidReplayFairFiniteNoncompactProTruth_directConsumer
          oldVisit sourceIndex) ∧
      (∀ stages : Finset Nat,
        type_of%
          (canonicalPaidReplayFairFiniteSubfamilyKernel oldVisit sourceIndex m
            stages)) :=
  ⟨canonicalCofinalPaidReplayFairFiniteProTruth_directConsumer point,
    canonicalPaidReplayFairFiniteNoncompactProTruth_directConsumer oldVisit
      sourceIndex,
    canonicalPaidReplayFairFiniteSubfamilyKernel oldVisit sourceIndex m⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth.canonicalPaidReplayFairFiniteNoncompactProTruth_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth.canonicalCofinalPaidReplayFairFiniteNoncompactProTruth_directConsumer
