import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Source.SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Consumer.ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade

/-!
# Proof-carrying strict finite-archive gain cascade

Every finite revision adds a witness bit which is irreducible to the preceding
archive, while the preceding archive remains an exact projection of the new
one.  The carrier-capacity law is exact at every depth and is consumed together
with the still-open paid-replay authority kernel.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveStrictGainCascade

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision
open M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveStrictGain

/-- One strict-gain step consumes the full local-repair/later-kernel mouth and
adds exact projection, witness irreducibility and carrier growth. -/
theorem canonicalPaidReplayFiniteArchiveStrictGainStep_directConsumer
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    type_of%
        (canonicalPaidReplayFiniteArchiveRevisionStep_directConsumer
          calculation) ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        canonicalPaidReplayFiniteArchiveRevisionProjection calculation
            ((canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
              calculation).archiveReadout replay) =
          calculation.archiveReadout replay) ∧
      (¬ ∃ decode : calculation.Archive → Bool,
        ∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
          decode (calculation.archiveReadout replay) =
            canonicalPaidReplayArchiveWitnessPublicationTag calculation
              replay) ∧
      @Fintype.card
          (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
            calculation).Archive
          (canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
            calculation).archiveFintype =
        @Fintype.card calculation.Archive calculation.archiveFintype * 2 ∧
      type_of%
        (canonicalPaidReplayFiniteArchiveActualImage_card_strictlyGrows
          calculation) :=
  ⟨canonicalPaidReplayFiniteArchiveRevisionStep_directConsumer calculation,
    canonicalPaidReplayFiniteArchiveRevisionProjection_exact calculation,
    canonicalPaidReplayArchiveWitnessTag_notFactorThroughCurrentArchive
      calculation,
    canonicalPaidReplayFiniteArchiveGeneratedNext_card calculation,
    canonicalPaidReplayFiniteArchiveActualImage_card_strictlyGrows
      calculation⟩

/-- All-depth maximum: every recursive step is a strict gain, its whole
authority observer stays open, and capacity is exactly initial×2^depth. -/
theorem canonicalPaidReplayFiniteArchiveStrictGainCascade_directConsumer
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    let stateAt :=
      canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex lowerBound archive
    type_of%
        (canonicalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
          oldVisit sourceIndex lowerBound archive) ∧
      (∀ depth,
        type_of%
          (canonicalPaidReplayFiniteArchiveStrictGainStep_directConsumer
            (stateAt depth))) ∧
      (∀ depth,
        @Fintype.card (stateAt depth).Archive
            (stateAt depth).archiveFintype =
          Fintype.card Archive * 2 ^ depth) := by
  dsimp
  exact
    ⟨canonicalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
        oldVisit sourceIndex lowerBound archive,
      fun depth =>
        canonicalPaidReplayFiniteArchiveStrictGainStep_directConsumer
          (canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
            sourceIndex lowerBound archive depth),
      canonicalPaidReplayFiniteArchiveRevision_card_exact oldVisit
        sourceIndex lowerBound archive⟩

/-- The same constitutional point now carries the strict all-depth gain law;
the previous open-cascade mouth remains an exact conjunct. -/
theorem canonicalCofinalPaidReplayFiniteArchiveStrictGainCascade_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFiniteArchiveStrictGainCascade_directConsumer
          oldVisit sourceIndex m
          (canonicalCofinalPaidReplayPublicationTag point)) :=
  ⟨canonicalCofinalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
      point,
    canonicalPaidReplayFiniteArchiveStrictGainCascade_directConsumer oldVisit
      sourceIndex m (canonicalCofinalPaidReplayPublicationTag point)⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveStrictGainCascade
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveStrictGainCascade.canonicalPaidReplayFiniteArchiveStrictGainStep_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveStrictGainCascade.canonicalPaidReplayFiniteArchiveStrictGainCascade_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveStrictGainCascade.canonicalCofinalPaidReplayFiniteArchiveStrictGainCascade_directConsumer
