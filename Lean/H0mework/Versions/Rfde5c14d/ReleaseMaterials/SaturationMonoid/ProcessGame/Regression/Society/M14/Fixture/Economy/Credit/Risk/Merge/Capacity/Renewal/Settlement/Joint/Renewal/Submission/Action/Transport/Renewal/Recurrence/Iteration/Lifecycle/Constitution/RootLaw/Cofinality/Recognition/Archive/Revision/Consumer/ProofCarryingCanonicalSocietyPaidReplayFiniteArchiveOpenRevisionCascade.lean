import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Source.SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Consumer.ProofCarryingCanonicalSocietyPaidReplayNoFiniteTruthCompletion

/-!
# Proof-carrying open finite-archive revision cascade

At every finite revision depth, an honest K-free witness separates the current
paid-replay kernel pair.  The refined archive remains finite, so it generates
a new kernel strictly later than both old endpoints.  Thus every finite
observer revision is useful locally and open globally.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication
open M14ProofCarryingCanonicalSocietyPaidReplayNoFiniteTruthCompletion
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision
open M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveRevision.CanonicalPaidReplayFiniteArchiveRevisionCalculationAt

/-- One exact revision step: positive two-point repair and a strictly later
whole-archive kernel are generated from the same predecessor calculation. -/
theorem canonicalPaidReplayFiniteArchiveRevisionStep_directConsumer
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (calculation :
      CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex) :
    let O := calculation.observer
    let pair := calculation.currentPair
    let refinement :=
      canonicalPaidReplayArchiveCurrentKernelRefinementAt calculation
    let next :=
      canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
    Nonempty
        (SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation
          pair.left) ∧
      IsEmpty
        (SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation
          pair.right) ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        canonicalPaidReplayArchiveWitnessPublicationTag calculation replay =
            true ↔
          Nonempty
            (SourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation
              replay)) ∧
      calculation.lowerBound < pair.left.1 ∧
      calculation.lowerBound < pair.right.1 ∧
      O.forget pair.left = O.forget pair.right ∧
      O.authorityK pair.left ≠ O.authorityK pair.right ∧
      canonicalPaidReplayRefinedArchiveReadout calculation pair.left ≠
        canonicalPaidReplayRefinedArchiveReadout calculation pair.right ∧
      Nonempty
        (FaithfulAuthorityReconstruction refinement.twoPointObserver) ∧
      Nonempty (AuthorityFactorization refinement.twoPointObserver) ∧
      ¬ Nonempty (AuthorityFactorization O) ∧
      ¬ Nonempty (FaithfulAuthorityReconstruction O) ∧
      next.lowerBound = max pair.left.1 pair.right.1 ∧
      (∀ replay :
          AnyContributionCapacityPostSettlementPaidReplay oldVisit
            sourceIndex,
        next.archiveReadout replay =
          canonicalPaidReplayRefinedArchiveReadout calculation replay) ∧
      pair.left.1 < next.currentPair.left.1 ∧
      pair.right.1 < next.currentPair.left.1 ∧
      pair.left.1 < next.currentPair.right.1 ∧
      pair.right.1 < next.currentPair.right.1 ∧
      next.observer.forget next.currentPair.left =
        next.observer.forget next.currentPair.right ∧
      next.observer.authorityK next.currentPair.left ≠
        next.observer.authorityK next.currentPair.right ∧
      ¬ Nonempty (AuthorityFactorization next.observer) := by
  dsimp
  let pair := calculation.currentPair
  let refinement :=
    canonicalPaidReplayArchiveCurrentKernelRefinementAt calculation
  let next :=
    canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt calculation
  have nextLeftLater := next.currentPair_left_later
  have nextRightLater := next.currentPair_right_later
  rw [canonicalPaidReplayFiniteArchiveGeneratedNext_lowerBound] at nextLeftLater nextRightLater
  exact
    ⟨⟨sourceGeneratedCanonicalPaidReplayArchiveWitnessAt calculation⟩,
      canonicalPaidReplayArchiveCurrentPair_rightWitness_isEmpty calculation,
      canonicalPaidReplayArchiveWitnessPublicationTag_true_iff calculation,
      calculation.currentPair_left_later,
      calculation.currentPair_right_later,
      pair.visible_eq,
      pair.authority_ne,
      canonicalPaidReplayRefinedArchive_separatesCurrentPair calculation,
      ⟨refinement.twoPointFaithfulAuthorityReconstruction⟩,
      ⟨refinement.twoPointAuthorityFactorization⟩,
      pair.noAuthorityFactorization,
      pair.noFaithfulAuthorityReconstruction,
      canonicalPaidReplayFiniteArchiveGeneratedNext_lowerBound calculation,
      canonicalPaidReplayFiniteArchiveGeneratedNext_archiveReadout calculation,
      (Nat.le_max_left _ _).trans_lt nextLeftLater,
      (Nat.le_max_right _ _).trans_lt nextLeftLater,
      (Nat.le_max_left _ _).trans_lt nextRightLater,
      (Nat.le_max_right _ _).trans_lt nextRightLater,
      next.currentPair.visible_eq,
      next.currentPair.authority_ne,
      next.currentPair.noAuthorityFactorization⟩

/-- Maximum all-finite-depth consumer.  Each state is computed recursively;
strictly increasing bounds certify that no positive finite revision period can
close the observer process. -/
theorem canonicalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    let stateAt :=
      canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
        sourceIndex lowerBound archive
    (∀ depth,
        type_of%
          (canonicalPaidReplayFiniteArchiveRevisionStep_directConsumer
            (stateAt depth))) ∧
      (∀ depth,
        stateAt (depth + 1) =
          canonicalPaidReplayFiniteArchiveGeneratedNextCalculationAt
            (stateAt depth)) ∧
      StrictMono (fun depth => (stateAt depth).lowerBound) ∧
      Function.Injective (fun depth => (stateAt depth).lowerBound) ∧
      (∀ depth period, 0 < period →
        stateAt (depth + period) ≠ stateAt depth) := by
  dsimp
  let stateAt :=
    canonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
      sourceIndex lowerBound archive
  have boundsStrictMono :
      StrictMono (fun depth => (stateAt depth).lowerBound) :=
    canonicalPaidReplayFiniteArchiveRevisionBounds_strictMono oldVisit
      sourceIndex lowerBound archive
  exact
    ⟨fun depth =>
        canonicalPaidReplayFiniteArchiveRevisionStep_directConsumer
          (stateAt depth),
      (fun depth =>
        canonicalPaidReplayFiniteArchiveRevisionCalculationAt_succ oldVisit
          sourceIndex lowerBound depth archive),
      boundsStrictMono,
      boundsStrictMono.injective,
      by
        intro depth period periodPositive stateEquality
        have indexLt : depth < depth + period := by omega
        have boundEquality :=
          congrArg
            (fun state :
              CanonicalPaidReplayFiniteArchiveRevisionCalculationAt oldVisit
                sourceIndex => state.lowerBound)
            stateEquality
        exact (ne_of_lt (boundsStrictMono indexLt)) boundEquality.symm⟩

/-- The constitutional source witness starts an all-depth revision cascade at
its own cofinal point.  The previous no-finite-truth mouth is preserved as an
exact conjunct. -/
theorem canonicalCofinalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    type_of%
        (canonicalCofinalPaidReplayNoFiniteTruthCompletion_directConsumer
          point) ∧
      type_of%
        (canonicalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
          oldVisit sourceIndex m
          (canonicalCofinalPaidReplayPublicationTag point)) :=
  ⟨canonicalCofinalPaidReplayNoFiniteTruthCompletion_directConsumer point,
    canonicalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
      oldVisit sourceIndex m
        (canonicalCofinalPaidReplayPublicationTag point)⟩

end
end M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade.canonicalPaidReplayFiniteArchiveRevisionStep_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade.canonicalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyPaidReplayFiniteArchiveOpenRevisionCascade.canonicalCofinalPaidReplayFiniteArchiveOpenRevisionCascade_directConsumer
