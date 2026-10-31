import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Source.SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication

/-!
# Proof-carrying canonical cofinal paid-replay kernel escape

The fivefold constitution's own self-U8 observer pair now produces a witness
at the same cofinal point.  The coarse paid-replay observer remains
non-faithful; honest publication restores reconstruction only on its exact
generated two-point restriction.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyCofinalPaidReplayKernelEscape

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14SourceGeneratedCanonicalSocietyCofinalPaidReplayWitnessPublication

theorem canonicalCofinalPaidReplay_twoPointPosteriorReconstruction
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    let refinement := canonicalCofinalPaidReplayKernelRefinementAt point
    Nonempty
        (FaithfulAuthorityReconstruction refinement.twoPointObserver) ∧
      Nonempty (AuthorityFactorization refinement.twoPointObserver) := by
  dsimp
  let refinement := canonicalCofinalPaidReplayKernelRefinementAt point
  exact
    ⟨⟨refinement.twoPointFaithfulAuthorityReconstruction⟩,
      ⟨refinement.twoPointAuthorityFactorization⟩⟩

/-- Full same-point consumer.  Its only input is the already generated
canonical cofinal point. -/
theorem canonicalCofinalPaidReplayKernelEscape_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel m : Nat}
    {pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel m}
    (point : CanonicalSocietyCofinalPointMaterialAt initial observerFuel m
      pulse) :
    let O := contributionCapacityPostSettlementPaidReplayPulseObserver
      oldVisit sourceIndex
    let pair := canonicalCofinalPaidReplayKernelPairAt point
    let refinement := canonicalCofinalPaidReplayKernelRefinementAt point
    Nonempty (AuthorityKernelPair O) ∧
      Nonempty
        (SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point pair.left) ∧
      IsEmpty
        (SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point pair.right) ∧
      (∀ replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
          sourceIndex,
        canonicalCofinalPaidReplayPublicationTag point replay = true ↔
          Nonempty
            (SourceGeneratedCanonicalCofinalPaidReplayWitnessAt point replay)) ∧
      O.forget pair.left = O.forget pair.right ∧
      O.authorityK pair.left ≠ O.authorityK pair.right ∧
      type_of% pair.noOccurrenceLeftInverse ∧
      ¬ Nonempty (AuthorityFactorization O) ∧
      ¬ Nonempty (FaithfulAuthorityReconstruction O) ∧
      (canonicalCofinalPaidReplayRefinedObserverAt point).forget pair.left ≠
        (canonicalCofinalPaidReplayRefinedObserverAt point).forget pair.right ∧
      Nonempty
        (FaithfulAuthorityReconstruction refinement.twoPointObserver) ∧
      Nonempty (AuthorityFactorization refinement.twoPointObserver) ∧
      type_of% point.selfU8Tick.nextMorphismCertificate ∧
      type_of% point.selfU8Tick.paidTargetIsNextSourceEvent ∧
      type_of% point.selfU8Tick.paidTargetIsNextSpanPayment ∧
      type_of% point.selfU8Tick.nextCycleMouthExact ∧
      type_of% point.selfU8Tick.currentAndNextPaymentOccurrencesDistinct := by
  dsimp
  let pair := canonicalCofinalPaidReplayKernelPairAt point
  let refinement := canonicalCofinalPaidReplayKernelRefinementAt point
  exact
    ⟨⟨pair⟩,
      ⟨sourceGeneratedCanonicalCofinalPaidReplayWitnessAt point⟩,
      canonicalCofinalPaidReplayKernelPair_rightWitness_isEmpty point,
      canonicalCofinalPaidReplayPublicationTag_true_iff point,
      pair.visible_eq,
      pair.authority_ne,
      pair.noOccurrenceLeftInverse,
      pair.noAuthorityFactorization,
      pair.noFaithfulAuthorityReconstruction,
      canonicalCofinalPaidReplay_refinedVisible_ne point,
      (canonicalCofinalPaidReplay_twoPointPosteriorReconstruction point).1,
      (canonicalCofinalPaidReplay_twoPointPosteriorReconstruction point).2,
      point.selfU8Tick.nextMorphismCertificate,
      point.selfU8Tick.paidTargetIsNextSourceEvent,
      point.selfU8Tick.paidTargetIsNextSpanPayment,
      point.selfU8Tick.nextCycleMouthExact,
      point.selfU8Tick.currentAndNextPaymentOccurrencesDistinct⟩

end
end M14ProofCarryingCanonicalSocietyCofinalPaidReplayKernelEscape
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyCofinalPaidReplayKernelEscape.canonicalCofinalPaidReplay_twoPointPosteriorReconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyCofinalPaidReplayKernelEscape.canonicalCofinalPaidReplayKernelEscape_directConsumer
