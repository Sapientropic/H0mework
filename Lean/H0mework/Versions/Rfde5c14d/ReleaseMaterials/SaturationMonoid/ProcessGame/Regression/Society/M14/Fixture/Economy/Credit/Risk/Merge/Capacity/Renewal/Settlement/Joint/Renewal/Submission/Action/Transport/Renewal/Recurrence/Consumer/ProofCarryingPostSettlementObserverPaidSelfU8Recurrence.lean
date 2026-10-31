import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.NoGo.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo

/-!
# Proof-carrying recurrence of renewed authority through self-U8

The consumer retains the current paid-renewal checkpoint, the exact
old-right/new-left and paid-target/new-right splice, the independently
source-generated next authority/morphism, and the next PCL/self-U8 chain.  It
also retains cross-path normal-form/K nonreconstruction, adjacent Payment
occurrence separation and universal administrative-label no-gos.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo

structure ProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    {morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority}
    {current :
      ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt morphism}
    (recurrence :
      SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt morphism
        current) : Prop where
  private mk ::
  currentCertificate :
    ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
      (currentMorphism recurrence)
  oldRightIsNextLeft :
    (nextNovelty recurrence).leftReplay =
      rightReplayAt oldVisit sourceIndex boundary
  oldRightPayloadIsCurrentSpan :
    (nextNovelty recurrence).leftReplay.2 =
      replay (legislationSpan (currentMorphism recurrence))
  nextSpanIsNextRight :
    replay (nextSpan recurrence) = (nextNovelty recurrence).rightReplay.2
  paidTargetIsNextSourceEvent :
    (currentPaidRenewal recurrence).targetConsequence.outerRootEvent =
      (sourceSubmission (nextSpan recurrence)).exactEvent
  paidTargetIsNextSpanPayment :
    ((currentPaidRenewal recurrence).targetConsequence.actualExit
      ).paymentOccurrence = targetPaymentOccurrence (nextSpan recurrence)
  nextAuthorityIsFreshInput :
    (nextMorphism recurrence).sourceAuthority = nextAuthority recurrence
  nextDispositionInstalled :
    transportedDisposition (nextMorphism recurrence) =
      (activatedSubmissionAt oldVisit sourceIndex (boundary + 1)
        ).payload.disposition
  nextMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (nextMorphism recurrence)
  nextCycleMouthExact :
    (nextCycle recurrence).2.2.1 = nextMorphism recurrence
  nextActualPathsDistinct :
    (nextNovelty recurrence).leftReplay.2.actualPath ≠
      (nextNovelty recurrence).rightReplay.2.actualPath
  nextSameNormalDifferentK :
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget (nextNovelty recurrence).leftReplay =
        observer.forget (nextNovelty recurrence).rightReplay ∧
      observer.authorityK (nextNovelty recurrence).leftReplay ≠
        observer.authorityK (nextNovelty recurrence).rightReplay
  nextNoOccurrenceReconstruction :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget
  nextNoAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex))
  nextNoFaithfulReconstruction :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex))
  currentAndNextPaymentOccurrencesDistinct :
    currentSelfU8PaymentOccurrence recurrence ≠
      nextSelfU8PaymentOccurrence recurrence
  oldSelfU8ReplayEmpty :
    IsEmpty (ExactOldSelfU8OccurrenceReplaysAsNextAt recurrence)
  antiRetaliationUsesCurrentRenewal :
    (antiRetaliationAt recurrence).standingRenewal =
      currentPaidRenewal recurrence
  administrativeNoAuthority :
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      ¬ Nonempty
        (AuthorityFactorization
          (administrativeRetaliationObserver oldVisit sourceIndex label))
  administrativeNoOccurrenceReconstruction :
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      ¬ ∃ reconstruct : AdministrativeRetaliationVisible →
          AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex,
        Function.LeftInverse reconstruct
          (administrativeRetaliationObserver oldVisit sourceIndex label
            ).forget
  administrativeNoFaithfulReconstruction :
    ∀ label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
        Bool,
      ¬ Nonempty
        (FaithfulAuthorityReconstruction
          (administrativeRetaliationObserver oldVisit sourceIndex label))
  administrativeLabelsDoNotChangeRestriction :
    administrativeEligibilityReadout false =
      administrativeEligibilityReadout true

/-- Independent consumer of one generated recurrence splice. -/
theorem proofCarryingPostSettlementObserverPaidSelfU8Recurrence
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {span :
      SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
        oldVisit sourceIndex boundary}
    {authority :
      SourceNativeObserverConsumerRootedAuthorityAt (sourceSubmission span)}
    {morphism :
      SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
        span authority}
    {current :
      ProofCarryingPostSettlementObserverPaidSuccessorRenewalAt morphism}
    (recurrence :
      SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt morphism
        current) :
    ProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt recurrence where
  currentCertificate := recurrence.currentCertificate
  oldRightIsNextLeft := recurrence.nextNoveltyLeft_isCurrentRightReplay
  oldRightPayloadIsCurrentSpan :=
    recurrence.nextNoveltyLeftPayload_isCurrentSpanReplay
  nextSpanIsNextRight := recurrence.nextSpanReplay_isNextNoveltyRight
  paidTargetIsNextSourceEvent :=
    recurrence.currentPaidTargetEvent_isNextSourceEvent
  paidTargetIsNextSpanPayment :=
    recurrence.currentPaidTargetPayment_isNextSpanPayment
  nextAuthorityIsFreshInput :=
    recurrence.nextMorphism_sourceAuthority_isFreshInput
  nextDispositionInstalled := recurrence.nextMorphism_disposition_isInstalled
  nextMorphismCertificate := recurrence.nextMorphismCertificate
  nextCycleMouthExact := recurrence.nextCycle_morphism_isGeneratedNext
  nextActualPathsDistinct := nextActualPaths_ne recurrence
  nextSameNormalDifferentK := nextSameNormalForm_differentK recurrence
  nextNoOccurrenceReconstruction := nextNoOccurrenceReconstruction recurrence
  nextNoAuthorityFactorization := nextNoAuthorityFactorization recurrence
  nextNoFaithfulReconstruction := nextNoFaithfulReconstruction recurrence
  currentAndNextPaymentOccurrencesDistinct :=
    currentAndNextSelfU8PaymentOccurrences_ne recurrence
  oldSelfU8ReplayEmpty := oldSelfU8OccurrenceReplaysAsNext_isEmpty recurrence
  antiRetaliationUsesCurrentRenewal :=
    antiRetaliationStandingRenewal_isCurrentPaidRenewal recurrence
  administrativeNoAuthority := fun label =>
    administrativeLabel_noAuthorityFactorization recurrence label
  administrativeNoOccurrenceReconstruction := fun label =>
    administrativeLabel_noOccurrenceLeftInverse recurrence label
  administrativeNoFaithfulReconstruction := fun label =>
    administrativeLabel_noFaithfulReconstruction recurrence label
  administrativeLabelsDoNotChangeRestriction :=
    administrativeLabels_doNotChangeInstalledRestriction

/-- Closed current checkpoint, generated recurrence and direct consumer. -/
abbrev AnyProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  Sigma fun paid :
      AnyProofCarryingPostSettlementObserverPaidSuccessorRenewalAt oldVisit
        sourceIndex boundary =>
    { recurrence :
        SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
          paid.1.2.2.1 paid.2 //
      ProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt recurrence }

def canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnyProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt oldVisit
      sourceIndex boundary :=
  let paid :=
    canonicalProofCarryingPostSettlementObserverPaidSuccessorRenewalAt
      oldVisit sourceIndex boundary
  let recurrence :=
    sourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
      paid.1.2.2.1 paid.2
  ⟨paid, ⟨recurrence,
    proofCarryingPostSettlementObserverPaidSelfU8Recurrence recurrence⟩⟩

end
end M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence.proofCarryingPostSettlementObserverPaidSelfU8Recurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence.canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
