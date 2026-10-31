import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Producer.SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Refusal.NoGo.SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Accountability.Consumer.ProofCarryingContributionCapacityPostSettlementExternalLiability

/-!
# No replay or worthiness authority across the self-U8 recurrence

The next cofinal novelty already supplies the strongest cross-occurrence
negative: different actual paths, one visible normal form, different K, and
no occurrence or authority reconstruction.  The current and next self-U8
Payments are additionally locked to adjacent paid indices, so the old
Payment/self-U8 occurrence cannot impersonate the new one.

Administrative or worthiness labels remain observer readouts.  For every
label family, the current paid pair has no authority factorization, occurrence
left inverse or faithful reconstruction; the label cannot alter the installed
UBI restriction.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14ProofCarryingContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable
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
      current)

include recurrence

/-- Same paid source, now viewed by the existing anti-retaliation producer. -/
def antiRetaliationAt := by
  cases recurrence
  exact sourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
    sourceIndex (paidIndexAt morphism)

theorem antiRetaliationStandingRenewal_isCurrentPaidRenewal :
    (antiRetaliationAt recurrence).standingRenewal =
      currentPaidRenewal recurrence := by
  cases recurrence
  rfl

/-! ## Next cofinal kernel pair -/

theorem nextActualPaths_ne :
    (nextNovelty recurrence).leftReplay.2.actualPath ≠
      (nextNovelty recurrence).rightReplay.2.actualPath :=
  (nextNovelty recurrence).actualPaths_ne

theorem nextSameNormalForm_differentK :
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget (nextNovelty recurrence).leftReplay =
        observer.forget (nextNovelty recurrence).rightReplay ∧
      observer.authorityK (nextNovelty recurrence).leftReplay ≠
        observer.authorityK (nextNovelty recurrence).rightReplay :=
  (nextNovelty recurrence).sameNormalForm_differentK

theorem nextNoOccurrenceReconstruction :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget :=
  (nextNovelty recurrence).noOccurrenceReconstruction

theorem nextNoAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) :=
  (nextNovelty recurrence).noAuthorityFactorization

theorem nextNoFaithfulReconstruction :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) :=
  (nextNovelty recurrence).noFaithfulReconstruction

/-! ## Exact Payment/self-U8 occurrence lock -/

def currentSelfU8PaymentOccurrence :=
  contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
    sourceIndex (paidIndexAt (currentMorphism recurrence))
    (currentPaidRenewal recurrence).sourceConsequence.actualExit

def nextSelfU8PaymentOccurrence :=
  contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
    sourceIndex (paidIndexAt (currentMorphism recurrence) + 1)
    (currentPaidRenewal recurrence).targetConsequence.actualExit

theorem currentAndNextSelfU8PaymentOccurrences_ne :
    currentSelfU8PaymentOccurrence recurrence ≠
      nextSelfU8PaymentOccurrence recurrence := by
  intro occurrenceEquality
  have indexEquality :=
    contributionCapacityPostSettlementGeneratedPaymentOccurrences_indexLocked
      oldVisit sourceIndex
      (currentPaidRenewal recurrence).sourceConsequence.actualExit
      (currentPaidRenewal recurrence).targetConsequence.actualExit
      occurrenceEquality
  omega

/-- False fibre retaining both complete self-U8 morphism certificates and
adding only the forbidden old-Payment-as-next-Payment equality. -/
structure ExactOldSelfU8OccurrenceReplaysAsNextAt : Prop where
  currentMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (currentMorphism recurrence)
  nextMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (nextMorphism recurrence)
  paymentOccurrenceReplayed :
    currentSelfU8PaymentOccurrence recurrence =
      nextSelfU8PaymentOccurrence recurrence

theorem oldSelfU8OccurrenceReplaysAsNext_isEmpty :
    IsEmpty (ExactOldSelfU8OccurrenceReplaysAsNextAt recurrence) :=
  ⟨fun replay =>
    currentAndNextSelfU8PaymentOccurrences_ne recurrence
      replay.paymentOccurrenceReplayed⟩

/-! ## Administrative / worthiness observer no-gos -/

theorem administrativeLabel_noAuthorityFactorization
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ Nonempty
      (AuthorityFactorization
        (administrativeRetaliationObserver oldVisit sourceIndex label)) :=
  administrativeRetaliation_noAuthorityFactorization
    (antiRetaliationAt recurrence) label

theorem administrativeLabel_noOccurrenceLeftInverse
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ ∃ reconstruct : AdministrativeRetaliationVisible →
        AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (administrativeRetaliationObserver oldVisit sourceIndex label
          ).forget :=
  administrativeRetaliation_noOccurrenceLeftInverse
    (antiRetaliationAt recurrence) label

theorem administrativeLabel_noFaithfulReconstruction
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (administrativeRetaliationObserver oldVisit sourceIndex label)) :=
  administrativeRetaliation_noFaithfulReconstruction
    (antiRetaliationAt recurrence) label

omit recurrence in theorem administrativeLabels_doNotChangeInstalledRestriction :
    administrativeEligibilityReadout false =
      administrativeEligibilityReadout true :=
  administrative_labels_do_not_control_renewal

end
end M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo.nextSameNormalForm_differentK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo.nextNoAuthorityFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo.currentAndNextSelfU8PaymentOccurrences_ne
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo.oldSelfU8OccurrenceReplaysAsNext_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo.administrativeLabel_noAuthorityFactorization
