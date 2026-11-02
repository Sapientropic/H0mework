import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Consumer.ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

/-!
# The next registered Society Payment boundary

The current completed self-U8 occurrence is not a missing realization.
This module consumes its paid recurrence and retains the next exact Payment
visit, original row authority and source-generated failure face.  It is the
entry coordinate for a new material source construction, not an installation
certificate for an economic readout.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.FreshPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14ProofCarryingPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt

def registered (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  canonicalProofCarryingPostSettlementObserverPaidSelfU8RecurrenceAt
    oldVisit sourceIndex boundary

def recurrence (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (registered oldVisit sourceIndex boundary).2.val

def span (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  nextSpan (recurrence oldVisit sourceIndex boundary)

def bridge (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    (nextNovelty (recurrence oldVisit sourceIndex boundary))

def visit (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt jointRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (bridge oldVisit sourceIndex boundary).rightRootVisit

def authority (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt jointRoot
      (visit oldVisit sourceIndex boundary) M9ProofCarryingRenewalU8Failure.entry :=
  M9ProofCarryingRenewalU8Failure.authorityAt
    (bridge oldVisit sourceIndex boundary).rightRootVisit

def failureFace (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (bridge oldVisit sourceIndex boundary).rightFailureFace

def rootedFailure (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (bridge oldVisit sourceIndex boundary).rightRootedFailure

theorem payment_is_registered_paid_target (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ((currentPaidRenewal (recurrence oldVisit sourceIndex boundary)).targetConsequence.actualExit
      ).paymentOccurrence = targetPaymentOccurrence (span oldVisit sourceIndex boundary) :=
  currentPaidTargetPayment_isNextSpanPayment (recurrence oldVisit sourceIndex boundary)

theorem payment_is_exact_original_root_event (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (targetPaymentOccurrence (span oldVisit sourceIndex boundary)).rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (visit oldVisit sourceIndex boundary) := by
  exact (span oldVisit sourceIndex boundary).targetPaymentRootOccurrenceExact

theorem completed_payment_cannot_impersonate_next
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    currentSelfU8PaymentOccurrence (recurrence oldVisit sourceIndex boundary) ≠
      nextSelfU8PaymentOccurrence (recurrence oldVisit sourceIndex boundary) :=
  (registered oldVisit sourceIndex boundary).2.property.currentAndNextPaymentOccurrencesDistinct

theorem old_selfU8_replay_is_empty (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IsEmpty (ExactOldSelfU8OccurrenceReplaysAsNextAt
      (recurrence oldVisit sourceIndex boundary)) :=
  (registered oldVisit sourceIndex boundary).2.property.oldSelfU8ReplayEmpty

/-- A build-time source obligation at the exact fresh Payment row.  This
does not expose a runtime branch until its concrete realization is installed. -/
def frontier (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  SourceNativeInquiryCofaceFrontierAt.ofRootFailureFace
    (root := jointRoot) (visit := visit oldVisit sourceIndex boundary)
    (U7 := RootInquiryU8CompletionRegression.U7)
    (calculus := RootInquiryU8CompletionRegression.theoryAuditCalculus)
    (oldTheory := RootInquiryU8CompletionRegression.oldTheory)
    (query := ())
    (event := ULift.up.{1, 0} (jointRoot.emitted
      (visit oldVisit sourceIndex boundary).current))
    (entry := M9ProofCarryingRenewalU8Failure.entry)
    (authority := authority oldVisit sourceIndex boundary)
    (obstruction := RootInquiryU8CompletionRegression.obstruction)
    (u7Gate := RootInquiryU8CompletionRegression.u7Gate)
    (failure := RootInquiryU8CompletionRegression.failure)
    (failureFace oldVisit sourceIndex boundary) rfl
    (M9ProofCarryingRenewalU8Failure.successorAt
      (bridge oldVisit sourceIndex boundary).rightRootVisit)

theorem frontier_uses_registered_failure (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (frontier oldVisit sourceIndex boundary).rooted =
      rootedFailure oldVisit sourceIndex boundary := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.FreshPayment
