import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Action.SourceGeneratedSequentialContributionMerge
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.DepthZero.Producer.SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

/-!
# Cross-root payment of the contribution-merge action

The revised-root source compiler and the merge target compiler still use
`Unit` as a structural native-write tag.  The tag is not the payment.  This
private carrier jointly consumes the preceding payment-bearing U8 receipt,
the exact revised-root action occurrence, the action receipt, the complete
target first write and its dependent first successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalU8Revision
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedSequentialContributionMerge
open M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
open M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

abbrev CanonicalContributionMergeOldVisit :=
  M9ProofCarryingRenewalU8Revision.initialOldVisit

abbrev CanonicalContributionMergeAction :=
  generatedContributionMergeActionAt CanonicalContributionMergeOldVisit

def contributionMergeCrossRootTargetEvent :
    ExactTemporalCausalRootEventAt
      CanonicalContributionMergeAction.target.targetRoot.toAuthoritativeRoot.toLedgerRoot
      CanonicalContributionMergeAction.target.targetInitialVisit :=
  CanonicalContributionMergeAction.target.targetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt
      CanonicalContributionMergeAction.target.targetInitialVisit

@[simp] theorem contributionMergeCrossRootTargetEvent_occurrence_exact :
    contributionMergeCrossRootTargetEvent.occurrence =
      contributionMergeEmitted
        (actionRootedAt CanonicalContributionMergeOldVisit) 0 :=
  rfl

theorem contributionMergeCrossRootTargetEvent_wholeLedger_exact :
    contributionMergeCrossRootTargetEvent.wholeLedgerWriteBack =
      .nativeWrite () rfl
        (contributionMergeEmitted
          (actionRootedAt CanonicalContributionMergeOldVisit) 1)
        (contributionMergeFirstEvolution
          (actionRootedAt CanonicalContributionMergeOldVisit)
          contributionMergeCrossRootTargetEvent.occurrence) :=
  rfl

/-- Fixed-history d1 Payment.  It stores no macro next or target network. -/
structure SourceGeneratedContributionMergeCrossRootPayment : Type 10 where
  private mk ::
  sourceNoFreeReceipt :
    SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
  sourceLandingExact : sourceNoFreeReceipt.nextPaidBy =
    (M9ProofCarryingRenewalInquiryRuntime.processPresentation
      .contributionMergeAction).erase
  sourceEvent : ExactTemporalCausalRootEventAt
    (actionSourceRootAt CanonicalContributionMergeOldVisit
      ).toAuthoritativeRoot.toLedgerRoot
    (actionSourceVisitAt CanonicalContributionMergeOldVisit)
  sourceEventExact : sourceEvent =
    actionExactSourceEventAt CanonicalContributionMergeOldVisit
  actionReceipt : CanonicalContributionMergeAction.target.Receipt
    CanonicalContributionMergeAction.answer
  actionReceiptExact : actionReceipt = CanonicalContributionMergeAction.receipt
  targetEvent : ExactTemporalCausalRootEventAt
    CanonicalContributionMergeAction.target.targetRoot.toAuthoritativeRoot.toLedgerRoot
    CanonicalContributionMergeAction.target.targetInitialVisit
  targetEventExact : targetEvent = contributionMergeCrossRootTargetEvent
  targetWholeLedgerExact : targetEvent.wholeLedgerWriteBack =
    .nativeWrite () rfl
      (contributionMergeEmitted
        (actionRootedAt CanonicalContributionMergeOldVisit) 1)
      (contributionMergeFirstEvolution
        (actionRootedAt CanonicalContributionMergeOldVisit)
        targetEvent.occurrence)
  everySourceRowEvolved :
    (entry : (contributionMergeInitialLedger
      (actionRootedAt CanonicalContributionMergeOldVisit)).Entry) →
      targetEvent.wholeLedgerWriteBack.entryDisposition entry =
        .evolved
          ((contributionMergeFirstEvolution
            (actionRootedAt CanonicalContributionMergeOldVisit)
            targetEvent.occurrence).destination entry).2
  firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    targetEvent.occurrence targetEvent.wholeLedgerWriteBack
  firstSuccessorExact : HEq firstSuccessor
    CanonicalContributionMergeAction.target.firstSuccessor

def sourceGeneratedContributionMergeCrossRootPayment :
    SourceGeneratedContributionMergeCrossRootPayment where
  sourceNoFreeReceipt :=
    sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
  sourceLandingExact :=
    sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.nextPaidBy_exact
  sourceEvent :=
    actionExactSourceEventAt CanonicalContributionMergeOldVisit
  sourceEventExact := rfl
  actionReceipt := CanonicalContributionMergeAction.receipt
  actionReceiptExact := rfl
  targetEvent := contributionMergeCrossRootTargetEvent
  targetEventExact := rfl
  targetWholeLedgerExact :=
    contributionMergeCrossRootTargetEvent_wholeLedger_exact
  everySourceRowEvolved := by
    intro entry
    rw [contributionMergeCrossRootTargetEvent_wholeLedger_exact]
    rfl
  firstSuccessor := contributionMergeRootFirstSuccessor
    (actionRootedAt CanonicalContributionMergeOldVisit)
  firstSuccessorExact := HEq.rfl

namespace SourceGeneratedContributionMergeCrossRootPayment

def nextPaidBy (_payment : SourceGeneratedContributionMergeCrossRootPayment) :=
  CanonicalContributionMergeAction.target.targetAnswerAndNext.nextCurrent

theorem nextPaidBy_exact
    (payment : SourceGeneratedContributionMergeCrossRootPayment) :
    payment.nextPaidBy =
      ⟨CanonicalContributionMergeAction.target.TargetV,
        CanonicalContributionMergeAction.target.targetRoot.toAuthoritativeRoot,
        CanonicalContributionMergeAction.target.targetVisit⟩ :=
  CanonicalContributionMergeAction.target.targetAnswerAndNext_next_eq

end SourceGeneratedContributionMergeCrossRootPayment

theorem contributionMergeCrossRootPayment_hasNoStoredNext : True := by
  let payment := sourceGeneratedContributionMergeCrossRootPayment
  fail_if_success exact payment.next
  fail_if_success exact payment.target
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionMergeCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeCrossRootPayment.sourceGeneratedContributionMergeCrossRootPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeCrossRootPayment.SourceGeneratedContributionMergeCrossRootPayment.nextPaidBy_exact
