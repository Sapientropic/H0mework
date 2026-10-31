import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Action.Reopening.Producer.SourceGeneratedContributionCapacityReopeningActionPayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Payment.Consumer.ProofCarryingContributionCapacityU8RuntimePayment

/-!
# Direct consumer of the cross-root reopening-action payment

The canonical depth-five action is paid only when its exact receipt-selected
actual exit, target current-zero native write, complete target evolution and
target first successor occur together.  Its paid next is the action target's
macro answer-and-next; the source capacity-U8 micro next cannot inhabit that
target-world type.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityReopeningActionPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningActionSource
open M14SourceGeneratedSequentialContributionCapacityReopening
open M14SourceGeneratedContributionCapacityReopeningActionPayment
open M14SourceGeneratedContributionCapacityReopeningActionPayment.ContributionCapacityReopeningActionPaymentAt
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14ProofCarryingContributionCapacityU8RuntimePayment
open M14UBIPeriodicRootHistory

theorem contributionCapacityReopeningActionOuterSourceEvent_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex).sourceEvent =
      contributionCapacityU8RuntimePaymentRootEventAt oldVisit
        (sourceIndex + 2) :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).sourceEventExact

theorem contributionCapacityReopeningActionOuterSourcePayment_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit
      (sourceIndex + 2) :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).sourcePayment

theorem contributionCapacityReopeningActionSource_receipt_sameActualExit
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.sourceActualExit = payment.receiptActualExit :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).sourceReceiptActualExitExact

theorem contributionCapacityReopeningActionReceipt_targetWrite_sameActualExit
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.receiptActualExit = payment.targetActualExit :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).receiptTargetActualExitExact

theorem contributionCapacityReopeningActionSource_actualExit_choice_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.sourceActualExit =
      Classical.choice
        (contributionCapacityReopeningActionSourceActualExitAuthorityAt
          oldVisit sourceIndex payment.sourceWrite) :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).sourceActualExitChoiceExact

theorem contributionCapacityReopeningActionReceipt_actualExit_choice_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.receiptActualExit =
      Classical.choice
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).receipt.periodicActualExitGenerated :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).receiptActualExitChoiceExact

theorem contributionCapacityReopeningActionTarget_actualExit_choice_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetActualExit = Classical.choice payment.targetWrite.down :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).targetActualExitChoiceExact

theorem contributionCapacityReopeningActionPayment_targetNativeWrite_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetEvent.wholeLedgerWriteBack =
      .nativeWrite payment.targetWrite rfl
        (contributionCapacityReopeningEmitted oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex) 1)
        (contributionCapacityReopeningEvolution oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex) payment.targetEvent.occurrence) :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).targetWholeLedgerNativeWriteExact

theorem contributionCapacityReopeningActionPayment_everyTargetRow_evolved
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 3) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetEvent.wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningCurrentEntryAt oldVisit 0 entryIndex) =
      .evolved
        (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
          sourceIndex entryIndex) :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).everyTargetRowEvolved entryIndex

theorem contributionCapacityReopeningActionPayment_firstSuccessor_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    HEq
      (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex).firstSuccessor
      (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
        ).target.firstSuccessor :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).firstSuccessorExact

theorem contributionCapacityReopeningActionPayment_macroNext_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex).nextPaidBy =
      ⟨(CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.TargetV,
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetRoot.toAuthoritativeRoot,
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetVisit⟩ :=
  ContributionCapacityReopeningActionPaymentAt.nextPaidBy_exact oldVisit
    sourceIndex

/-- A receipt, native write or successor is only one projection of the
cross-root authority and cannot retype as the private Payment. -/
theorem bareReceipt_write_or_successor_cannot_retype_asReopeningActionPayment
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let action :=
    CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
  let payment :=
    sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex
  fail_if_success
    exact (action.receipt :
      ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex)
  fail_if_success
    exact (payment.targetWrite :
      ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex)
  fail_if_success
    exact (payment.targetEvent.wholeLedgerWriteBack :
      ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex)
  fail_if_success
    exact (payment.firstSuccessor :
      ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex)
  trivial

/-- The old capacity-U8 root's micro next has a different world index from
the action-generated reopening macro next. -/
theorem sourceU8MicroNext_cannot_retype_asReopeningActionMacroNext
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let sourceMicroNext :=
    (contributionCapacityReopeningActionSourceRootAt oldVisit
      ).generatedNextCurrentAt
        (contributionCapacityReopeningActionSourceVisitAt oldVisit sourceIndex)
  fail_if_success
    exact (sourceMicroNext :
      SourceNativeAuthoritativeRootCurrentAt (ReopeningNAt oldVisit))
  trivial

structure ProofCarryingContributionCapacityReopeningActionPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  payment : Nonempty
    (ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex)
  outerSourceEventExact :
    (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex).sourceEvent =
      contributionCapacityU8RuntimePaymentRootEventAt oldVisit
        (sourceIndex + 2)
  outerSourcePayment :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit
      (sourceIndex + 2)
  sourceActualExitChoiceExact :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.sourceActualExit =
      Classical.choice
        (contributionCapacityReopeningActionSourceActualExitAuthorityAt
          oldVisit sourceIndex payment.sourceWrite)
  receiptActualExitChoiceExact :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.receiptActualExit =
      Classical.choice
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).receipt.periodicActualExitGenerated
  targetActualExitChoiceExact :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetActualExit = Classical.choice payment.targetWrite.down
  sourceAndReceiptActualExitSame :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.sourceActualExit = payment.receiptActualExit
  actionReceiptPeriodicPaymentGenerated :
    Nonempty (PeriodicSourceBackedPaymentAt
      (contributionCapacityReopeningDepthAt sourceIndex))
  receiptAndTargetActualExitSame :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.receiptActualExit = payment.targetActualExit
  targetNativeWriteExact :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetEvent.wholeLedgerWriteBack =
      .nativeWrite payment.targetWrite rfl
        (contributionCapacityReopeningEmitted oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex) 1)
        (contributionCapacityReopeningEvolution oldVisit sourceIndex
          (contributionCapacityReopeningActionExactSourceEventAt oldVisit
            sourceIndex) payment.targetEvent.occurrence)
  everyTargetRowEvolved : ∀ entryIndex : Fin 3,
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetEvent.wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningCurrentEntryAt oldVisit 0 entryIndex) =
      .evolved
        (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
          sourceIndex entryIndex)
  firstSuccessorExact : HEq
    (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex).firstSuccessor
    (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
      ).target.firstSuccessor
  macroNextExact :
    (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex).nextPaidBy =
      ⟨(CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.TargetV,
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetRoot.toAuthoritativeRoot,
        (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
          ).target.targetVisit⟩

theorem proofCarryingContributionCapacityReopeningActionPayment
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex where
  payment :=
    ⟨sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex⟩
  outerSourceEventExact :=
    contributionCapacityReopeningActionOuterSourceEvent_exact oldVisit
      sourceIndex
  outerSourcePayment :=
    contributionCapacityReopeningActionOuterSourcePayment_exact oldVisit
      sourceIndex
  sourceActualExitChoiceExact :=
    contributionCapacityReopeningActionSource_actualExit_choice_exact oldVisit
      sourceIndex
  receiptActualExitChoiceExact :=
    contributionCapacityReopeningActionReceipt_actualExit_choice_exact oldVisit
      sourceIndex
  targetActualExitChoiceExact :=
    contributionCapacityReopeningActionTarget_actualExit_choice_exact oldVisit
      sourceIndex
  sourceAndReceiptActualExitSame :=
    contributionCapacityReopeningActionSource_receipt_sameActualExit oldVisit
      sourceIndex
  actionReceiptPeriodicPaymentGenerated :=
    (CanonicalContributionCapacityReopeningActionAt oldVisit sourceIndex
      ).receipt.periodicPaymentGenerated
  receiptAndTargetActualExitSame :=
    contributionCapacityReopeningActionReceipt_targetWrite_sameActualExit
      oldVisit sourceIndex
  targetNativeWriteExact :=
    contributionCapacityReopeningActionPayment_targetNativeWrite_exact oldVisit
      sourceIndex
  everyTargetRowEvolved :=
    contributionCapacityReopeningActionPayment_everyTargetRow_evolved oldVisit
      sourceIndex
  firstSuccessorExact :=
    contributionCapacityReopeningActionPayment_firstSuccessor_exact oldVisit
      sourceIndex
  macroNextExact :=
    contributionCapacityReopeningActionPayment_macroNext_exact oldVisit
      sourceIndex

structure CanonicalContributionCapacityReopeningActionPaymentCertificate :
    Prop where
  outerU8RuntimePayment :
    ProofCarryingContributionCapacityU8RuntimePayment
  crossRootPayment :
    ProofCarryingContributionCapacityReopeningActionPaymentAt canonicalOldVisit
      1
  depthFiveActionExact :
    sixthTick.resolution =
      .actualAction
        (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1)
  depthFiveOuterSourceEventExact :
    sixthTick.receipt.1 =
      contributionCapacityU8RuntimePaymentRootEventAt canonicalOldVisit 3
  depthFiveNextPreservesTargetRoot : HEq
    (processPresentation (.contributionCapacityReopened 0)).state.base.root
    (generatedContributionCapacityReopeningActionAt canonicalOldVisit 1
      ).target.targetRoot

theorem canonicalContributionCapacityReopeningActionPaymentCertificate :
    CanonicalContributionCapacityReopeningActionPaymentCertificate where
  outerU8RuntimePayment :=
    proofCarryingContributionCapacityU8RuntimePayment
  crossRootPayment :=
    proofCarryingContributionCapacityReopeningActionPayment canonicalOldVisit 1
  depthFiveActionExact :=
    sixthTick_resolution_is_contributionCapacityReopening
  depthFiveOuterSourceEventExact :=
    depthFive_U8PaidSourceEvent_exact
  depthFiveNextPreservesTargetRoot :=
    sixthTick_next_preserves_contributionCapacityReopeningRoot

end
end M14ProofCarryingContributionCapacityReopeningActionPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningActionPayment.proofCarryingContributionCapacityReopeningActionPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityReopeningActionPayment.canonicalContributionCapacityReopeningActionPaymentCertificate
