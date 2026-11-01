import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedSequentialContributionCapacityCut
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Payment.Action.Producer.SourceGeneratedContributionMergeCrossRootPayment

/-!
# Structural-debit Payment of the contribution-capacity cut

Depth two is paid by a real complete-ledger debit, not by the target root's
`Unit` native-write tag.  The carrier consumes the preceding merge Payment,
the exact action source, the action receipt, both rows of the target first
write, the strict `1 -> 0` contribution debit, obstruction continuity and the
dependent first successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeCrossRootPayment
open M14SourceGeneratedContributionMergeCrossRootPayment.SourceGeneratedContributionMergeCrossRootPayment
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedSequentialContributionCapacityCut

abbrev CanonicalContributionCapacityCutOldVisit :=
  CanonicalContributionMergeOldVisit

abbrev CanonicalContributionCapacityCutAction :=
  generatedContributionCapacityCutActionAt
    CanonicalContributionCapacityCutOldVisit

def contributionCapacityCutCrossRootTargetEvent :
    ExactTemporalCausalRootEventAt
      CanonicalContributionCapacityCutAction.target.targetRoot.toAuthoritativeRoot.toLedgerRoot
      CanonicalContributionCapacityCutAction.target.targetInitialVisit :=
  CanonicalContributionCapacityCutAction.target.targetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt
      CanonicalContributionCapacityCutAction.target.targetInitialVisit

@[simp] theorem contributionCapacityCutCrossRootTargetEvent_occurrence_exact :
    contributionCapacityCutCrossRootTargetEvent.occurrence =
      contributionCapacityCutEmitted
        (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit) 0 :=
  rfl

theorem contributionCapacityCutCrossRootTargetEvent_wholeLedger_exact :
    contributionCapacityCutCrossRootTargetEvent.wholeLedgerWriteBack =
      .nativeWrite () rfl
        (contributionCapacityCutEmitted
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit) 1)
        (contributionCapacityFirstEvolution
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
          contributionCapacityCutCrossRootTargetEvent.occurrence) :=
  rfl

structure SourceGeneratedContributionCapacityCutCrossRootPayment : Type 10 where
  private mk ::
  sourcePayment : SourceGeneratedContributionMergeCrossRootPayment
  sourceLandingExact : sourcePayment.nextPaidBy =
    ⟨capacityActionSourceVAt CanonicalContributionCapacityCutOldVisit,
      (capacityActionSourceRootAt CanonicalContributionCapacityCutOldVisit
        ).toAuthoritativeRoot,
      capacityActionSourceVisitAt CanonicalContributionCapacityCutOldVisit⟩
  sourceEvent : ExactTemporalCausalRootEventAt
    (capacityActionSourceRootAt CanonicalContributionCapacityCutOldVisit
      ).toAuthoritativeRoot.toLedgerRoot
    (capacityActionSourceVisitAt CanonicalContributionCapacityCutOldVisit)
  sourceEventExact : sourceEvent =
    capacityActionExactSourceEventAt CanonicalContributionCapacityCutOldVisit
  actionReceipt : CanonicalContributionCapacityCutAction.target.Receipt
    CanonicalContributionCapacityCutAction.answer
  actionReceiptExact : actionReceipt =
    CanonicalContributionCapacityCutAction.receipt
  targetEvent : ExactTemporalCausalRootEventAt
    CanonicalContributionCapacityCutAction.target.targetRoot.toAuthoritativeRoot.toLedgerRoot
    CanonicalContributionCapacityCutAction.target.targetInitialVisit
  targetEventExact : targetEvent =
    contributionCapacityCutCrossRootTargetEvent
  targetWholeLedgerExact : targetEvent.wholeLedgerWriteBack =
    .nativeWrite () rfl
      (contributionCapacityCutEmitted
        (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit) 1)
      (contributionCapacityFirstEvolution
        (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
        targetEvent.occurrence)
  everySourceRowCovered :
    (entry : (contributionCapacityCutInitialLedger
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)).Entry) →
      contributionCapacityFirstSourceEntryAt
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
          (contributionCapacityFirstSourceEntryIndex
            (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
            entry) = entry
  everyTargetRowCovered :
    (entry : (contributionCapacityCutTargetLedger
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)).Entry) →
      contributionCapacityFirstTargetEntryAt
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
          (contributionCapacityFirstTargetEntryIndex
            (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
            entry) = entry
  strictDebitDispositionExact :
    targetEvent.wholeLedgerWriteBack.entryDisposition
        (initialContribution
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)) =
      .evolved actionReceipt.strictDebit
  obstructionContinuityDispositionExact :
    targetEvent.wholeLedgerWriteBack.entryDisposition
        (initialObstruction
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)) =
      .evolved actionReceipt.obstructionContinuity
  firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    targetEvent.occurrence targetEvent.wholeLedgerWriteBack
  firstSuccessorExact : HEq firstSuccessor
    CanonicalContributionCapacityCutAction.target.firstSuccessor

def sourceGeneratedContributionCapacityCutCrossRootPayment :
    SourceGeneratedContributionCapacityCutCrossRootPayment where
  sourcePayment := sourceGeneratedContributionMergeCrossRootPayment
  sourceLandingExact :=
    sourceGeneratedContributionMergeCrossRootPayment.nextPaidBy_exact
  sourceEvent :=
    capacityActionExactSourceEventAt CanonicalContributionCapacityCutOldVisit
  sourceEventExact := rfl
  actionReceipt := CanonicalContributionCapacityCutAction.receipt
  actionReceiptExact := rfl
  targetEvent := contributionCapacityCutCrossRootTargetEvent
  targetEventExact := rfl
  targetWholeLedgerExact :=
    contributionCapacityCutCrossRootTargetEvent_wholeLedger_exact
  everySourceRowCovered :=
    contributionCapacityFirstSourceEntryAt_index
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
  everyTargetRowCovered :=
    contributionCapacityFirstTargetEntryAt_index
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
  strictDebitDispositionExact := by
    rw [contributionCapacityCutCrossRootTargetEvent_wholeLedger_exact]
    rfl
  obstructionContinuityDispositionExact := by
    rw [contributionCapacityCutCrossRootTargetEvent_wholeLedger_exact]
    rfl
  firstSuccessor := contributionCapacityRootFirstSuccessor
    (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
  firstSuccessorExact := HEq.rfl

namespace SourceGeneratedContributionCapacityCutCrossRootPayment

def nextPaidBy
    (_payment : SourceGeneratedContributionCapacityCutCrossRootPayment) :=
  CanonicalContributionCapacityCutAction.target.targetAnswerAndNext.nextCurrent

theorem nextPaidBy_exact
    (payment : SourceGeneratedContributionCapacityCutCrossRootPayment) :
    payment.nextPaidBy =
      ⟨CanonicalContributionCapacityCutAction.target.TargetV,
        CanonicalContributionCapacityCutAction.target.targetRoot.toAuthoritativeRoot,
        CanonicalContributionCapacityCutAction.target.targetVisit⟩ :=
  CanonicalContributionCapacityCutAction.target.targetAnswerAndNext_next_eq

end SourceGeneratedContributionCapacityCutCrossRootPayment

theorem contributionCapacityCutCrossRootPayment_hasNoStoredNext : True := by
  let payment := sourceGeneratedContributionCapacityCutCrossRootPayment
  fail_if_success exact payment.next
  fail_if_success exact payment.target
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionCapacityCutCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutCrossRootPayment.sourceGeneratedContributionCapacityCutCrossRootPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutCrossRootPayment.SourceGeneratedContributionCapacityCutCrossRootPayment.nextPaidBy_exact
