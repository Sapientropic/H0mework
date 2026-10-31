import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M13.Revision.SelfU8Regression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Policy.UBIPolicyBreakingOccurrence

/-!
# Payment-bearing depth-zero U8 no-free receipt

The initial runtime tick is constitutional rather than an ordinary native
payment: its revised-root `NativeWriteAt` is still `Unit`.  It is nevertheless
not null.  The exact old-root occurrence is the existing depth-zero
source-backed payment occurrence, and the same tick consumes the canonical
coface factorization, attached first write, both revised-row answer-and-next
authorities and the generated revised macro next.

This module reuses that one U8 core.  It adds no revision, occurrence, ledger,
branch enum or stored next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M13SelfU8Regression
open M14UBIPeriodicRootHistory
open M14UBIPolicyBreakingOccurrence

/-- One fixed receipt for runtime depth zero.  Every field consumes an
existing producer at the exact canonical occurrence; no caller supplies a
revision, target current, ledger coverage or next. -/
structure SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt : Prop where
  private mk ::
  sourceRootEventIsPaymentOccurrence :
    (⟨jointVisit.current, firstTick.receipt.1.occurrence⟩ :
      Sigma jointRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt) =
      ⟨(temporalVisitAt 0).current,
        (periodicSourceBackedPaymentAt 0).rootOccurrence.occurrence⟩
  resolutionExact :
    firstTick.resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure jointCore
  cofaceMorphismExact :
    firstTick.receipt.2.1.1 = jointCore.cofaceFactorization.1
  attachedRealizationExact :
    firstTick.receipt.2.1.2 = jointCore.cofaceFactorization.2
  firstWriteExact :
    firstTick.receipt.2.1.2.firstWrite = selfU8.firstWrite
  firstWriteConsumesExact :
    HEq firstTick.receipt.2.1.2.firstWriteConsumes
      selfU8.firstWriteConsumes
  oldAnswerAndNextExact :
    firstTick.receipt.2.2.1 = selfU8.oldRowAnswerAndNext
  newAnswerAndNextExact :
    firstTick.receipt.2.2.2 = selfU8.newRowAnswerAndNext
  revisedRowsShareNext :
    selfU8.oldRowAnswerAndNext.nextCurrent =
      selfU8.newRowAnswerAndNext.nextCurrent
  genuineFirstSplit : Nonempty
    (jointCore.revision.generate).SourceGeneratedFirstWriteGenuineSplitAt
  firstRowsExact :
    ((revisedFirstEvolution.origin revisedLossChildA).1 = oldRevisedEntry) ∧
      ((revisedFirstEvolution.origin revisedLossChildB).1 = oldRevisedEntry) ∧
      ((revisedFirstEvolution.origin revisedTargetObstruction).1 =
        newRevisedEntry) ∧
      revisedLossChildA.progressBudget = 1 ∧
      revisedLossChildB.progressBudget = 1 ∧
      oldRevisedEntry.progressBudget = 2 ∧
      newRevisedEntry.progressBudget = 0

theorem sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt :
    SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt where
  sourceRootEventIsPaymentOccurrence := by
    rfl
  resolutionExact := firstTick_resolution_is_jointCore
  cofaceMorphismExact := rfl
  attachedRealizationExact := rfl
  firstWriteExact := rfl
  firstWriteConsumesExact := HEq.rfl
  oldAnswerAndNextExact := rfl
  newAnswerAndNextExact := rfl
  revisedRowsShareNext := revised_rows_share_one_next
  genuineFirstSplit :=
    ⟨generatedFirstWriteGenuineSplitAt
      M9ProofCarryingRenewalU8Revision.initialOldVisit⟩
  firstRowsExact := revisedFirst_rows_exact

namespace SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

/-- The macro next is read from the existing self-U8 consumption. -/
def nextPaidBy
    (_receipt : SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt) :
    AnyAuthoritativeRootCurrent :=
  selfU8.revisedNext

theorem nextPaidBy_exact
    (receipt : SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt) :
    receipt.nextPaidBy =
      (processPresentation .contributionMergeAction).erase :=
  rfl

end SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

theorem depthZeroU8NoFreeReceipt_hasNoStoredNext : True := by
  let receipt := sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
  fail_if_success exact receipt.next
  fail_if_success exact receipt.target
  fail_if_success exact receipt.future
  trivial

end
end M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.nextPaidBy_exact
