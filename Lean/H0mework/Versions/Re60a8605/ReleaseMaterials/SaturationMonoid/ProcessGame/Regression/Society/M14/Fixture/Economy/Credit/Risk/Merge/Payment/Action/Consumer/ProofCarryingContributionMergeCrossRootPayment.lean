import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Payment.Action.Producer.SourceGeneratedContributionMergeCrossRootPayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Runtime.SourceGeneratedContributionMergeSupportSeparation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Direct consumer of the contribution-merge cross-root Payment

Runtime depth one uses the Payment's exact revised-root event and action
receipt.  Its macro successor is the generated merge target current, never
the source revised-root micro successor and never an isolated `Unit` tag.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionMergeCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeSupportSeparation
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionMergeCrossRootPayment
open M14SourceGeneratedContributionMergeCrossRootPayment.SourceGeneratedContributionMergeCrossRootPayment

abbrev CanonicalContributionMergeCrossRootPayment :=
  SourceGeneratedContributionMergeCrossRootPayment

def canonicalContributionMergeCrossRootPayment :
    CanonicalContributionMergeCrossRootPayment :=
  sourceGeneratedContributionMergeCrossRootPayment

@[simp] theorem depthOne_sourceEvent_exact :
    secondTick.receipt.1 =
      canonicalContributionMergeCrossRootPayment.sourceEvent :=
  rfl

@[simp] theorem depthOne_resolution_exact :
    secondTick.resolution =
      .actualAction CanonicalContributionMergeAction :=
  rfl

@[simp] theorem depthOne_actionReceipt_exact :
    secondTick.receipt.2 =
      canonicalContributionMergeCrossRootPayment.actionReceipt :=
  rfl

@[simp] theorem depthOne_runtimeNextEngine_exact :
    (jointRuntime.stateAt 2).engine = secondTick.next :=
  rfl

theorem depthOne_macroNext_erases_to_NextPaidBy :
    (processPresentation .contributionCapacityAction).erase =
      ⟨CanonicalContributionMergeAction.target.TargetN,
        canonicalContributionMergeCrossRootPayment.nextPaidBy⟩ :=
  rfl

theorem depthOne_NextPaidBy_exact :
    canonicalContributionMergeCrossRootPayment.nextPaidBy =
      ⟨CanonicalContributionMergeAction.target.TargetV,
        CanonicalContributionMergeAction.target.targetRoot.toAuthoritativeRoot,
        CanonicalContributionMergeAction.target.targetVisit⟩ :=
  canonicalContributionMergeCrossRootPayment.nextPaidBy_exact

theorem depthOne_sourceMicroNetwork_ne_macroNetwork :
    M14SourceGeneratedContributionMergeSupportSeparation.RevisedN ≠
      M14SourceGeneratedContributionMergeSupportSeparation.MergeN :=
  revisedNetwork_ne_mergeNetwork

theorem bareUnit_receipt_write_orSuccessor_cannot_retype_asMergePayment :
    True := by
  let payment := canonicalContributionMergeCrossRootPayment
  fail_if_success
    exact (() : CanonicalContributionMergeCrossRootPayment)
  fail_if_success
    exact (payment.actionReceipt : CanonicalContributionMergeCrossRootPayment)
  fail_if_success
    exact (payment.targetEvent.wholeLedgerWriteBack :
      CanonicalContributionMergeCrossRootPayment)
  fail_if_success
    exact (payment.firstSuccessor : CanonicalContributionMergeCrossRootPayment)
  trivial

structure ProofCarryingContributionMergeCrossRootPayment : Prop where
  paymentGenerated : Nonempty CanonicalContributionMergeCrossRootPayment
  sourceEventExact :
    secondTick.receipt.1 =
      canonicalContributionMergeCrossRootPayment.sourceEvent
  resolutionExact :
    secondTick.resolution =
      .actualAction CanonicalContributionMergeAction
  actionReceiptExact :
    secondTick.receipt.2 =
      canonicalContributionMergeCrossRootPayment.actionReceipt
  everySourceRowEvolved :
    (entry : (contributionMergeInitialLedger
      (actionRootedAt CanonicalContributionMergeOldVisit)).Entry) →
      (canonicalContributionMergeCrossRootPayment.targetEvent
        ).wholeLedgerWriteBack.entryDisposition entry =
        .evolved
          ((contributionMergeFirstEvolution
            (actionRootedAt CanonicalContributionMergeOldVisit)
            canonicalContributionMergeCrossRootPayment.targetEvent.occurrence
          ).destination entry).2
  firstSuccessorExact : HEq
    canonicalContributionMergeCrossRootPayment.firstSuccessor
    CanonicalContributionMergeAction.target.firstSuccessor
  runtimeNextEngineExact :
    (jointRuntime.stateAt 2).engine = secondTick.next
  macroNextErasesToNextPaidBy :
    (processPresentation .contributionCapacityAction).erase =
      ⟨CanonicalContributionMergeAction.target.TargetN,
        canonicalContributionMergeCrossRootPayment.nextPaidBy⟩
  nextPaidByExact :
    canonicalContributionMergeCrossRootPayment.nextPaidBy =
      ⟨CanonicalContributionMergeAction.target.TargetV,
        CanonicalContributionMergeAction.target.targetRoot.toAuthoritativeRoot,
        CanonicalContributionMergeAction.target.targetVisit⟩
  sourceMicroAndMacroNetworksDistinct :
    M14SourceGeneratedContributionMergeSupportSeparation.RevisedN ≠
      M14SourceGeneratedContributionMergeSupportSeparation.MergeN

theorem proofCarryingContributionMergeCrossRootPayment :
    ProofCarryingContributionMergeCrossRootPayment where
  paymentGenerated := ⟨canonicalContributionMergeCrossRootPayment⟩
  sourceEventExact := depthOne_sourceEvent_exact
  resolutionExact := depthOne_resolution_exact
  actionReceiptExact := depthOne_actionReceipt_exact
  everySourceRowEvolved :=
    canonicalContributionMergeCrossRootPayment.everySourceRowEvolved
  firstSuccessorExact :=
    canonicalContributionMergeCrossRootPayment.firstSuccessorExact
  runtimeNextEngineExact := depthOne_runtimeNextEngine_exact
  macroNextErasesToNextPaidBy := depthOne_macroNext_erases_to_NextPaidBy
  nextPaidByExact := depthOne_NextPaidBy_exact
  sourceMicroAndMacroNetworksDistinct :=
    depthOne_sourceMicroNetwork_ne_macroNetwork

end
end M14ProofCarryingContributionMergeCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeCrossRootPayment.proofCarryingContributionMergeCrossRootPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeCrossRootPayment.depthOne_macroNext_erases_to_NextPaidBy
