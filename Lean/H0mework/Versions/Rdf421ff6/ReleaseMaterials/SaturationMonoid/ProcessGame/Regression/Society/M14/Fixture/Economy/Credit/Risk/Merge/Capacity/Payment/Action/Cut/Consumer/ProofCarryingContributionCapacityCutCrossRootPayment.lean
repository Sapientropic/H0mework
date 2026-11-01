import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Payment.Action.Cut.Producer.SourceGeneratedContributionCapacityCutCrossRootPayment
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.SourceGeneratedContributionCapacitySupportSeparation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Direct consumer of the contribution-capacity cut Payment

The third runtime tick consumes the canonical merge-root event and its
structural-debit Payment.  Complete Fin-2 coverage, `1 -> 0`, `0 -> 0`, the
target first successor and the macro next are one authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityCutCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionCapacitySupportSeparation
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityCutCrossRootPayment
open M14SourceGeneratedContributionCapacityCutCrossRootPayment.SourceGeneratedContributionCapacityCutCrossRootPayment

abbrev CanonicalContributionCapacityCutCrossRootPayment :=
  SourceGeneratedContributionCapacityCutCrossRootPayment

def canonicalContributionCapacityCutCrossRootPayment :
    CanonicalContributionCapacityCutCrossRootPayment :=
  sourceGeneratedContributionCapacityCutCrossRootPayment

@[simp] theorem depthTwo_sourceEvent_exact :
    thirdTick.receipt.1 =
      canonicalContributionCapacityCutCrossRootPayment.sourceEvent :=
  rfl

@[simp] theorem depthTwo_resolution_exact :
    thirdTick.resolution =
      .actualAction CanonicalContributionCapacityCutAction :=
  rfl

@[simp] theorem depthTwo_actionReceipt_exact :
    thirdTick.receipt.2 =
      canonicalContributionCapacityCutCrossRootPayment.actionReceipt :=
  rfl

@[simp] theorem depthTwo_runtimeNextEngine_exact :
    (jointRuntime.stateAt 3).engine = thirdTick.next :=
  rfl

theorem depthTwo_macroNext_erases_to_NextPaidBy :
    (processPresentation .contributionCapacityFailure).erase =
      ⟨CanonicalContributionCapacityCutAction.target.TargetN,
        canonicalContributionCapacityCutCrossRootPayment.nextPaidBy⟩ :=
  rfl

theorem depthTwo_NextPaidBy_exact :
    canonicalContributionCapacityCutCrossRootPayment.nextPaidBy =
      ⟨CanonicalContributionCapacityCutAction.target.TargetV,
        CanonicalContributionCapacityCutAction.target.targetRoot.toAuthoritativeRoot,
        CanonicalContributionCapacityCutAction.target.targetVisit⟩ :=
  canonicalContributionCapacityCutCrossRootPayment.nextPaidBy_exact

theorem depthTwo_mergeNetwork_ne_capacityNetwork :
    M14SourceGeneratedContributionMergeSupportSeparation.MergeN ≠
      M14SourceGeneratedContributionCapacitySupportSeparation.CapacityN := by
  intro network_eq
  exact mergeSupport_ne_capacitySupport
    (congrArg WorldRelationNetwork.Support network_eq)

theorem depthTwo_sourceMicroCurrent_ne_macroCurrent : (2 : Nat) ≠ 1 := by
  decide

theorem bareUnit_receipt_debit_write_orSuccessor_cannot_retype_asCapacityPayment :
    True := by
  let payment := canonicalContributionCapacityCutCrossRootPayment
  fail_if_success
    exact (() : CanonicalContributionCapacityCutCrossRootPayment)
  fail_if_success
    exact (payment.actionReceipt :
      CanonicalContributionCapacityCutCrossRootPayment)
  fail_if_success
    exact (payment.actionReceipt.strictDebit :
      CanonicalContributionCapacityCutCrossRootPayment)
  fail_if_success
    exact (payment.actionReceipt.obstructionContinuity :
      CanonicalContributionCapacityCutCrossRootPayment)
  fail_if_success
    exact (payment.targetEvent.wholeLedgerWriteBack :
      CanonicalContributionCapacityCutCrossRootPayment)
  fail_if_success
    exact (payment.firstSuccessor :
      CanonicalContributionCapacityCutCrossRootPayment)
  trivial

structure ProofCarryingContributionCapacityCutCrossRootPayment : Prop where
  paymentGenerated :
    Nonempty CanonicalContributionCapacityCutCrossRootPayment
  sourceEventExact :
    thirdTick.receipt.1 =
      canonicalContributionCapacityCutCrossRootPayment.sourceEvent
  resolutionExact :
    thirdTick.resolution =
      .actualAction CanonicalContributionCapacityCutAction
  actionReceiptExact :
    thirdTick.receipt.2 =
      canonicalContributionCapacityCutCrossRootPayment.actionReceipt
  completeSourceCoverage :
    (entry : (contributionCapacityCutInitialLedger
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)).Entry) →
      contributionCapacityFirstSourceEntryAt
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
          (contributionCapacityFirstSourceEntryIndex
            (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
            entry) = entry
  completeTargetCoverage :
    (entry : (contributionCapacityCutTargetLedger
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)).Entry) →
      contributionCapacityFirstTargetEntryAt
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
          (contributionCapacityFirstTargetEntryIndex
            (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
            entry) = entry
  sourceBudgetOne :
    (initialContribution
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
      ).progressBudget = 1
  targetBudgetZero :
    (contributionCapacityCutTargetContribution
      (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
      ).progressBudget = 0
  strictDebitDispositionExact :
    (canonicalContributionCapacityCutCrossRootPayment.targetEvent
      ).wholeLedgerWriteBack.entryDisposition
          (initialContribution
            (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)) =
      .evolved
        canonicalContributionCapacityCutCrossRootPayment.actionReceipt.strictDebit
  obstructionContinuityDispositionExact :
    (canonicalContributionCapacityCutCrossRootPayment.targetEvent
      ).wholeLedgerWriteBack.entryDisposition
          (initialObstruction
            (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)) =
      .evolved
        canonicalContributionCapacityCutCrossRootPayment.actionReceipt.obstructionContinuity
  firstSuccessorExact : HEq
    canonicalContributionCapacityCutCrossRootPayment.firstSuccessor
    CanonicalContributionCapacityCutAction.target.firstSuccessor
  runtimeNextEngineExact :
    (jointRuntime.stateAt 3).engine = thirdTick.next
  macroNextErasesToNextPaidBy :
    (processPresentation .contributionCapacityFailure).erase =
      ⟨CanonicalContributionCapacityCutAction.target.TargetN,
        canonicalContributionCapacityCutCrossRootPayment.nextPaidBy⟩
  nextPaidByExact :
    canonicalContributionCapacityCutCrossRootPayment.nextPaidBy =
      ⟨CanonicalContributionCapacityCutAction.target.TargetV,
        CanonicalContributionCapacityCutAction.target.targetRoot.toAuthoritativeRoot,
        CanonicalContributionCapacityCutAction.target.targetVisit⟩
  sourceMicroAndMacroNetworksDistinct :
    M14SourceGeneratedContributionMergeSupportSeparation.MergeN ≠
      M14SourceGeneratedContributionCapacitySupportSeparation.CapacityN
  sourceMicroAndMacroCurrentsDistinct : (2 : Nat) ≠ 1

theorem proofCarryingContributionCapacityCutCrossRootPayment :
    ProofCarryingContributionCapacityCutCrossRootPayment where
  paymentGenerated := ⟨canonicalContributionCapacityCutCrossRootPayment⟩
  sourceEventExact := depthTwo_sourceEvent_exact
  resolutionExact := depthTwo_resolution_exact
  actionReceiptExact := depthTwo_actionReceipt_exact
  completeSourceCoverage :=
    canonicalContributionCapacityCutCrossRootPayment.everySourceRowCovered
  completeTargetCoverage :=
    canonicalContributionCapacityCutCrossRootPayment.everyTargetRowCovered
  sourceBudgetOne :=
    canonicalContributionCapacityCutCrossRootPayment.actionReceipt.sourceBudgetOne
  targetBudgetZero :=
    canonicalContributionCapacityCutCrossRootPayment.actionReceipt.targetBudgetZero
  strictDebitDispositionExact :=
    canonicalContributionCapacityCutCrossRootPayment.strictDebitDispositionExact
  obstructionContinuityDispositionExact :=
    canonicalContributionCapacityCutCrossRootPayment.obstructionContinuityDispositionExact
  firstSuccessorExact :=
    canonicalContributionCapacityCutCrossRootPayment.firstSuccessorExact
  runtimeNextEngineExact := depthTwo_runtimeNextEngine_exact
  macroNextErasesToNextPaidBy := depthTwo_macroNext_erases_to_NextPaidBy
  nextPaidByExact := depthTwo_NextPaidBy_exact
  sourceMicroAndMacroNetworksDistinct :=
    depthTwo_mergeNetwork_ne_capacityNetwork
  sourceMicroAndMacroCurrentsDistinct :=
    depthTwo_sourceMicroCurrent_ne_macroCurrent

end
end M14ProofCarryingContributionCapacityCutCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCutCrossRootPayment.proofCarryingContributionCapacityCutCrossRootPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityCutCrossRootPayment.depthTwo_macroNext_erases_to_NextPaidBy
