import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Payment.Action.Producer.SourceGeneratedContributionCapacitySettlementCrossRootPayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Direct consumer of the settlement cross-root payment

Runtime depth eight consumes the paid reopening current-three event as the
source of the generated settlement action.  Its macro next is the settlement
target current selected by that action, not the paid source compiler's Nat
micro-successor and not the target ingress tag alone.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacitySettlementCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedSequentialContributionCapacitySettlement
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment.SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt

abbrev CanonicalSettlementCrossRootPayment :=
  CanonicalContributionCapacitySettlementCrossRootPaymentAt canonicalOldVisit 1

def canonicalSettlementCrossRootPayment : CanonicalSettlementCrossRootPayment :=
  sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
    canonicalOldVisit 1

@[simp] theorem depthEight_paidSourceEvent_exact :
    ninthTick.receipt.1 =
      ContributionCapacitySettlementPaidSourceEventAt canonicalOldVisit 1 :=
  rfl

@[simp] theorem depthEight_resolution_is_paidSettlementAction :
    ninthTick.resolution =
      .actualAction
        (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1) :=
  rfl

@[simp] theorem depthEight_actionReceipt_exact :
    ninthTick.receipt.2 =
      (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
        1).receipt :=
  rfl

set_option linter.defProp false in
def depthEight_next_erasesToGenerated :=
  ninthTick.next_erases_to_generated

@[simp] theorem depthEight_runtimeNextEngine_exact :
    (jointRuntime.stateAt 9).engine = ninthTick.next :=
  rfl

/-- The runtime macro successor is exactly `NextPaidBy` of the cross-root
payment. -/
theorem depthEight_macroNext_erases_to_NextPaidBy :
    (processPresentation .contributionCapacitySettlementTerminal).erase =
      ⟨(generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.TargetN,
        canonicalSettlementCrossRootPayment.nextPaidBy⟩ :=
  rfl

theorem depthEight_NextPaidBy_exact :
    canonicalSettlementCrossRootPayment.nextPaidBy =
      ⟨(generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.TargetV,
        (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.targetVisit⟩ :=
  canonicalSettlementCrossRootPayment.nextPaidBy_exact

/-- Source micro-current and action macro-target use different current
carriers (`Nat` versus `Bool`), so the former cannot be substituted for the
latter. -/
theorem depthEight_sourceMicroCurrentCarrier_ne_macroTargetCarrier :
    (ReopeningVAt canonicalOldVisit 1).Current ≠
      (SettlementVAt canonicalOldVisit).Current :=
  nat_ne_bool

theorem bareSourcePayment_actionReceipt_orFirstSuccessor_cannot_retype_asCrossRootPayment :
    True := by
  let payment := canonicalSettlementCrossRootPayment
  let action :=
    generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit 1
  fail_if_success
    exact (payment.sourcePayment : CanonicalSettlementCrossRootPayment)
  fail_if_success
    exact (payment.actionReceipt : CanonicalSettlementCrossRootPayment)
  fail_if_success
    exact (action.target.firstSuccessor : CanonicalSettlementCrossRootPayment)
  trivial

structure ProofCarryingContributionCapacitySettlementCrossRootPayment : Prop where
  paymentGenerated : Nonempty CanonicalSettlementCrossRootPayment
  paidSourceEventExact :
    ninthTick.receipt.1 =
      ContributionCapacitySettlementPaidSourceEventAt canonicalOldVisit 1
  actionResolutionExact :
    ninthTick.resolution =
      .actualAction
        (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1)
  actionReceiptExact :
    ninthTick.receipt.2 =
      (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
        1).receipt
  runtimeNextEngineExact :
    (jointRuntime.stateAt 9).engine = ninthTick.next
  macroNextErasesToNextPaidBy :
    (processPresentation .contributionCapacitySettlementTerminal).erase =
      ⟨(generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.TargetN,
        canonicalSettlementCrossRootPayment.nextPaidBy⟩
  nextPaidByExact :
    canonicalSettlementCrossRootPayment.nextPaidBy =
      ⟨(generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.TargetV,
        (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
          1).target.targetVisit⟩
  sourceMicroAndMacroCurrentCarriersDistinct :
    (ReopeningVAt canonicalOldVisit 1).Current ≠
      (SettlementVAt canonicalOldVisit).Current

theorem proofCarryingContributionCapacitySettlementCrossRootPayment :
    ProofCarryingContributionCapacitySettlementCrossRootPayment where
  paymentGenerated := ⟨canonicalSettlementCrossRootPayment⟩
  paidSourceEventExact := depthEight_paidSourceEvent_exact
  actionResolutionExact := depthEight_resolution_is_paidSettlementAction
  actionReceiptExact := depthEight_actionReceipt_exact
  runtimeNextEngineExact := depthEight_runtimeNextEngine_exact
  macroNextErasesToNextPaidBy :=
    depthEight_macroNext_erases_to_NextPaidBy
  nextPaidByExact := depthEight_NextPaidBy_exact
  sourceMicroAndMacroCurrentCarriersDistinct :=
    depthEight_sourceMicroCurrentCarrier_ne_macroTargetCarrier

end
end M14ProofCarryingContributionCapacitySettlementCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacitySettlementCrossRootPayment.proofCarryingContributionCapacitySettlementCrossRootPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacitySettlementCrossRootPayment.depthEight_macroNext_erases_to_NextPaidBy
