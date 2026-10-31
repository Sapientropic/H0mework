import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Assembly.ProofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Payment.Producer.SourceGeneratedContributionCapacityPostSettlementOccurrencePayment

/-!
# No divergent next from payment-proof selection

For every Payment shape used by the canonical history, `NextPaidBy` is fixed
by its source/action index rather than by proof or receipt selection.  The
remaining compiler-native receipts are Props indexed by their exact root
occurrence, so two proofs at one index are identical.  These are pointwise
coherence laws, not a stored history or future schedule.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityNoDivergentPaidNext

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
open M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
open M14SourceGeneratedContributionMergeCrossRootPayment
open M14SourceGeneratedContributionMergeCrossRootPayment.SourceGeneratedContributionMergeCrossRootPayment
open M14SourceGeneratedContributionCapacityCutCrossRootPayment
open M14SourceGeneratedContributionCapacityCutCrossRootPayment.SourceGeneratedContributionCapacityCutCrossRootPayment
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityReopeningActionPayment
open M14SourceGeneratedContributionCapacityReopeningActionPayment.ContributionCapacityReopeningActionPaymentAt
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment.SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
open M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt
open M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment.PostSettlementOccurrencePaymentAt

theorem depthZero_nextPaidBy_proofIndependent
    (left right :
      SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt) :
    left.nextPaidBy = right.nextPaidBy :=
  rfl

theorem depthOne_nextPaidBy_proofIndependent
    (left right : SourceGeneratedContributionMergeCrossRootPayment) :
    left.nextPaidBy = right.nextPaidBy :=
  rfl

theorem depthTwo_nextPaidBy_proofIndependent
    (left right : SourceGeneratedContributionCapacityCutCrossRootPayment) :
    left.nextPaidBy = right.nextPaidBy :=
  rfl

theorem reopeningAction_nextPaidBy_proofIndependent
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (left right : ContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex) :
    left.nextPaidBy = right.nextPaidBy :=
  rfl

theorem settlementAction_nextPaidBy_proofIndependent
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {action : ContributionCapacitySettlementPaidActionAt oldVisit sourceIndex}
    (left right :
      SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
        oldVisit sourceIndex action) :
    left.nextPaidBy = right.nextPaidBy :=
  rfl

theorem postSettlement_nextPaidBy_proofIndependent
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (left right : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit) :
    left.nextPaidBy = right.nextPaidBy := by
  change left.successor.targetOccurrence = right.successor.targetOccurrence
  have successor_eq : left.successor = right.successor := by
    change (show PUnit from left.successor) =
      (show PUnit from right.successor)
    exact Subsingleton.elim _ _
  rw [successor_eq]

theorem u8RuntimeReceipt_proofIndependent
    (oldVisit : OldVisit) (index : Nat)
    (left right : SourceGeneratedContributionCapacityU8RuntimePaymentAt
      oldVisit index) : left = right :=
  Subsingleton.elim _ _

theorem u8RevisionReceipt_proofIndependent
    (oldVisit : OldVisit)
    (left right : SourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
      oldVisit) : left = right :=
  Subsingleton.elim _ _

theorem reopeningRuntimeReceipt_proofIndependent
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (left right : SourceGeneratedContributionCapacityReopeningRuntimePaymentAt
      oldVisit sourceIndex index) : left = right :=
  Subsingleton.elim _ _

theorem terminalReceipt_proofIndependent
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
        oldVisit sourceIndex) : left = right :=
  Subsingleton.elim _ _

theorem survivorRuntimeReceipt_proofIndependent
    (index : Nat)
    (left right :
      SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
        index) : left = right :=
  Subsingleton.elim _ _

structure ProofCarryingContributionCapacityNoDivergentPaidNext : Prop where
  depthZero : ∀ left right :
    SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt,
      left.nextPaidBy = right.nextPaidBy
  depthOne : ∀ left right : SourceGeneratedContributionMergeCrossRootPayment,
    left.nextPaidBy = right.nextPaidBy
  depthTwo : ∀ left right :
    SourceGeneratedContributionCapacityCutCrossRootPayment,
      left.nextPaidBy = right.nextPaidBy
  reopeningAction : ∀ {oldVisit : OldVisit} {sourceIndex : Nat}
    (left right : ContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex), left.nextPaidBy = right.nextPaidBy
  settlementAction : ∀ {oldVisit : OldVisit} {sourceIndex : Nat}
    {action : ContributionCapacitySettlementPaidActionAt oldVisit sourceIndex}
    (left right :
      SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
        oldVisit sourceIndex action), left.nextPaidBy = right.nextPaidBy
  postSettlement : ∀ {oldVisit : OldVisit} {sourceIndex index : Nat}
    {rootEvent : ExactTemporalCausalRootEventAt
      (ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
        index)}
    {actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)}
    (left right : PostSettlementOccurrencePaymentAt oldVisit sourceIndex index
      rootEvent actualExit), left.nextPaidBy = right.nextPaidBy
  u8Runtime : ∀ (oldVisit : OldVisit) (index : Nat)
    (left right : SourceGeneratedContributionCapacityU8RuntimePaymentAt
      oldVisit index), left = right
  u8Revision : ∀ (oldVisit : OldVisit)
    (left right : SourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt
      oldVisit), left = right
  reopeningRuntime : ∀ (oldVisit : OldVisit) (sourceIndex index : Nat)
    (left right : SourceGeneratedContributionCapacityReopeningRuntimePaymentAt
      oldVisit sourceIndex index), left = right
  terminal : ∀ (oldVisit : OldVisit) (sourceIndex : Nat)
    (left right :
      SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
        oldVisit sourceIndex), left = right
  survivorRuntime : ∀ (index : Nat)
    (left right :
      SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
        index), left = right

theorem proofCarryingContributionCapacityNoDivergentPaidNext :
    ProofCarryingContributionCapacityNoDivergentPaidNext where
  depthZero := depthZero_nextPaidBy_proofIndependent
  depthOne := depthOne_nextPaidBy_proofIndependent
  depthTwo := depthTwo_nextPaidBy_proofIndependent
  reopeningAction := reopeningAction_nextPaidBy_proofIndependent
  settlementAction := settlementAction_nextPaidBy_proofIndependent
  postSettlement := postSettlement_nextPaidBy_proofIndependent
  u8Runtime := u8RuntimeReceipt_proofIndependent
  u8Revision := u8RevisionReceipt_proofIndependent
  reopeningRuntime := reopeningRuntimeReceipt_proofIndependent
  terminal := terminalReceipt_proofIndependent
  survivorRuntime := survivorRuntimeReceipt_proofIndependent

end
end M14ProofCarryingContributionCapacityNoDivergentPaidNext
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityNoDivergentPaidNext.proofCarryingContributionCapacityNoDivergentPaidNext
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityNoDivergentPaidNext.postSettlement_nextPaidBy_proofIndependent
