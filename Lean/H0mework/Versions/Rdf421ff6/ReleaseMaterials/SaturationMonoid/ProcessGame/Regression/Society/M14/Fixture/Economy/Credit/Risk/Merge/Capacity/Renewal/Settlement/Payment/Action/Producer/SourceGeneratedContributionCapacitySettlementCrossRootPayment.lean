import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Producer.SourceGeneratedContributionCapacityReopeningRuntimePayment
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Action.SourceGeneratedSequentialContributionCapacitySettlement

/-!
# Cross-root payment of the settlement actual action

The settlement action starts at reopening current three.  That exact source
event now carries a compiler-native actual-service payment.  The same event
indexes the generated sequential action, its ingress receipt and the
settlement target's first whole-ledger successor.  The action payment stores
no next or target; its macro successor is read from the action index.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementCrossRootPayment

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementRoot
open M14SourceGeneratedSequentialContributionCapacitySettlement

/-- The action source is definitionally the paid reopening event at positive
current index two, hence local current three. -/
abbrev ContributionCapacitySettlementPaidSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit sourceIndex 2

abbrev ContributionCapacitySettlementPaidActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceGeneratedSequentialActualActionAt
    (contributionCapacitySettlementActionProgramAt oldVisit sourceIndex)
    (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex)

def generatedContributionCapacitySettlementPaidActionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacitySettlementPaidActionAt oldVisit sourceIndex :=
  (contributionCapacitySettlementActionProgramAt oldVisit sourceIndex).generate
    (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex)

@[simp] theorem generatedContributionCapacitySettlementPaidAction_eq_canonical
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    generatedContributionCapacitySettlementPaidActionAt oldVisit sourceIndex =
      generatedContributionCapacitySettlementActionAt oldVisit sourceIndex :=
  rfl

/-- Private action-payment carrier.  The source payment and target receipt are
forced to share the action's exact source event by the action type index. -/
structure SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (action : ContributionCapacitySettlementPaidActionAt oldVisit
      sourceIndex) : Type 10 where
  private mk ::
  sourcePayment :
    SourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex 2
  sourcePaymentWitnessExact :
    contributionCapacityReopeningRuntimePaymentAt oldVisit sourceIndex 2 =
      PLift.up
        (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex
          ).occurrence.2.periodicExitGenerated
  actionReceipt : action.target.Receipt action.answer
  actionReceiptExact : actionReceipt = action.receipt
  targetFirstSuccessorExact :
    action.target.firstSuccessor =
      contributionCapacitySettlementFirstSuccessor oldVisit sourceIndex
        (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex)

abbrev CanonicalContributionCapacitySettlementCrossRootPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt oldVisit
    sourceIndex
    (generatedContributionCapacitySettlementPaidActionAt oldVisit sourceIndex)

def sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    CanonicalContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex where
  sourcePayment :=
    sourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
      sourceIndex 2
  sourcePaymentWitnessExact := rfl
  actionReceipt :=
    (generatedContributionCapacitySettlementPaidActionAt oldVisit sourceIndex
      ).receipt
  actionReceiptExact := rfl
  targetFirstSuccessorExact := rfl

namespace SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt

/-- The macro next is a dependent readout of the generated action target,
never a payment field. -/
def nextPaidBy
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {action : ContributionCapacitySettlementPaidActionAt oldVisit sourceIndex}
    (_payment : SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
      oldVisit sourceIndex action) :=
  action.target.targetAnswerAndNext.nextCurrent

theorem nextPaidBy_exact
    {oldVisit : OldVisit} {sourceIndex : Nat}
    {action : ContributionCapacitySettlementPaidActionAt oldVisit sourceIndex}
    (payment : SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
      oldVisit sourceIndex action) :
    payment.nextPaidBy =
      ⟨action.target.TargetV, action.target.targetRoot.toAuthoritativeRoot,
        action.target.targetVisit⟩ :=
  action.target.targetAnswerAndNext_next_eq

end SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt

theorem contributionCapacitySettlementCrossRootPayment_hasNoNextOrTarget
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let payment :=
    sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex
  fail_if_success exact payment.next
  fail_if_success exact payment.target
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionCapacitySettlementCrossRootPayment
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementCrossRootPayment.sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementCrossRootPayment.SourceGeneratedContributionCapacitySettlementCrossRootPaymentAt.nextPaidBy_exact
