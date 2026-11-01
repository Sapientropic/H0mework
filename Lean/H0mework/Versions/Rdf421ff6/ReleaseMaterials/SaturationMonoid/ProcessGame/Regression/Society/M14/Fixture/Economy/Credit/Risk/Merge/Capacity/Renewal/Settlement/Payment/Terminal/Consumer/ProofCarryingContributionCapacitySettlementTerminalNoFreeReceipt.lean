import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Payment.Terminal.Producer.SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Direct consumer of the faithful-terminal no-free receipt

Runtime depth nine consumes the exact complete terminal occurrence.  Its
answer-and-next is the living-root handoff to the two-row survivor world;
there is constructively no local ledger successor that could be relabelled as
a payment.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt

@[simp] theorem depthNine_terminalRootEvent_exact :
    tenthTick.receipt.1 =
      contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1 :=
  rfl

@[simp] theorem depthNine_resolution_is_terminalAnswer :
    tenthTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementTerminalAnswerFaceAt canonicalOldVisit 1)
        (contributionCapacitySettlementTerminalAnswerConsumerAt
          canonicalOldVisit 1) :=
  tenthTick_is_generated_settlement_terminal_answer

@[simp] theorem depthNine_answerAndNext_exact :
    tenthTick.receipt.2.2 =
      contributionCapacitySettlementTerminalAnswerAndNextAt canonicalOldVisit
        1 :=
  rfl

@[simp] theorem depthNine_exactFaithfulTerminal :
    tenthTickExactFaithfulTerminal =
      contributionCapacitySettlementTerminalExactAt canonicalOldVisit 1 :=
  rfl

@[simp] theorem depthNine_runtimeNextEngine_exact :
    (jointRuntime.stateAt 10).engine = tenthTick.next :=
  rfl

theorem depthNine_macroLanding_is_handoffGenerated :
    tenthTick.receipt.2.2.nextCurrent =
      contributionCapacitySettlementTerminalNextPaidBy canonicalOldVisit 1 :=
  rfl

theorem bareTerminalAnswer_orReceipt_cannot_retype_asNativePayment : True := by
  fail_if_success
    exact (tenthTick.receipt.2.2 :
      ContributionCapacitySettlementSurvivorExactWholeLedgerPaymentAt 10)
  fail_if_success
    exact (tenthTickExactFaithfulTerminal :
      ContributionCapacitySettlementSurvivorExactWholeLedgerPaymentAt 10)
  trivial

structure ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt :
    Prop where
  receipt :
    SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
      canonicalOldVisit 1
  rootEventExact :
    tenthTick.receipt.1 =
      contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1
  resolutionExact :
    tenthTick.resolution =
      .directlyAnswered
        (contributionCapacitySettlementTerminalAnswerFaceAt canonicalOldVisit 1)
        (contributionCapacitySettlementTerminalAnswerConsumerAt
          canonicalOldVisit 1)
  answerAndNextExact :
    tenthTick.receipt.2.2 =
      contributionCapacitySettlementTerminalAnswerAndNextAt canonicalOldVisit
        1
  exactTerminal :
    tenthTickExactFaithfulTerminal =
      contributionCapacitySettlementTerminalExactAt canonicalOldVisit 1
  runtimeNextEngineExact :
    (jointRuntime.stateAt 10).engine = tenthTick.next
  macroLandingHandoffGenerated :
    tenthTick.receipt.2.2.nextCurrent =
      contributionCapacitySettlementTerminalNextPaidBy canonicalOldVisit 1

theorem proofCarryingContributionCapacitySettlementTerminalNoFreeReceipt :
    ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt where
  receipt :=
    sourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
      canonicalOldVisit 1
  rootEventExact := depthNine_terminalRootEvent_exact
  resolutionExact := depthNine_resolution_is_terminalAnswer
  answerAndNextExact := depthNine_answerAndNext_exact
  exactTerminal := depthNine_exactFaithfulTerminal
  runtimeNextEngineExact := depthNine_runtimeNextEngine_exact
  macroLandingHandoffGenerated :=
    depthNine_macroLanding_is_handoffGenerated

end
end M14ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt.proofCarryingContributionCapacitySettlementTerminalNoFreeReceipt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt.depthNine_macroLanding_is_handoffGenerated
