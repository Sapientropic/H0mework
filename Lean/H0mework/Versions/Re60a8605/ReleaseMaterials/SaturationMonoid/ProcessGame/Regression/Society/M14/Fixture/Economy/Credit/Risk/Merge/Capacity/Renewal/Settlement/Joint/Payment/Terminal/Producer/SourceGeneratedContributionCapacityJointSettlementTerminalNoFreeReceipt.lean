import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Payment.Action.Producer.SourceGeneratedContributionCapacityJointSettlementCrossRootPayment

/-!
# Joint-settlement faithful-terminal no-free receipt

The actual action Payment lands at the exact `Bool true` current.  That current
is a faithful terminal: its complete `Fin 2` ledger is discharged, it has no
local ledger successor, and only the already installed terminal-handoff law
generates the first post-settlement current.  This is a separate source object
from the action Payment, not a compressed two-step receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedSequentialContributionCapacityJointSettlement
open M14SourceGeneratedContributionCapacityJointSettlementState
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment
open M14SourceGeneratedContributionCapacityJointSettlementCrossRootPayment.SourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt

def contributionCapacityJointSettlementTerminalRootEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactTemporalCausalRootEventAt
      (CanonicalJointRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetVisit :=
  (CanonicalJointRootAt oldVisit sourceIndex
    ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetVisit

def contributionCapacityJointSettlementTerminalExactAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityJointSettlementExactTerminal oldVisit sourceIndex
    (CanonicalJointMaterialAt oldVisit sourceIndex)

@[simp] theorem contributionCapacityJointSettlementTerminalRootEvent_occurrence_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit sourceIndex
      ).occurrence =
      (CanonicalJointRootAt oldVisit sourceIndex).emitted true :=
  rfl

theorem contributionCapacityJointSettlementTerminalWholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      .faithfulTerminal .settled rfl
        (contributionCapacityJointSettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution :=
  rfl

theorem contributionCapacityJointSettlementTerminalEveryRow_terminal
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex) =
      .terminal
        ((contributionCapacityJointSettlementTerminalExactAt oldVisit
          sourceIndex).ledgerEvolution.discharge
            (contributionCapacityJointSettlementLiveEntryAt oldVisit
              entryIndex)) := by
  rw [contributionCapacityJointSettlementTerminalWholeLedger_exact]
  rfl

def contributionCapacityJointSettlementTerminalAnswerAndNextAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  (CanonicalJointRootAt oldVisit sourceIndex
    ).generatedCausalEntryAnswerAndNextAt
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetVisit
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetEntry
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetAuthority

/-- Handoff-generated macro next, not a local successor. -/
def contributionCapacityJointSettlementTerminalNextPaidBy
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  (contributionCapacityJointSettlementTerminalAnswerAndNextAt oldVisit
    sourceIndex).nextCurrent

theorem contributionCapacityJointSettlementTerminalNextPaidBy_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacityJointSettlementTerminalNextPaidBy oldVisit sourceIndex =
      ⟨PostSettlementRenewalVAt oldVisit,
        contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
          sourceIndex,
        contributionCapacityPostSettlementRenewalInitialVisit oldVisit
          sourceIndex⟩ :=
  rfl

/-- The action Payment reaches exactly the terminal root/current/visit consumed
by this separate receipt. -/
theorem contributionCapacityJointSettlementActionNext_isTerminalCurrent
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
        oldVisit sourceIndex).nextPaidBy =
      ⟨ContributionCapacityJointSettlementVAt oldVisit,
        (CanonicalJointRootAt oldVisit sourceIndex).toAuthoritativeRoot,
        (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
          sourceIndex).target.targetVisit⟩ :=
  (sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
    oldVisit sourceIndex).nextPaidBy_exact

structure SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 13 where
  private mk ::
  sourceActionPayment :
    CanonicalContributionCapacityJointSettlementCrossRootPaymentAt oldVisit
      sourceIndex
  sourceActionNextExact : sourceActionPayment.nextPaidBy =
    ⟨ContributionCapacityJointSettlementVAt oldVisit,
      (CanonicalJointRootAt oldVisit sourceIndex).toAuthoritativeRoot,
      (generatedContributionCapacityJointSettlementPaidActionAt oldVisit
        sourceIndex).target.targetVisit⟩
  exactTerminal : Nonempty
    (SourceFaithfulTerminalOccurrenceAt
      (CanonicalJointRootAt oldVisit sourceIndex).source.base
      ((CanonicalJointRootAt oldVisit sourceIndex).emitted true))
  wholeLedgerTerminalExact :
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      .faithfulTerminal .settled rfl
        (contributionCapacityJointSettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution
  everyRowTerminal : ∀ entryIndex : Fin 2,
    (contributionCapacityJointSettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex) =
      .terminal
        ((contributionCapacityJointSettlementTerminalExactAt oldVisit
          sourceIndex).ledgerEvolution.discharge
            (contributionCapacityJointSettlementLiveEntryAt oldVisit
              entryIndex))
  noLocalLedgerSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityJointSettlementTerminalRootEventAt oldVisit
        sourceIndex).occurrence
      (contributionCapacityJointSettlementTerminalRootEventAt oldVisit
        sourceIndex).wholeLedgerWriteBack)
  nextPaidByExact :
    contributionCapacityJointSettlementTerminalNextPaidBy oldVisit sourceIndex =
      ⟨PostSettlementRenewalVAt oldVisit,
        contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
          sourceIndex,
        contributionCapacityPostSettlementRenewalInitialVisit oldVisit
          sourceIndex⟩

def sourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
      oldVisit sourceIndex where
  sourceActionPayment :=
    sourceGeneratedContributionCapacityJointSettlementCrossRootPaymentAt
      oldVisit sourceIndex
  sourceActionNextExact :=
    contributionCapacityJointSettlementActionNext_isTerminalCurrent oldVisit
      sourceIndex
  exactTerminal :=
    ⟨contributionCapacityJointSettlementTerminalExactAt oldVisit sourceIndex⟩
  wholeLedgerTerminalExact :=
    contributionCapacityJointSettlementTerminalWholeLedger_exact oldVisit
      sourceIndex
  everyRowTerminal :=
    contributionCapacityJointSettlementTerminalEveryRow_terminal oldVisit
      sourceIndex
  noLocalLedgerSuccessor := ⟨fun successor => nomatch successor⟩
  nextPaidByExact :=
    contributionCapacityJointSettlementTerminalNextPaidBy_exact oldVisit
      sourceIndex

theorem contributionCapacityJointSettlementTerminalReceipt_hasNoLocalNext
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let receipt :=
    sourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
      oldVisit sourceIndex
  fail_if_success exact receipt.localSuccessor
  fail_if_success exact receipt.target
  fail_if_success exact receipt.future
  trivial

end
end M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt.sourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceiptAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt.contributionCapacityJointSettlementActionNext_isTerminalCurrent
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementTerminalNoFreeReceipt.contributionCapacityJointSettlementTerminalNextPaidBy_exact
