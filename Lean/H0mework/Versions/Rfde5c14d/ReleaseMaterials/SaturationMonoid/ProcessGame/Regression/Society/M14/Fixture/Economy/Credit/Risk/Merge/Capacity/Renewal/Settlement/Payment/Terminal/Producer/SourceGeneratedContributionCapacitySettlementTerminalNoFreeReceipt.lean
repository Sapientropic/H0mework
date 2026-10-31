import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Action.SourceGeneratedContributionCapacitySettlementState

/-!
# Faithful-terminal no-free receipt

The settlement terminal is not a native payment.  Its exact occurrence
discharges every Fin-3 source row and has no local ledger successor; the
living root's already installed terminal-handoff law alone generates the
survivor current.  This dependent receipt keeps terminal and payment
authorities disjoint without introducing a new outcome enum.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
open M14SourceGeneratedContributionCapacitySettlementRoot
open M14SourceGeneratedContributionCapacitySettlementState

def contributionCapacitySettlementTerminalRootEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactTemporalCausalRootEventAt
      (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (CanonicalContributionCapacitySettlementActionAt oldVisit sourceIndex
        ).target.targetVisit :=
  (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
    ).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (CanonicalContributionCapacitySettlementActionAt oldVisit sourceIndex
        ).target.targetVisit

def contributionCapacitySettlementTerminalExactAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacitySettlementExactTerminal oldVisit sourceIndex
    (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
      sourceIndex)

@[simp] theorem contributionCapacitySettlementTerminalRootEvent_occurrence_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).occurrence =
      (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
        ).emitted true :=
  rfl

theorem contributionCapacitySettlementTerminalWholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      .faithfulTerminal .settled rfl
        (contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution :=
  rfl

theorem contributionCapacitySettlementTerminalEveryRow_terminal
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (entry : (contributionCapacitySettlementFullLedger oldVisit).Entry) :
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition entry =
      .terminal
        ((contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution.discharge entry) := by
  rw [contributionCapacitySettlementTerminalWholeLedger_exact]
  rfl

def contributionCapacitySettlementTerminalAnswerAndNextAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
    ).generatedCausalEntryAnswerAndNextAt
      (CanonicalContributionCapacitySettlementActionAt oldVisit sourceIndex
        ).target.targetVisit
      (CanonicalContributionCapacitySettlementActionAt oldVisit sourceIndex
        ).target.targetEntry
      (CanonicalContributionCapacitySettlementActionAt oldVisit sourceIndex
        ).target.targetAuthority

/-- Handoff-generated world next; not a local ledger successor field. -/
def contributionCapacitySettlementTerminalNextPaidBy
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  (contributionCapacitySettlementTerminalAnswerAndNextAt oldVisit sourceIndex
    ).nextCurrent

theorem contributionCapacitySettlementTerminalNextPaidBy_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacitySettlementTerminalNextPaidBy oldVisit sourceIndex =
      ⟨ContributionCapacitySettlementSurvivorVAt oldVisit,
        contributionCapacitySettlementSurvivorAuthoritativeRoot oldVisit
          sourceIndex
          (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
            sourceIndex),
        contributionCapacitySettlementSurvivorInitialVisit oldVisit sourceIndex
          (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
            sourceIndex)⟩ :=
  rfl

structure SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  private mk ::
  exactTerminal : Nonempty
    (SourceFaithfulTerminalOccurrenceAt
      (CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
        ).source.base
      ((CanonicalContributionCapacitySettlementRootAt oldVisit sourceIndex
        ).emitted true))
  wholeLedgerTerminalExact :
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack =
      .faithfulTerminal .settled rfl
        (contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution
  everyRowTerminal : ∀
      entry : (contributionCapacitySettlementFullLedger oldVisit).Entry,
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition entry =
      .terminal
        ((contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution.discharge entry)
  noLocalLedgerSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
        ).occurrence
      (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
        ).wholeLedgerWriteBack)
  nextPaidByExact :
    contributionCapacitySettlementTerminalNextPaidBy oldVisit sourceIndex =
      ⟨ContributionCapacitySettlementSurvivorVAt oldVisit,
        contributionCapacitySettlementSurvivorAuthoritativeRoot oldVisit
          sourceIndex
          (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
            sourceIndex),
        contributionCapacitySettlementSurvivorInitialVisit oldVisit sourceIndex
          (CanonicalContributionCapacitySettlementSourceEventAt oldVisit
            sourceIndex)⟩

theorem sourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
      oldVisit sourceIndex where
  exactTerminal :=
    ⟨contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex⟩
  wholeLedgerTerminalExact :=
    contributionCapacitySettlementTerminalWholeLedger_exact oldVisit
      sourceIndex
  everyRowTerminal :=
    contributionCapacitySettlementTerminalEveryRow_terminal oldVisit
      sourceIndex
  noLocalLedgerSuccessor :=
    ⟨fun successor => nomatch successor⟩
  nextPaidByExact :=
    contributionCapacitySettlementTerminalNextPaidBy_exact oldVisit
      sourceIndex

end
end M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt.sourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt.contributionCapacitySettlementTerminalNextPaidBy_exact
