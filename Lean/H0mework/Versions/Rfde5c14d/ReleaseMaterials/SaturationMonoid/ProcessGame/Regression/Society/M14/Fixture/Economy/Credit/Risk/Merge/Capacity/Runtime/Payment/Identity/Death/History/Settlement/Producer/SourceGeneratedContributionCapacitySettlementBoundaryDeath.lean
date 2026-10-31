import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.History.Reopening.Producer.SourceGeneratedContributionCapacityReopeningRenewalDeath
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Payment.Action.Consumer.ProofCarryingContributionCapacitySettlementCrossRootPayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Payment.Terminal.Consumer.ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Consumer.SourceGeneratedContributionCapacitySettlementConsumer

/-!
# Arithmetic death at the settlement boundary

Runtime depth eight pays the existing reopening event.  The generated action
then enters the settlement root through a separate `.ingress` native write;
that target ingress is not a second actual-service Payment.  Its complete
three-row compiler write carries the inherited contribution row on the same
old lineage with budget `0 -> 0`, so every strict same-debt renewal fibre at
that boundary is empty.

Runtime depth nine is authority-disjoint again: `NativeWriteAt true` is empty,
while the exact occurrence is an inventory-complete faithful terminal with no
local ledger successor.  Its installed handoff sends the contribution row to
the survivor under the existing debt origin.  Thus depth nine is terminal
separation and same-debt handoff, not a later arithmetic-payment edge and not
the first arithmetic death.  No root, process, ledger, history, registry,
date, Payment or completed future is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementBoundaryDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningState
open M14SourceGeneratedContributionCapacityReopeningRenewalDeath
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementConsumer
open M14SourceGeneratedSequentialContributionCapacitySettlement
open M14SourceGeneratedContributionCapacitySettlementRoot
open M14SourceGeneratedContributionCapacitySettlementCrossRootPayment
open M14ProofCarryingContributionCapacitySettlementCrossRootPayment
open M14SourceGeneratedContributionCapacitySettlementTerminalNoFreeReceipt
open M14ProofCarryingContributionCapacitySettlementTerminalNoFreeReceipt

/-! ## Depth-eight paid source and authority-separated target ingress -/

/-- The full-ledger row zero is definitionally the inherited contribution,
not the independently generated residual row. -/
def contributionCapacitySettlementBoundaryContributionAt
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementFullLedger oldVisit).Entry :=
  contributionCapacitySettlementFullEntryAt oldVisit (0 : Fin 3)

@[simp] theorem contributionCapacitySettlementBoundaryContribution_content_exact
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementBoundaryContributionAt oldVisit).1 =
      (contributionCapacityU8InheritedContribution oldVisit).1 :=
  rfl

@[simp] theorem contributionCapacitySettlementBoundaryContribution_claim_exact
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementBoundaryContributionAt oldVisit).claim =
      (contributionCapacityU8InheritedContribution oldVisit).claim :=
  rfl

@[simp] theorem contributionCapacitySettlementBoundaryContribution_budget_zero
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementBoundaryContributionAt oldVisit
      ).progressBudget = 0 :=
  contributionCapacityReopeningTargetEntry_budget_zero oldVisit _

/-- Existing pre-revision origin of the inherited contribution.  This is
consumed as provenance and is not reconstructed from the visible budget. -/
abbrev ContributionCapacitySettlementBoundaryInheritedOriginAt
    (oldVisit : OldVisit) :=
  ContributionCapacityReopeningU8ContributionOriginAt oldVisit

def contributionCapacitySettlementBoundaryInheritedOriginAt
    (oldVisit : OldVisit) :
    ContributionCapacitySettlementBoundaryInheritedOriginAt oldVisit :=
  contributionCapacityReopeningU8ContributionOriginAt oldVisit

/-- The target ingress root event generated by the exact paid reopening
source event. -/
def contributionCapacitySettlementBoundaryIngressGeneratedAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacitySettlementInitialGenerated oldVisit sourceIndex
    (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex)

/-- Compiler-selected identity evolution of the inherited contribution row at
the settlement ingress. -/
def contributionCapacitySettlementBoundaryIngressEvolutionAt
    (oldVisit : OldVisit) :
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit) :=
  .carried rfl HEq.rfl

def contributionCapacitySettlementBoundaryIngressLineageAt
    (oldVisit : OldVisit) :
    RootDebtLineageAt (ReopeningNAt oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit) :=
  (contributionCapacitySettlementBoundaryIngressEvolutionAt oldVisit
    ).toDebtLineage

/-- The actual target root disposition, not a numerical readout, selects the
same carried row evolution. -/
theorem contributionCapacitySettlementBoundaryIngressDisposition_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementBoundaryIngressGeneratedAt oldVisit
      sourceIndex).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementBoundaryContributionAt oldVisit) =
      .evolved
        (contributionCapacitySettlementBoundaryIngressEvolutionAt oldVisit) :=
  rfl

/-- Canonical compiler origin of the ingress target. -/
def contributionCapacitySettlementBoundaryIngressOldOriginAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ExactTargetDebtOriginAt
      (contributionCapacitySettlementFullLedger oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit) :=
  (contributionCapacitySettlementWriteEvolution oldVisit sourceIndex
    (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex)
    (contributionCapacitySettlementEmitted oldVisit sourceIndex
      (ContributionCapacitySettlementPaidSourceEventAt oldVisit sourceIndex)
      false)).targetOldOrigin
        (contributionCapacitySettlementBoundaryContributionAt oldVisit)

@[simp] theorem
    contributionCapacitySettlementBoundaryIngressOldOrigin_source_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
      sourceIndex).1 =
      contributionCapacitySettlementBoundaryContributionAt oldVisit :=
  rfl

/-- The ordinary ingress cannot relabel this exact old row as a fresh birth. -/
theorem contributionCapacitySettlementBoundaryIngressFresh_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (RootDebtFreshAt (ReopeningNAt oldVisit)
        (contributionCapacitySettlementFullLedger oldVisit).support
        (contributionCapacitySettlementBoundaryContributionAt oldVisit)) :=
  ⟨fun fresh => PEmpty.elim
    ((contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
      sourceIndex).excludesFresh fresh)⟩

/-- The d8 carrier stores the existing actual-service Payment and its exact
action receipt, while the target ingress authority remains a separately typed
settlement native write. -/
structure SourceGeneratedContributionCapacitySettlementBoundaryAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 19 where
  private mk ::
  sourcePayment :
    CanonicalContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex
  sourcePaymentExact : sourcePayment =
    sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex
  ingressReceipt :
    (generatedContributionCapacitySettlementPaidActionAt oldVisit sourceIndex
      ).target.Receipt
      (generatedContributionCapacitySettlementPaidActionAt oldVisit sourceIndex
        ).answer
  ingressReceiptExact : ingressReceipt = sourcePayment.actionReceipt
  targetIngressWrite : (SettlementVAt oldVisit).NativeWriteAt false
  targetIngressWriteExact : targetIngressWrite = .ingress
  targetContributionDispositionExact :
    (contributionCapacitySettlementBoundaryIngressGeneratedAt oldVisit
      sourceIndex).wholeLedgerWriteBack.entryDisposition
        (contributionCapacitySettlementBoundaryContributionAt oldVisit) =
      .evolved
        (contributionCapacitySettlementBoundaryIngressEvolutionAt oldVisit)

def sourceGeneratedContributionCapacitySettlementBoundaryAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacitySettlementBoundaryAt oldVisit
      sourceIndex where
  sourcePayment :=
    sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex
  sourcePaymentExact := rfl
  ingressReceipt :=
    (sourceGeneratedContributionCapacitySettlementCrossRootPaymentAt oldVisit
      sourceIndex).actionReceipt
  ingressReceiptExact := rfl
  targetIngressWrite := .ingress
  targetIngressWriteExact := rfl
  targetContributionDispositionExact :=
    contributionCapacitySettlementBoundaryIngressDisposition_exact oldVisit
      sourceIndex

/-- Hypothetical strict renewal at the target ingress.  All real ingredients
are fixed by the boundary carrier and the compiler-selected old row; only the
strict `0 < 0` debit is impossible. -/
structure ExactContributionCapacitySettlementIngressStrictRenewalAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 20 where
  private mk ::
  boundary : SourceGeneratedContributionCapacitySettlementBoundaryAt oldVisit
    sourceIndex
  boundaryExact : boundary =
    sourceGeneratedContributionCapacitySettlementBoundaryAt oldVisit
      sourceIndex
  oldOrigin : ExactTargetDebtOriginAt
    (contributionCapacitySettlementFullLedger oldVisit)
    (contributionCapacitySettlementBoundaryContributionAt oldVisit)
  oldOriginExact : oldOrigin =
    contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
      sourceIndex
  sameDebt : RootDebtLineageAt (ReopeningNAt oldVisit)
    (contributionCapacitySettlementBoundaryContributionAt oldVisit)
    (contributionCapacitySettlementBoundaryContributionAt oldVisit)
  sameDebtExact : sameDebt =
    contributionCapacitySettlementBoundaryIngressLineageAt oldVisit
  strictDebit :
    (contributionCapacitySettlementBoundaryContributionAt oldVisit
      ).progressBudget <
      (contributionCapacitySettlementBoundaryContributionAt oldVisit
        ).progressBudget

theorem exactContributionCapacitySettlementIngressStrictRenewal_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (ExactContributionCapacitySettlementIngressStrictRenewalAt oldVisit
        sourceIndex) := by
  constructor
  intro renewal
  have zero :=
    contributionCapacitySettlementBoundaryContribution_budget_zero oldVisit
  have strict := renewal.strictDebit
  rw [zero] at strict
  exact Nat.not_lt_zero _ strict

/-! ## Depth-nine faithful terminal and same-debt handoff -/

/-- At terminal current `true` the settlement vocabulary has no native write
at all, hence no actual-service Payment edge. -/
theorem contributionCapacitySettlementTerminalNativeWrite_isEmpty
    (oldVisit : OldVisit) :
    IsEmpty ((SettlementVAt oldVisit).NativeWriteAt true) :=
  ⟨fun write => nomatch write⟩

theorem contributionCapacitySettlementTerminalFaithful_inhabited
    (oldVisit : OldVisit) :
    Nonempty ((SettlementVAt oldVisit).FaithfulTerminalAt true) :=
  ⟨.settled⟩

theorem contributionCapacitySettlementBoundaryTerminalEveryRow_terminal
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (entry : (contributionCapacitySettlementFullLedger oldVisit).Entry) :
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition entry =
      .terminal
        ((contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution.discharge entry) :=
  contributionCapacitySettlementTerminalEveryRow_terminal oldVisit
    sourceIndex entry

theorem contributionCapacitySettlementBoundaryTerminal_noLocalSuccessor
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (SourceNativeLedgerGeneratedSuccessorAt
        (contributionCapacitySettlementTerminalRootEventAt oldVisit
          sourceIndex).occurrence
        (contributionCapacitySettlementTerminalRootEventAt oldVisit
          sourceIndex).wholeLedgerWriteBack) :=
  (sourceGeneratedContributionCapacitySettlementTerminalNoFreeReceiptAt
    oldVisit sourceIndex).noLocalLedgerSuccessor

/-- Existing terminal-handoff origin of the survivor contribution. -/
def contributionCapacitySettlementBoundarySurvivorOriginAt
    (oldVisit : OldVisit) :=
  contributionCapacitySettlementSurvivorDebtOrigin oldVisit
    (contributionCapacitySettlementSurvivorContribution oldVisit)

@[simp] theorem contributionCapacitySettlementBoundarySurvivorOrigin_source_exact
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementBoundarySurvivorOriginAt oldVisit).1 =
      contributionCapacitySettlementBoundaryContributionAt oldVisit :=
  rfl

/-- d9 hands the exact same contribution debt to the survivor old face. -/
def contributionCapacitySettlementBoundaryTerminalHandoffLineageAt
    (oldVisit : OldVisit) :
    RootDebtLineageAt (ReopeningNAt oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit)
      (contributionCapacitySettlementSurvivorContribution oldVisit) :=
  (contributionCapacitySettlementBoundarySurvivorOriginAt oldVisit).2

/-- Composition from the ingress compiler origin through the d9 survivor
handoff.  The terminal does not delete or recreate the debt identity. -/
def contributionCapacitySettlementBoundaryIngressToSurvivorLineageAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    RootDebtLineageAt (ReopeningNAt oldVisit)
      (contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
        sourceIndex).1
      (contributionCapacitySettlementSurvivorContribution oldVisit) :=
  { lineage_eq :=
      (contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
        sourceIndex).2.lineage_eq.trans
        (contributionCapacitySettlementBoundaryTerminalHandoffLineageAt
          oldVisit).lineage_eq
    claim_eq :=
      (contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
        sourceIndex).2.claim_eq.trans
        (contributionCapacitySettlementBoundaryTerminalHandoffLineageAt
          oldVisit).claim_eq }

/-- The d9 contribution debt as a current of the already registered
settlement-to-survivor process. -/
def contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootDebtCurrentAt
      (settlementDebtProcessAt oldVisit sourceIndex)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit) where
  state := none
  entry := contributionCapacitySettlementBoundaryContributionAt oldVisit
  sameDebt := ⟨rfl, rfl⟩

/-- The exact generated successor still contains the same contribution debt
on the d10 survivor face. -/
def contributionCapacitySettlementBoundarySurvivorContributionTargetAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeRootDebtTargetAt
      (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
        oldVisit sourceIndex) :=
  ⟨contributionCapacitySettlementSurvivorContribution oldVisit,
    contributionCapacitySettlementBoundaryTerminalHandoffLineageAt oldVisit⟩

/-- d9 is locally terminal but cannot be final settlement of the inherited
contribution, because its generated d10 successor contains the same debt. -/
theorem contributionCapacitySettlementBoundaryTerminalContributionSettlement_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (SourceNativeRootDebtSettlementAt
        (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
          oldVisit sourceIndex)) :=
  ⟨fun settlement => settlement.noSameDebtAtTarget.false
    (contributionCapacitySettlementBoundarySurvivorContributionTargetAt
      oldVisit sourceIndex)⟩

/-- A terminal arithmetic edge would first require a terminal-current native
write.  That fibre is empty before any debit field can be supplied. -/
abbrev ContributionCapacitySettlementTerminalArithmeticEdgeAt
    (oldVisit : OldVisit) :=
  (SettlementVAt oldVisit).NativeWriteAt true

theorem contributionCapacitySettlementTerminalArithmeticEdge_isEmpty
    (oldVisit : OldVisit) :
    IsEmpty (ContributionCapacitySettlementTerminalArithmeticEdgeAt oldVisit) :=
  contributionCapacitySettlementTerminalNativeWrite_isEmpty oldVisit

structure ProofCarryingContributionCapacitySettlementBoundaryDeathAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  boundaryGenerated : Nonempty
    (SourceGeneratedContributionCapacitySettlementBoundaryAt oldVisit
      sourceIndex)
  inheritedOriginGenerated : Nonempty
    (ContributionCapacitySettlementBoundaryInheritedOriginAt oldVisit)
  ingressOldOriginGenerated : Nonempty
    (ExactTargetDebtOriginAt
      (contributionCapacitySettlementFullLedger oldVisit)
      (contributionCapacitySettlementBoundaryContributionAt oldVisit))
  ingressContributionBudgetZero :
    (contributionCapacitySettlementBoundaryContributionAt oldVisit
      ).progressBudget = 0
  ingressStrictRenewalEmpty : IsEmpty
    (ExactContributionCapacitySettlementIngressStrictRenewalAt oldVisit
      sourceIndex)
  terminalNativeWriteEmpty : IsEmpty
    ((SettlementVAt oldVisit).NativeWriteAt true)
  terminalFaithfulInhabited : Nonempty
    ((SettlementVAt oldVisit).FaithfulTerminalAt true)
  terminalEveryRow : ∀
      entry : (contributionCapacitySettlementFullLedger oldVisit).Entry,
    (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
      ).wholeLedgerWriteBack.entryDisposition entry =
      .terminal
        ((contributionCapacitySettlementTerminalExactAt oldVisit sourceIndex
          ).ledgerEvolution.discharge entry)
  terminalNoLocalSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
        ).occurrence
      (contributionCapacitySettlementTerminalRootEventAt oldVisit sourceIndex
        ).wholeLedgerWriteBack)
  terminalArithmeticEdgeEmpty : IsEmpty
    (ContributionCapacitySettlementTerminalArithmeticEdgeAt oldVisit)
  handoffContinuesIngressDebt : Nonempty
    (RootDebtLineageAt (ReopeningNAt oldVisit)
      (contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
        sourceIndex).1
      (contributionCapacitySettlementSurvivorContribution oldVisit))
  inheritedContributionFinalSettlementEmpty : IsEmpty
    (SourceNativeRootDebtSettlementAt
      (contributionCapacitySettlementBoundaryTerminalContributionCurrentAt
        oldVisit sourceIndex))

theorem proofCarryingContributionCapacitySettlementBoundaryDeathAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacitySettlementBoundaryDeathAt oldVisit
      sourceIndex where
  boundaryGenerated :=
    ⟨sourceGeneratedContributionCapacitySettlementBoundaryAt oldVisit
      sourceIndex⟩
  inheritedOriginGenerated :=
    ⟨contributionCapacitySettlementBoundaryInheritedOriginAt oldVisit⟩
  ingressOldOriginGenerated :=
    ⟨contributionCapacitySettlementBoundaryIngressOldOriginAt oldVisit
      sourceIndex⟩
  ingressContributionBudgetZero :=
    contributionCapacitySettlementBoundaryContribution_budget_zero oldVisit
  ingressStrictRenewalEmpty :=
    exactContributionCapacitySettlementIngressStrictRenewal_isEmpty oldVisit
      sourceIndex
  terminalNativeWriteEmpty :=
    contributionCapacitySettlementTerminalNativeWrite_isEmpty oldVisit
  terminalFaithfulInhabited :=
    contributionCapacitySettlementTerminalFaithful_inhabited oldVisit
  terminalEveryRow :=
    contributionCapacitySettlementBoundaryTerminalEveryRow_terminal oldVisit
      sourceIndex
  terminalNoLocalSuccessor :=
    contributionCapacitySettlementBoundaryTerminal_noLocalSuccessor oldVisit
      sourceIndex
  terminalArithmeticEdgeEmpty :=
    contributionCapacitySettlementTerminalArithmeticEdge_isEmpty oldVisit
  handoffContinuesIngressDebt :=
    ⟨contributionCapacitySettlementBoundaryIngressToSurvivorLineageAt
      oldVisit sourceIndex⟩
  inheritedContributionFinalSettlementEmpty :=
    contributionCapacitySettlementBoundaryTerminalContributionSettlement_isEmpty
      oldVisit sourceIndex

/-! ## Canonical d8/d9 runtime seal -/

structure ProofCarryingCanonicalContributionCapacitySettlementBoundaryDeath :
    Prop where
  boundary : ProofCarryingContributionCapacitySettlementBoundaryDeathAt
    canonicalOldVisit 1
  depthEightPaidSourceExact :
    ninthTick.receipt.1 =
      ContributionCapacitySettlementPaidSourceEventAt canonicalOldVisit 1
  depthEightIngressReceiptExact :
    ninthTick.receipt.2 =
      (generatedContributionCapacitySettlementPaidActionAt canonicalOldVisit
        1).receipt
  depthNineTerminalRootEventExact :
    tenthTick.receipt.1 =
      contributionCapacitySettlementTerminalRootEventAt canonicalOldVisit 1
  depthNineFaithfulTerminalExact :
    tenthTickExactFaithfulTerminal =
      contributionCapacitySettlementTerminalExactAt canonicalOldVisit 1
  depthNineHandoffExact :
    tenthTick.receipt.2.2.nextCurrent =
      contributionCapacitySettlementTerminalNextPaidBy canonicalOldVisit 1

theorem proofCarryingCanonicalContributionCapacitySettlementBoundaryDeath :
    ProofCarryingCanonicalContributionCapacitySettlementBoundaryDeath where
  boundary :=
    proofCarryingContributionCapacitySettlementBoundaryDeathAt
      canonicalOldVisit 1
  depthEightPaidSourceExact := depthEight_paidSourceEvent_exact
  depthEightIngressReceiptExact := depthEight_actionReceipt_exact
  depthNineTerminalRootEventExact := depthNine_terminalRootEvent_exact
  depthNineFaithfulTerminalExact := depthNine_exactFaithfulTerminal
  depthNineHandoffExact := depthNine_macroLanding_is_handoffGenerated

/-! ## Negative controls -/

set_option linter.unusedVariables false in
theorem settlementBoundaryDeath_hasNoSecondPaymentOrCallerHistory
    (oldVisit : OldVisit) (sourceIndex : Nat) : True := by
  let boundary :=
    sourceGeneratedContributionCapacitySettlementBoundaryAt oldVisit
      sourceIndex
  fail_if_success
    exact (boundary.targetIngressWrite :
      CanonicalContributionCapacitySettlementCrossRootPaymentAt oldVisit
        sourceIndex)
  fail_if_success
    exact (boundary.ingressReceipt :
      CanonicalContributionCapacitySettlementCrossRootPaymentAt oldVisit
        sourceIndex)
  fail_if_success exact boundary.secondPayment
  fail_if_success exact boundary.history
  fail_if_success exact boundary.date
  fail_if_success exact boundary.registry
  fail_if_success exact boundary.future
  fail_if_success exact boundary.completedFuture
  trivial

end
end M14SourceGeneratedContributionCapacitySettlementBoundaryDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementBoundaryDeath.sourceGeneratedContributionCapacitySettlementBoundaryAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementBoundaryDeath.exactContributionCapacitySettlementIngressStrictRenewal_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementBoundaryDeath.contributionCapacitySettlementTerminalArithmeticEdge_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementBoundaryDeath.contributionCapacitySettlementBoundaryTerminalContributionSettlement_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementBoundaryDeath.proofCarryingCanonicalContributionCapacitySettlementBoundaryDeath
