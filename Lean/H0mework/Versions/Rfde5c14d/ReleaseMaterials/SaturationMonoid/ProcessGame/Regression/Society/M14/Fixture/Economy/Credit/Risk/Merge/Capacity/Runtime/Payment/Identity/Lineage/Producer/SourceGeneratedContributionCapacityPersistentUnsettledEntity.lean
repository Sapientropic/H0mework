import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Payment.Action.Cut.Consumer.ProofCarryingContributionCapacityCutCrossRootPayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Runtime.Payment.Producer.SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.NoGo.SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity

/-!
# Persistent unsettled contribution entity

The capacity-cut Payment first pays the inherited contribution row by the
exact complete-ledger debit `1 -> 0`.  The settlement-survivor process then
retains that source-generated debt identity at every actual current.  Each
current emits its own actual-service Payment and whole-ledger evolution, but
the tracked entity row is carried `0 -> 0` and remains locally unterminated.

The carrier below is a zero-field restriction of those existing currents.
Its entity identity is the composed `RootDebtLineageAt` already stored in the
registered debt current; neither the temporal index, a database label, nor a
visible budget readout defines the entity.  No occurrence, ledger, payment
registry, history table, or completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPersistentUnsettledEntity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityCutCrossRootPayment
open M14ProofCarryingContributionCapacityCutCrossRootPayment
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementConsumer
open M14SourceGeneratedContributionCapacitySettlementSurvivorNoFreeEternity
open M14SourceGeneratedContributionCapacitySettlementSurvivorRuntimePayment

/-- The exact inherited contribution row of the existing survivor ledger. -/
def persistentContributionEntityEntry :=
  contributionCapacitySettlementSurvivorContribution
    canonicalSettlementOldVisit

/-- Its origin is selected by the existing terminal-to-survivor handoff. -/
abbrev PersistentContributionEntityOrigin :=
  contributionCapacitySettlementSurvivorDebtOriginAt
    canonicalSettlementOldVisit persistentContributionEntityEntry

/-- Registered current of the same source debt at one actual survivor index. -/
def persistentContributionEntityCurrentAt (index : Nat) :
    SourceNativeRootDebtCurrentAt
      (settlementDebtProcessAt canonicalSettlementOldVisit 1)
      PersistentContributionEntityOrigin :=
  contributionCapacitySettlementSurvivorDebtCurrentAt
    canonicalSettlementOldVisit 1 index persistentContributionEntityEntry

/-- Zero-field source token.  The index selects an already generated current;
it supplies no entity key, row, lineage, Payment, debit, target, or future. -/
inductive SourceGeneratedPersistentUnsettledContributionEntityAt
    (index : Nat) : Type 22
  | private generated

def sourceGeneratedPersistentUnsettledContributionEntityAt
    (index : Nat) :
    SourceGeneratedPersistentUnsettledContributionEntityAt index :=
  .generated

namespace SourceGeneratedPersistentUnsettledContributionEntityAt

variable {index : Nat}
  (entity : SourceGeneratedPersistentUnsettledContributionEntityAt index)

theorem eq_generated :
    entity = sourceGeneratedPersistentUnsettledContributionEntityAt index := by
  cases entity
  rfl

def current :
    SourceNativeRootDebtCurrentAt
      (settlementDebtProcessAt canonicalSettlementOldVisit 1)
      PersistentContributionEntityOrigin := by
  cases entity
  exact persistentContributionEntityCurrentAt index

/-- Entity identity is the existing source-to-current debt-lineage fold. -/
def lineageFold :
    RootDebtLineageAt
      (M14SourceGeneratedContributionCapacityReopeningWorld.ReopeningNAt
        canonicalSettlementOldVisit)
      PersistentContributionEntityOrigin (current entity).entry :=
  (current entity).sameDebt

def rootEvent := by
  cases entity
  exact contributionCapacitySettlementSurvivorRuntimePaymentRootEventAt index

def paymentWitness := by
  cases entity
  exact contributionCapacitySettlementSurvivorRuntimePaymentAt index

theorem runtimePaymentGenerated :
    SourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt
      index :=
  sourceGeneratedContributionCapacitySettlementSurvivorRuntimePaymentAt index

@[simp] theorem current_entry_exact :
    (current entity).entry = persistentContributionEntityEntry := by
  cases entity
  rfl

@[simp] theorem current_budget_zero : (current entity).budget = 0 := by
  cases entity
  exact contributionCapacitySettlementSurvivorDebtCurrent_budget_zero
    canonicalSettlementOldVisit 1 index persistentContributionEntityEntry

theorem lineageFold_isSourceGenerated :
    lineageFold entity =
      (contributionCapacitySettlementSurvivorDebtOrigin
        canonicalSettlementOldVisit persistentContributionEntityEntry).2 := by
  cases entity
  rfl

/-- The exact Payment-bearing root event evolves the tracked row.  It does
not terminally settle it and cannot be replaced by the bare Payment witness. -/
theorem paymentWholeLedgerDisposition_exact :
    (rootEvent entity).wholeLedgerWriteBack.entryDisposition
        persistentContributionEntityEntry =
      LedgerEntryDispositionAt.evolved
        (contributionCapacitySettlementSurvivorRuntimePaymentRowEvolutionAt
          index 0) := by
  cases entity
  exact
    contributionCapacitySettlementSurvivorRuntimePayment_everyRow_evolved
      index 0

theorem localTerminalEmpty :
    IsEmpty (SourceNativeRootDebtLocalTerminalAt (current entity)) := by
  cases entity
  exact contributionCapacitySettlementSurvivorDebtCurrent_noLocalTerminal
    canonicalSettlementOldVisit 1 index persistentContributionEntityEntry

theorem paidMacroEmpty :
    IsEmpty
      (SourceNativePaidRootDebtMacroContinuationAt (current entity)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero (current entity)
    (current_budget_zero entity)

end SourceGeneratedPersistentUnsettledContributionEntityAt

/-- Every actual survivor current regenerates the same lineage-fixed entity,
its own exact Payment witness, and its complete row disposition. -/
theorem everyCurrent_generatesPersistentUnsettledContributionEntity :
    ∀ index : Nat,
      Nonempty (SourceGeneratedPersistentUnsettledContributionEntityAt index) :=
  fun index =>
    ⟨sourceGeneratedPersistentUnsettledContributionEntityAt index⟩

/-- The first structural debit is an existing Payment mouth, not a numeric
potential supplied to this producer. -/
theorem initialContributionEntityDebit_isExactPayment :
    let payment := canonicalContributionCapacityCutCrossRootPayment
    payment.targetEvent.wholeLedgerWriteBack.entryDisposition
        (initialContribution
          (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)) =
      .evolved payment.actionReceipt.strictDebit ∧
      (initialContribution
        (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
        ).progressBudget = 1 ∧
      (contributionCapacityCutTargetContribution
        (capacityActionRootedAt CanonicalContributionCapacityCutOldVisit)
        ).progressBudget = 0 :=
  ⟨canonicalContributionCapacityCutCrossRootPayment.strictDebitDispositionExact,
    canonicalContributionCapacityCutCrossRootPayment.actionReceipt.sourceBudgetOne,
    canonicalContributionCapacityCutCrossRootPayment.actionReceipt.targetBudgetZero⟩

theorem persistentEntity_hasNoCallerIdentityPaymentOrFuture
    (index : Nat) : True := by
  let entity :=
    sourceGeneratedPersistentUnsettledContributionEntityAt index
  fail_if_success exact entity.entityKey
  fail_if_success exact entity.databaseLabel
  fail_if_success exact entity.row
  fail_if_success exact entity.lineage
  fail_if_success exact entity.payment
  fail_if_success exact entity.debit
  fail_if_success exact entity.target
  fail_if_success exact entity.history
  fail_if_success exact entity.future
  fail_if_success exact entity.registry
  trivial

end
end M14SourceGeneratedContributionCapacityPersistentUnsettledEntity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPersistentUnsettledEntity.sourceGeneratedPersistentUnsettledContributionEntityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPersistentUnsettledEntity.SourceGeneratedPersistentUnsettledContributionEntityAt.paymentWholeLedgerDisposition_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPersistentUnsettledEntity.initialContributionEntityDebit_isExactPayment
