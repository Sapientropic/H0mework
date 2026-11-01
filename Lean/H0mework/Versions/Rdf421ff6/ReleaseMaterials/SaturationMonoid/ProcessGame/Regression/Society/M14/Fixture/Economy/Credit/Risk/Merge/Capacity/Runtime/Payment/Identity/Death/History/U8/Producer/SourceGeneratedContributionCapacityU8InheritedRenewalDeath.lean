import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Consumer.ProofCarryingContributionCapacityTargetOriginOrBirth
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Payment.Revision.Consumer.ProofCarryingContributionCapacityU8RevisionNoFreeReceipt

/-!
# U8 inherited-contribution renewal death

The capacity-cut target contribution enters the self-U8 world through the
existing exact old-origin presentation.  It is not the fresh U8 residual.
Every U8 occurrence generates a real whole-ledger Payment, but the inherited
contribution row is compiler-carried from budget zero to budget zero.

An exact renewal Payment for that row must therefore contain the same event's
compiler-selected evolution and a strict debit.  Its fibre is empty at every
U8 current.  No debt process, history table, stage registry or caller target
is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8RuntimePayment
open M14SourceGeneratedContributionCapacityNoFreeRestoration
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth
open M14ProofCarryingContributionCapacityTargetOriginOrBirth
open M14SourceGeneratedContributionCapacityU8RevisionNoFreeReceipt
open M14ProofCarryingContributionCapacityU8RevisionNoFreeReceipt

def contributionCapacityU8InheritedTargetAt
    (oldVisit : OldVisit) (index : Nat) :
    (contributionCapacityU8Ledger oldVisit).Entry :=
  ((contributionCapacityU8Evolution oldVisit
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).occurrence).destination
        (contributionCapacityU8InheritedContribution oldVisit)).1

def contributionCapacityU8InheritedEvolutionAt
    (oldVisit : OldVisit) (index : Nat) :
    LedgerEntryEvolutionAt (CapacityU8NAt oldVisit)
      (contributionCapacityU8InheritedContribution oldVisit)
      (contributionCapacityU8InheritedTargetAt oldVisit index) :=
  ((contributionCapacityU8Evolution oldVisit
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).occurrence).destination
        (contributionCapacityU8InheritedContribution oldVisit)).2

@[simp] theorem contributionCapacityU8InheritedTarget_eq_source
    (oldVisit : OldVisit) (index : Nat) :
    contributionCapacityU8InheritedTargetAt oldVisit index =
      contributionCapacityU8InheritedContribution oldVisit :=
  contributionCapacityU8Evolution_destination oldVisit
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index).occurrence
    (contributionCapacityU8InheritedContribution oldVisit)

def contributionCapacityU8InheritedDebtLineageAt
    (oldVisit : OldVisit) (index : Nat) :
    RootDebtLineageAt (CapacityU8NAt oldVisit)
      (contributionCapacityU8InheritedContribution oldVisit)
      (contributionCapacityU8InheritedTargetAt oldVisit index) :=
  (contributionCapacityU8InheritedEvolutionAt oldVisit index).toDebtLineage

/-- Private exact strict-renewal fibre.  The target row and debt lineage are
read from the canonical whole-ledger evolution, never supplied. -/
structure ExactContributionCapacityU8InheritedRenewalPaymentAt
    (oldVisit : OldVisit) (index : Nat) : Type 23 where
  private mk ::
  actualPayment :
    SourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit index
  oldOrigin : ExactTargetDebtOriginAt
    (contributionCapacityU8PreRevisionLedger oldVisit)
    (contributionCapacityU8InheritedContribution oldVisit)
  oldOriginExact : oldOrigin =
    contributionCapacityU8InheritedContributionOrigin oldVisit
  dispositionExact :
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityU8InheritedContribution oldVisit) =
      .evolved (contributionCapacityU8InheritedEvolutionAt oldVisit index)
  sameDebt : RootDebtLineageAt (CapacityU8NAt oldVisit)
    (contributionCapacityU8InheritedContribution oldVisit)
    (contributionCapacityU8InheritedTargetAt oldVisit index)
  sameDebtExact : sameDebt =
    contributionCapacityU8InheritedDebtLineageAt oldVisit index
  strictDebit :
    (contributionCapacityU8InheritedTargetAt oldVisit index).progressBudget <
      (contributionCapacityU8InheritedContribution oldVisit).progressBudget

theorem exactContributionCapacityU8InheritedRenewalPayment_isEmpty
    (oldVisit : OldVisit) (index : Nat) :
    IsEmpty
      (ExactContributionCapacityU8InheritedRenewalPaymentAt oldVisit index) := by
  constructor
  intro payment
  have sourceZero :
      (contributionCapacityU8InheritedContribution oldVisit).progressBudget =
        0 :=
    contributionCapacityU8Entry_budget_zero oldVisit
      (contributionCapacityU8InheritedContribution oldVisit)
  have targetZero :
      (contributionCapacityU8InheritedTargetAt oldVisit index).progressBudget =
        0 := by
    rw [contributionCapacityU8InheritedTarget_eq_source]
    exact sourceZero
  have strictDebit := payment.strictDebit
  rw [sourceZero, targetZero] at strictDebit
  exact Nat.not_lt_zero _ strictDebit

theorem contributionCapacityU8InheritedDisposition_exact
    (oldVisit : OldVisit) (index : Nat) :
    (contributionCapacityU8RuntimePaymentRootEventAt oldVisit index
      ).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityU8InheritedContribution oldVisit) =
      .evolved (contributionCapacityU8InheritedEvolutionAt oldVisit index) := by
  exact contributionCapacityU8RuntimePayment_everyRow_evolved oldVisit index 0

theorem contributionCapacityU8InheritedOrigin_isCutTarget
    (oldVisit : OldVisit) :
    (contributionCapacityU8InheritedContributionOrigin oldVisit).1 =
      contributionCapacityU8EmbeddedOldEntry oldVisit
        (contributionCapacityCutTargetContribution
          (capacityActionRootedAt oldVisit)) :=
  rfl

theorem contributionCapacityU8InheritedOrigin_notFresh
    (oldVisit : OldVisit) :
    IsEmpty
      (RootDebtFreshAt (CapacityU8NAt oldVisit)
        (contributionCapacityU8PreRevisionLedger oldVisit).support
        (contributionCapacityU8InheritedContribution oldVisit)) := by
  constructor
  intro fresh
  exact PEmpty.elim
    ((contributionCapacityU8InheritedContributionOrigin oldVisit).excludesFresh
      fresh)

/-- The revision receipt, rather than a numeric depth, fixes the first U8
Payment occurrence. -/
theorem contributionCapacityU8Revision_firstWritePayment_exact
    (oldVisit : OldVisit) :
    (sourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt oldVisit
      ).firstWritePayment =
      sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit 0 :=
  rfl

theorem contributionCapacityU8Revision_firstWriteOccurrence_exact
    (oldVisit : OldVisit) :
    (ContributionCapacityU8CanonicalRevisionAt oldVisit
      ).generate.initialRestructuringGenerated.occurrence =
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0).occurrence :=
  (sourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt oldVisit
    ).initialOccurrenceExact

theorem contributionCapacityU8Revision_firstWriteWholeLedger_exact
    (oldVisit : OldVisit) :
    (ContributionCapacityU8CanonicalRevisionAt oldVisit
      ).generate.initialRestructuringGenerated.wholeLedgerWriteBack =
      (contributionCapacityU8RuntimePaymentRootEventAt oldVisit 0
        ).wholeLedgerWriteBack :=
  (sourceGeneratedContributionCapacityU8RevisionNoFreeReceiptAt oldVisit
    ).initialWholeLedgerWriteExact

theorem u8InheritedRenewalDeath_hasNoCallerTargetHistoryOrDate
    (oldVisit : OldVisit) (index : Nat) : True := by
  let payment :=
    sourceGeneratedContributionCapacityU8RuntimePaymentAt oldVisit index
  fail_if_success exact
    (payment : ExactContributionCapacityU8InheritedRenewalPaymentAt oldVisit
      index)
  fail_if_success exact payment.target
  fail_if_success exact payment.history
  fail_if_success exact payment.date
  fail_if_success exact payment.future
  trivial

end
end M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath.exactContributionCapacityU8InheritedRenewalPayment_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath.contributionCapacityU8InheritedOrigin_notFresh
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8InheritedRenewalDeath.contributionCapacityU8Revision_firstWriteOccurrence_exact
