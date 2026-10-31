import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Action.Reopening.Producer.SourceGeneratedContributionCapacityReopeningActionPayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Payment.Producer.SourceGeneratedContributionCapacityReopeningRuntimePayment
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Gate.Birth.Producer.SourceGeneratedContributionCapacityTargetOriginOrBirth

/-!
# Arithmetic death of contribution renewal on the reopening root

The inherited contribution is the exact old-origin row installed from the
capacity-U8 coface, not the generated residual birth.  The reopening action
Payment and every positive-current runtime Payment each select that row's
compiler evolution.  Both evolutions preserve its already exhausted budget,
so the corresponding exact strict-debit renewal fibres are empty.

This file introduces no process, history, root, ledger, registry or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityReopeningRenewalDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityNoFreeRestoration
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningCompiler
open M14SourceGeneratedContributionCapacityReopeningActionPayment
open M14SourceGeneratedContributionCapacityReopeningRuntimePayment
open M14SourceGeneratedContributionCapacityTargetOriginOrBirth

/-! ## Exact inherited origin and compiler-selected contribution row -/

abbrev ContributionCapacityReopeningU8ContributionOriginAt
    (oldVisit : OldVisit) :=
  ExactTargetDebtOriginAt
    (contributionCapacityU8PreRevisionLedger oldVisit)
    (contributionCapacityU8InheritedContribution oldVisit)

/-- Existing old origin of the inherited contribution.  In particular this
is not the independently generated residual birth. -/
def contributionCapacityReopeningU8ContributionOriginAt
    (oldVisit : OldVisit) :
    ContributionCapacityReopeningU8ContributionOriginAt oldVisit :=
  contributionCapacityU8InheritedContributionOrigin oldVisit

/-- Row zero is the inherited contribution at every reopening current. -/
def contributionCapacityReopeningContributionEntryAt
    (oldVisit : OldVisit) (current : Nat) :=
  contributionCapacityReopeningCurrentEntryAt oldVisit current (0 : Fin 3)

@[simp] theorem contributionCapacityReopeningInitialContribution_content_exact
    (oldVisit : OldVisit) :
    (contributionCapacityReopeningContributionEntryAt oldVisit 0).1 =
      (contributionCapacityU8InheritedContribution oldVisit).1 :=
  rfl

@[simp] theorem contributionCapacityReopeningInitialContribution_claim_exact
    (oldVisit : OldVisit) :
    (contributionCapacityReopeningContributionEntryAt oldVisit 0).claim =
      (contributionCapacityU8InheritedContribution oldVisit).claim :=
  rfl

@[simp] theorem contributionCapacityReopeningInitialContribution_lineage_exact
    (oldVisit : OldVisit) :
    (ReopeningNAt oldVisit).lineageAt
        (contributionCapacityReopeningLedgerAtCurrent oldVisit 0).support =
      (CapacityU8NAt oldVisit).lineageAt
        (contributionCapacityU8Ledger oldVisit).support :=
  rfl

@[simp] theorem contributionCapacityReopeningContribution_budget_zero
    (oldVisit : OldVisit) (current : Nat) :
    (contributionCapacityReopeningContributionEntryAt oldVisit current
      ).progressBudget = 0 := by
  cases current with
  | zero =>
      exact contributionCapacityU8Entry_budget_zero oldVisit
        (contributionCapacityU8InheritedContribution oldVisit)
  | succ current =>
      exact contributionCapacityReopeningTargetEntry_budget_zero oldVisit
        (contributionCapacityReopeningContributionEntryAt oldVisit
          (current + 1))

/-- The action target's row-zero evolution, fixed by its current-zero
compiler image. -/
def contributionCapacityReopeningActionContributionEvolutionAt
    (oldVisit : OldVisit) :
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningContributionEntryAt oldVisit 0)
      (contributionCapacityReopeningContributionEntryAt oldVisit 1) :=
  contributionCapacityReopeningRowEvolution oldVisit 0 (0 : Fin 3)

def contributionCapacityReopeningActionContributionLineageAt
    (oldVisit : OldVisit) :
    RootDebtLineageAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningContributionEntryAt oldVisit 0)
      (contributionCapacityReopeningContributionEntryAt oldVisit 1) :=
  (contributionCapacityReopeningActionContributionEvolutionAt oldVisit
    ).toDebtLineage

theorem contributionCapacityReopeningActionContributionCompilerEvolution_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) : HEq
    (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
      sourceIndex (0 : Fin 3))
    (contributionCapacityReopeningActionContributionEvolutionAt oldVisit) :=
  HEq.rfl

theorem contributionCapacityReopeningActionContributionDisposition_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    let payment :=
      sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex
    payment.targetEvent.wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningContributionEntryAt oldVisit 0) =
      .evolved
        (contributionCapacityReopeningActionContributionEvolutionAt oldVisit) :=
  (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
    sourceIndex).everyTargetRowEvolved (0 : Fin 3)

/-- The exact row-zero evolution at one positive-current runtime Payment. -/
def contributionCapacityReopeningRuntimeContributionEvolutionAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    LedgerEntryEvolutionAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningContributionEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index))
      (contributionCapacityReopeningContributionEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index + 1)) :=
  contributionCapacityReopeningRowEvolution oldVisit
    (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit sourceIndex
      index) (0 : Fin 3)

def contributionCapacityReopeningRuntimeContributionLineageAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    RootDebtLineageAt (ReopeningNAt oldVisit)
      (contributionCapacityReopeningContributionEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index))
      (contributionCapacityReopeningContributionEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index + 1)) :=
  (contributionCapacityReopeningRuntimeContributionEvolutionAt oldVisit
    sourceIndex index).toDebtLineage

theorem contributionCapacityReopeningRuntimeContributionCompilerEvolution_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) : HEq
    (contributionCapacityReopeningRuntimePaymentRowEvolutionAt oldVisit
      sourceIndex index (0 : Fin 3))
    (contributionCapacityReopeningRuntimeContributionEvolutionAt oldVisit
      sourceIndex index) :=
  HEq.rfl

theorem contributionCapacityReopeningRuntimeContributionDisposition_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
      sourceIndex index).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningContributionEntryAt oldVisit
          (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
            sourceIndex index)) =
      .evolved
        (contributionCapacityReopeningRuntimeContributionEvolutionAt oldVisit
          sourceIndex index) :=
  contributionCapacityReopeningRuntimePayment_everyRow_evolved oldVisit
    sourceIndex index (0 : Fin 3)

/-! ## Action-target exact renewal fibre -/

/-- A hypothetical strict payment of the inherited contribution by the
reopening action target.  The Payment, disposition and lineage all refer to
the compiler-selected row zero; only strict debit is impossible. -/
structure ExactContributionCapacityReopeningActionRenewalPaymentAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Type 19 where
  private mk ::
  payment : ContributionCapacityReopeningActionPaymentAt oldVisit sourceIndex
  paymentExact : payment =
    sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
      sourceIndex
  oldOrigin : ContributionCapacityReopeningU8ContributionOriginAt oldVisit
  oldOriginExact : oldOrigin =
    contributionCapacityReopeningU8ContributionOriginAt oldVisit
  dispositionExact :
    payment.targetEvent.wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningContributionEntryAt oldVisit 0) =
      .evolved
        (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
          sourceIndex (0 : Fin 3))
  compilerEvolutionExact : HEq
    (contributionCapacityReopeningActionTargetRowEvolutionAt oldVisit
      sourceIndex (0 : Fin 3))
    (contributionCapacityReopeningActionContributionEvolutionAt oldVisit)
  sameDebt : RootDebtLineageAt (ReopeningNAt oldVisit)
    (contributionCapacityReopeningContributionEntryAt oldVisit 0)
    (contributionCapacityReopeningContributionEntryAt oldVisit 1)
  sameDebtExact : sameDebt =
    contributionCapacityReopeningActionContributionLineageAt oldVisit
  strictDebit :
    (contributionCapacityReopeningContributionEntryAt oldVisit 1
      ).progressBudget <
      (contributionCapacityReopeningContributionEntryAt oldVisit 0
        ).progressBudget

theorem exactContributionCapacityReopeningActionRenewalPayment_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (ExactContributionCapacityReopeningActionRenewalPaymentAt oldVisit
        sourceIndex) := by
  constructor
  intro payment
  have sourceZero :=
    contributionCapacityReopeningContribution_budget_zero oldVisit 0
  have targetZero :=
    contributionCapacityReopeningContribution_budget_zero oldVisit 1
  have strict := payment.strictDebit
  rw [sourceZero, targetZero] at strict
  exact Nat.not_lt_zero _ strict

/-! ## Positive-current runtime exact renewal fibre -/

/-- A hypothetical strict payment of the same inherited contribution by one
existing positive-current actual-service Payment. -/
structure ExactContributionCapacityReopeningRuntimeRenewalPaymentAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 19 where
  private mk ::
  payment : SourceGeneratedContributionCapacityReopeningRuntimePaymentAt
    oldVisit sourceIndex index
  oldOrigin : ContributionCapacityReopeningU8ContributionOriginAt oldVisit
  oldOriginExact : oldOrigin =
    contributionCapacityReopeningU8ContributionOriginAt oldVisit
  dispositionExact :
    (contributionCapacityReopeningRuntimePaymentRootEventAt oldVisit
      sourceIndex index).wholeLedgerWriteBack.entryDisposition
        (contributionCapacityReopeningContributionEntryAt oldVisit
          (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
            sourceIndex index)) =
      .evolved
        (contributionCapacityReopeningRuntimePaymentRowEvolutionAt oldVisit
          sourceIndex index (0 : Fin 3))
  compilerEvolutionExact : HEq
    (contributionCapacityReopeningRuntimePaymentRowEvolutionAt oldVisit
      sourceIndex index (0 : Fin 3))
    (contributionCapacityReopeningRuntimeContributionEvolutionAt oldVisit
      sourceIndex index)
  sameDebt : RootDebtLineageAt (ReopeningNAt oldVisit)
    (contributionCapacityReopeningContributionEntryAt oldVisit
      (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
        sourceIndex index))
    (contributionCapacityReopeningContributionEntryAt oldVisit
      (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
        sourceIndex index + 1))
  sameDebtExact : sameDebt =
    contributionCapacityReopeningRuntimeContributionLineageAt oldVisit
      sourceIndex index
  strictDebit :
    (contributionCapacityReopeningContributionEntryAt oldVisit
      (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
        sourceIndex index + 1)).progressBudget <
      (contributionCapacityReopeningContributionEntryAt oldVisit
        (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
          sourceIndex index)).progressBudget

theorem exactContributionCapacityReopeningRuntimeRenewalPayment_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (ExactContributionCapacityReopeningRuntimeRenewalPaymentAt oldVisit
        sourceIndex index) := by
  constructor
  intro payment
  have sourceZero :=
    contributionCapacityReopeningContribution_budget_zero oldVisit
      (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
        sourceIndex index)
  have targetZero :=
    contributionCapacityReopeningContribution_budget_zero oldVisit
      (contributionCapacityReopeningRuntimePaymentCurrentAt oldVisit
        sourceIndex index + 1)
  have strict := payment.strictDebit
  rw [sourceZero, targetZero] at strict
  exact Nat.not_lt_zero _ strict

/-! ## Negative controls -/

set_option linter.unusedVariables false in
theorem reopeningRenewalDeath_hasNoBarePaymentOrCallerCoordinates
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  fail_if_success
    exact
      (sourceGeneratedContributionCapacityReopeningActionPaymentAt oldVisit
        sourceIndex :
        ExactContributionCapacityReopeningActionRenewalPaymentAt oldVisit
          sourceIndex)
  fail_if_success
    exact
      (sourceGeneratedContributionCapacityReopeningRuntimePaymentAt oldVisit
        sourceIndex index :
        ExactContributionCapacityReopeningRuntimeRenewalPaymentAt oldVisit
          sourceIndex index)
  fail_if_success
    exact (fun payment :
      ExactContributionCapacityReopeningActionRenewalPaymentAt oldVisit
        sourceIndex => payment.target)
  fail_if_success
    exact (fun payment :
      ExactContributionCapacityReopeningActionRenewalPaymentAt oldVisit
        sourceIndex => payment.history)
  fail_if_success
    exact (fun payment :
      ExactContributionCapacityReopeningRuntimeRenewalPaymentAt oldVisit
        sourceIndex index => payment.date)
  fail_if_success
    exact (fun payment :
      ExactContributionCapacityReopeningRuntimeRenewalPaymentAt oldVisit
        sourceIndex index => payment.future)
  trivial

end
end M14SourceGeneratedContributionCapacityReopeningRenewalDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningRenewalDeath.contributionCapacityReopeningU8ContributionOriginAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningRenewalDeath.exactContributionCapacityReopeningActionRenewalPayment_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityReopeningRenewalDeath.exactContributionCapacityReopeningRuntimeRenewalPayment_isEmpty
