import H0mework.Foundation.Responsibility.NoetherianClosure

/-!
# Source-native Noetherian debt closure regressions

These checks lock the three authority boundaries of the composition law:

* zero credit cannot emit another paid macro;
* a macro cannot return the same debt current to itself;
* local terminal does not settle a debt which survives in the exact successor
  ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- The positive public consumer returns the exact generated terminal receipt. -/
def generated_noetherianDebtSettlementReceipt
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin)
    (current : SourceNativeRootDebtCurrentAt process origin) :
    Sigma fun target : SourceNativeRootDebtCurrentAt process origin =>
      LedgerEntryTerminalAt N target.entry :=
  law.generatedReceipt current

/-- Pure cross-face carry reads the same root debt and cannot manufacture a
payment by changing presentation. -/
theorem carried_root_faces_have_equal_budget
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (support_eq : sourceSupport = targetSupport)
    (entry_eq : HEq source target) :
    target.progressBudget = source.progressBudget :=
  LedgerEntryEvolutionAt.carried_progressBudget_eq support_eq entry_eq

/-- Prefix and suffix supply only no-refill context.  The public constructor
derives paid macro authority from the exact payment step itself. -/
def generated_paidMacro_of_exactPayment
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source paymentSource target :
      SourceNativeRootDebtCurrentAt process origin}
    (beforeHistory : SourceNativeRootDebtMacroHistoryAt source paymentSource)
    (payment : SourceNativeRootDebtPaymentStepAt paymentSource)
    (afterHistory : SourceNativeRootDebtMacroHistoryAt
      (paymentSource.next payment.step) target) :
    SourceNativePaidRootDebtMacroContinuationAt source :=
  SourceNativePaidRootDebtMacroContinuationAt.ofPayment
    beforeHistory payment afterHistory

/-- Equality-only evolution cannot be relabelled as a strict payment. -/
theorem equality_only_step_cannot_pay
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {source : SourceNativeRootDebtCurrentAt process origin}
    (payment : SourceNativeRootDebtPaymentStepAt source)
    (budget_eq : (source.next payment.step).budget = source.budget) : False :=
  payment.target_budget_ne_source budget_eq

/-- A total closure law must settle immediately when the tracked debt has no
remaining progress credit. -/
theorem noetherianDebtClosure_emits_settlement_of_budget_eq_zero
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (law : SourceNativeNoetherianDebtClosureLaw process origin)
    (current : SourceNativeRootDebtCurrentAt process origin)
    (budget_eq : current.budget = 0) :
    ∃ settlement : SourceNativeRootDebtSettlementAt current,
      law.emit current = .inl settlement := by
  cases emitted_eq : law.emit current with
  | inl settlement =>
      exact ⟨settlement, rfl⟩
  | inr continuation =>
      exact False.elim
        ((no_paidRootDebtMacroContinuation_of_budget_eq_zero
          current budget_eq).false continuation)

/-- A strict paid macro cannot self-seal by returning the tracked debt to the
same complete process current. -/
theorem no_paidRootDebtMacroContinuation_to_self
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    (current : SourceNativeRootDebtCurrentAt process origin)
    (continuation : SourceNativePaidRootDebtMacroContinuationAt current)
    (target_eq : continuation.target = current) : False := by
  have strict := continuation.strictDebit
  rw [target_eq] at strict
  exact Nat.lt_irrefl _ strict

/-- A local root terminal cannot close a debt while the exact generated
successor ledger still contains that same lineage and claim. -/
theorem localTerminal_with_sameDebtTarget_not_settlement
    {N : WorldRelationNetwork.{u}}
    {process : SourceNativeLivingRootProcess N}
    {originSupport : N.Support}
    {origin : OpenResponsibilityAt N originSupport}
    {current : SourceNativeRootDebtCurrentAt process origin}
    (_localTerminal : SourceNativeRootDebtLocalTerminalAt current)
    (survives : SourceNativeRootDebtTargetAt current) :
    IsEmpty (SourceNativeRootDebtSettlementAt current) where
  false settlement := settlement.noSameDebtAtTarget.false survives

#print axioms RootDebtLineageAt.trans
#print axioms LedgerEntryEvolutionAt.toDebtLineage
#print axioms LedgerEntryEvolutionAt.carried_progressBudget_eq
#print axioms SourceNativeRootDebtCurrentAt.next_budget_le
#print axioms SourceNativeRootDebtMacroHistoryAt.target_budget_le_source
#print axioms SourceNativeRootDebtPaymentStepAt.target_budget_ne_source
#print axioms SourceNativePaidRootDebtMacroContinuationAt.ofPayment
#print axioms SourceNativePaidRootDebtMacroContinuationAt.strictDebit
#print axioms no_paidRootDebtMacroContinuation_of_budget_eq_zero
#print axioms SourceNativeRootDebtLocalTerminalAt.receipt
#print axioms SourceNativeNoetherianDebtClosureLaw.continuationRel_wellFounded
#print axioms SourceNativeNoetherianDebtClosureLaw.generatedHistory
#print axioms SourceNativeNoetherianDebtClosureLaw.generatedReceipt
#print axioms generated_noetherianDebtSettlementReceipt
#print axioms carried_root_faces_have_equal_budget
#print axioms generated_paidMacro_of_exactPayment
#print axioms equality_only_step_cannot_pay
#print axioms noetherianDebtClosure_emits_settlement_of_budget_eq_zero
#print axioms no_paidRootDebtMacroContinuation_to_self
#print axioms localTerminal_with_sameDebtTarget_not_settlement

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
