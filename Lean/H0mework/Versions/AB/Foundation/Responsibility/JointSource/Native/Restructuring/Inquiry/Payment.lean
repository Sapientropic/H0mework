import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Math
import H0mework.Foundation.Responsibility.JointSource.Native.Receipt
import H0mework.Foundation.Responsibility.JointSource.Progress
import H0mework.Versions.R2.Foundation.Responsibility.NoetherianClosure

/-! Actual full destination receipts pay the math row of the existing general
inquiry root. The debt current is a restriction of its original process. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Payment
open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger RootInquiryCompletion
noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)

def canonicalSuccessor (depth : Nat) : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old program registered depth)).occurrence
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old program registered depth)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old program registered depth)).wholeLedgerWriteBack).get (by rfl)

theorem canonical_next (depth : Nat) : (canonicalSuccessor old program registered depth).targetCurrent =
    mathCurrent old program registered (depth + 1) := rfl

theorem destination_math (depth : Nat) :
    ((canonicalSuccessor old program registered depth).ledgerEvolution.destination
      (mathEntry old program registered depth)).1 = mathEntry old program registered (depth + 1) :=
  patch_destination_math program registered (mathCurrent old program registered depth)

def rowLineage (depth : Nat) : RootDebtLineageAt (World registered)
    (mathEntry old program registered 0) (mathEntry old program registered depth) := by
  cases depth with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth =>
      exact (rowLineage depth).trans ((destination_math old program registered depth) ▸
        ((canonicalSuccessor old program registered depth).ledgerEvolution.destination
          (mathEntry old program registered depth)).2.toDebtLineage)

def debtCurrent (depth : Nat) :
    SourceNativeRootDebtCurrentAt (Inquiry.process old program registered)
      (mathEntry old program registered 0) where
  state := ⟨depth + 1⟩
  entry := mathEntry old program registered depth
  sameDebt := rowLineage old program registered depth

def debtStep (depth : Nat) : SourceNativeRootDebtStepAt (debtCurrent old program registered depth) where
  targetEntry := ((canonicalSuccessor old program registered depth).ledgerEvolution.destination
    (mathEntry old program registered depth)).1
  evolution := ((canonicalSuccessor old program registered depth).ledgerEvolution.destination
    (mathEntry old program registered depth)).2
  sameDebtTarget_unique := by
    intro entry same
    have unique : entry = mathEntry old program registered (depth + 1) := by
      rcases entry with ⟨responsibility, opened⟩
      cases responsibility with
      | inl inherited => exact nomatch same.claim_eq
      | inr debt => cases debt; rcases opened with ⟨⟨proof⟩⟩; rfl
    exact unique.trans (destination_math old program registered depth).symm

theorem no_refill (depth : Nat) :
    (debtStep old program registered depth).targetEntry.progressBudget ≤
      (debtCurrent old program registered depth).budget :=
  (debtStep old program registered depth).progressBudget_not_refilled

private theorem receipt_budget {W : WorldRelationNetwork.{u}} {source firstTarget secondTarget : W.Support}
    {first : LedgerWriteEvolutionAt W ⟨source⟩ ⟨firstTarget⟩}
    {second : LedgerWriteEvolutionAt W ⟨source⟩ ⟨secondTarget⟩}
    (supports : firstTarget = secondTarget) (receipt : HEq first.destination second.destination)
    (entry : OpenResponsibilityAt W source) :
    (first.destination entry).1.progressBudget = (second.destination entry).1.progressBudget := by
  cases supports
  exact congrArg (fun destination => (destination entry).1.progressBudget) (eq_of_heq receipt)

variable (depth : Nat)
variable (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression)
  (mathCurrent old program registered depth).2.state)
variable (action : mathAction (mathCurrent old program registered depth).2 = .inr paid)

include action in
theorem canonical_paid_receipt :
    HEq (canonicalSuccessor old program registered depth).ledgerEvolution.destination
      (jointStepLedgerEvolution (law := Idle.law registered.input.environment registered.input.expression)
        (native program registered (mathCurrent old program registered depth)).baseLedger
        (mathCurrent old program registered depth).2.owner paid.2).destination :=
  paid_destination program registered (mathCurrent old program registered depth) paid action

def payment : SourceNativeRootDebtPaymentStepAt (debtCurrent old program registered depth) where
  step := debtStep old program registered depth
  strictDebit := by
    let actual := native program registered (mathCurrent old program registered depth)
    have nextState : (mathCurrent old program registered (depth + 1)).2.state = paid.1 :=
      actual.next_state.trans (by
        unfold mathTarget
        rw [action])
    have supportEq : supportAt registered (mathCurrent old program registered (depth + 1)) =
        (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf actual.targetOccurrence,
          some paid.1) :=
      Prod.ext (congrArg old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        actual.target_emitted.symm) (congrArg some nextState)
    have budgets := receipt_budget supportEq
      (canonical_paid_receipt old program registered depth paid action)
      (mathEntry old program registered depth)
    change ((canonicalSuccessor old program registered depth).ledgerEvolution.destination
      (mathEntry old program registered depth)).1.progressBudget <
        (mathEntry old program registered depth).progressBudget
    exact lt_of_eq_of_lt budgets (jointStepLedgerEvolution_debt_strict actual.baseLedger
      (mathCurrent old program registered depth).2.owner paid.2)

def generatePayment : SourceOperationExecutionDebt.Settlement (mathCurrent old program registered depth).2.state ⊕
    SourceNativeRootDebtPaymentStepAt (debtCurrent old program registered depth) := by
  cases selected : mathAction (mathCurrent old program registered depth).2 with
  | inl settled => exact .inl settled
  | inr actual => exact .inr (payment old program registered depth actual selected)

def paidContinuation : SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old program registered depth) :=
  .ofPayment .refl (payment old program registered depth paid action) .refl

theorem paidContinuation_wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process := Inquiry.process old program registered) (origin := mathEntry old program registered 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

theorem no_paid_of_zero (zero : remaining (mathCurrent old program registered depth).2.state.1 = 0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old program registered depth)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero _ zero

theorem zero_next_history (zero : remaining (mathCurrent old program registered depth).2.state.1 = 0) :
    (mathCurrent old program registered (depth + 1)).2.state =
      (mathCurrent old program registered depth).2.state :=
  (native program registered (mathCurrent old program registered depth)).next_state.trans
    (mathTarget_eq_of_zero (mathCurrent old program registered depth).2 zero)


end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
