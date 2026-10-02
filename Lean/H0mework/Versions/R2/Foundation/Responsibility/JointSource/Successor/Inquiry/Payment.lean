import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Math
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Completion
import H0mework.Versions.R2.Foundation.Responsibility.NoetherianClosure

/-! The original fixed source runtime's complete receipt pays the mathematical
debt. This debt restriction retains that exact authority root; the inquiry's
additional token cofaces share its ledger and are not identified as roots. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment
open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger RootInquiryCompletion CompilerFromPacketSourceLaw
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current)

abbrev process := Restructuring.process old.root.toAuthoritativeRoot registered packetAt

def mathVisit (depth : Nat) :=
  Restructuring.temporalVisit old.root.toAuthoritativeRoot registered packetAt (depth + 1)

def mathCurrent (depth : Nat) :=
  (Restructuring.finiteVisit old.root.toAuthoritativeRoot registered packetAt (depth + 1)).current

def mathEntry (depth : Nat) := CompilerFromPacketSourceLaw.mathEntry registered (mathCurrent old registered packetAt depth)

/-- The canonical whole write at the exact original process restriction. -/
def canonicalSuccessor (depth : Nat) : SourceNativeLedgerGeneratedSuccessorAt
    ((Restructuring.authoritativeRoot old.root.toAuthoritativeRoot registered packetAt).toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old registered packetAt depth)).occurrence
    ((Restructuring.authoritativeRoot old.root.toAuthoritativeRoot registered packetAt).toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old registered packetAt depth)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((Restructuring.authoritativeRoot old.root.toAuthoritativeRoot registered packetAt).toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old registered packetAt depth)).wholeLedgerWriteBack).get (by rfl)

theorem canonical_next (depth : Nat) : (canonicalSuccessor old registered packetAt depth).targetCurrent =
    mathCurrent old registered packetAt (depth + 1) := rfl

theorem actual_tick_receipt (depth : Nat) :
    HEq (Restructuring.tickSuccessor old.root.toAuthoritativeRoot registered packetAt
      (Restructuring.Completion.runtime old.root.toAuthoritativeRoot registered packetAt (depth + 1))).ledgerEvolution
      (canonicalSuccessor old registered packetAt depth).ledgerEvolution := by
  have atDepth := Restructuring.Completion.runtime_depth old.root.toAuthoritativeRoot registered packetAt (depth + 1)
  change HEq (patch registered packetAt
    (Restructuring.finiteVisit old.root.toAuthoritativeRoot registered packetAt
      (Restructuring.Completion.runtime old.root.toAuthoritativeRoot registered packetAt (depth + 1)).state.down).current).toLedgerWriteEvolution
    (patch registered packetAt (mathCurrent old registered packetAt depth)).toLedgerWriteEvolution
  rw [atDepth]
  rfl

theorem destination_math (depth : Nat) :
    ((canonicalSuccessor old registered packetAt depth).ledgerEvolution.destination
      (mathEntry old registered packetAt depth)).1 = mathEntry old registered packetAt (depth + 1) :=
  (congrArg (fun evolution => (evolution.destination (mathEntry old registered packetAt depth)).1)
    (patch_fold registered packetAt (mathCurrent old registered packetAt depth))).trans
    (join_destination_math (packetAt (mathCurrent old registered packetAt depth).1)
      (mathCurrent old registered packetAt depth).2)

def rowLineage (depth : Nat) : RootDebtLineageAt (World registered)
    (mathEntry old registered packetAt 0) (mathEntry old registered packetAt depth) := by
  cases depth with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth =>
      exact (rowLineage depth).trans ((destination_math old registered packetAt depth) ▸
        ((canonicalSuccessor old registered packetAt depth).ledgerEvolution.destination
          (mathEntry old registered packetAt depth)).2.toDebtLineage)

def debtCurrent (depth : Nat) : SourceNativeRootDebtCurrentAt (process old registered packetAt)
    (mathEntry old registered packetAt 0) where
  state := ⟨depth + 1⟩
  entry := mathEntry old registered packetAt depth
  sameDebt := rowLineage old registered packetAt depth

def debtStep (depth : Nat) : SourceNativeRootDebtStepAt (debtCurrent old registered packetAt depth) where
  targetEntry := ((canonicalSuccessor old registered packetAt depth).ledgerEvolution.destination
    (mathEntry old registered packetAt depth)).1
  evolution := ((canonicalSuccessor old registered packetAt depth).ledgerEvolution.destination
    (mathEntry old registered packetAt depth)).2
  sameDebtTarget_unique := by
    intro entry same
    have unique : entry = mathEntry old registered packetAt (depth + 1) := by
      rcases entry with ⟨responsibility, opened⟩
      cases responsibility with
      | inl inherited => exact nomatch same.claim_eq
      | inr debt => cases debt; rcases opened with ⟨⟨proof⟩⟩; rfl
    exact unique.trans (destination_math old registered packetAt depth).symm

theorem no_refill (depth : Nat) : (debtStep old registered packetAt depth).targetEntry.progressBudget ≤
    (debtCurrent old registered packetAt depth).budget :=
  (debtStep old registered packetAt depth).progressBudget_not_refilled

private theorem destination_heq {W : WorldRelationNetwork.{u}} {source leftTarget rightTarget : W.Support}
    {left : LedgerWriteEvolutionAt W ⟨source⟩ ⟨leftTarget⟩}
    {right : LedgerWriteEvolutionAt W ⟨source⟩ ⟨rightTarget⟩}
    (supports : leftTarget = rightTarget) (receipt : HEq left right) :
    HEq left.destination right.destination := by
  cases supports
  cases eq_of_heq receipt
  rfl

private theorem receipt_budget {W : WorldRelationNetwork.{u}} {source leftTarget rightTarget : W.Support}
    {left : LedgerWriteEvolutionAt W ⟨source⟩ ⟨leftTarget⟩}
    {right : LedgerWriteEvolutionAt W ⟨source⟩ ⟨rightTarget⟩}
    (supports : leftTarget = rightTarget) (receipt : HEq left.destination right.destination)
    (entry : OpenResponsibilityAt W source) :
    (left.destination entry).1.progressBudget = (right.destination entry).1.progressBudget := by
  cases supports
  exact congrArg (fun destination => (destination entry).1.progressBudget) (eq_of_heq receipt)

variable (depth : Nat)
variable (paid : GeneratedStepAt (scope registered) (mathCurrent old registered packetAt depth).2.state)
variable (action : mathAction (mathCurrent old registered packetAt depth).2 = .inr paid)

include action in
theorem next_paid : (mathCurrent old registered packetAt (depth + 1)).2.state = paid.1 := by
  change mathTarget (mathCurrent old registered packetAt depth).2 = paid.1
  unfold mathTarget
  rw [action]

include action in
theorem canonical_paid_receipt :
    HEq (canonicalSuccessor old registered packetAt depth).ledgerEvolution.destination
      (jointStepLedgerEvolution (law := scope registered)
        (originalFold (packetAt (mathCurrent old registered packetAt depth).1))
        (mathCurrent old registered packetAt depth).2.owner paid.2).destination :=
  (heq_of_eq (congrArg LedgerWriteEvolutionAt.destination
    (patch_fold registered packetAt (mathCurrent old registered packetAt depth)))).trans
    (destination_heq (congrArg (fun state =>
      (targetSupport (packetAt (mathCurrent old registered packetAt depth).1), some state))
        (next_paid old registered packetAt depth paid action))
      (join_whole_paid (packetAt (mathCurrent old registered packetAt depth).1)
        (mathCurrent old registered packetAt depth).2 paid action))

def payment : SourceNativeRootDebtPaymentStepAt (debtCurrent old registered packetAt depth) where
  step := debtStep old registered packetAt depth
  strictDebit := by
    have supports : supportAt registered (mathCurrent old registered packetAt (depth + 1)) =
        (targetSupport (packetAt (mathCurrent old registered packetAt depth).1), some paid.1) :=
      congrArg (fun state =>
        (targetSupport (packetAt (mathCurrent old registered packetAt depth).1), some state))
        (next_paid old registered packetAt depth paid action)
    have budgets := receipt_budget supports
      (canonical_paid_receipt old registered packetAt depth paid action) (mathEntry old registered packetAt depth)
    change ((canonicalSuccessor old registered packetAt depth).ledgerEvolution.destination
      (mathEntry old registered packetAt depth)).1.progressBudget < (mathEntry old registered packetAt depth).progressBudget
    exact lt_of_eq_of_lt budgets (jointStepLedgerEvolution_debt_strict
      (originalFold (packetAt (mathCurrent old registered packetAt depth).1))
      (mathCurrent old registered packetAt depth).2.owner paid.2)

def generatePayment : SourceOperationExecutionDebt.Settlement (mathCurrent old registered packetAt depth).2.state ⊕
    SourceNativeRootDebtPaymentStepAt (debtCurrent old registered packetAt depth) := by
  cases selected : mathAction (mathCurrent old registered packetAt depth).2 with
  | inl settled => exact .inl settled
  | inr actual => exact .inr (payment old registered packetAt depth actual selected)

def paidContinuation : SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old registered packetAt depth) :=
  .ofPayment .refl (payment old registered packetAt depth paid action) .refl

theorem paidContinuation_wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process := process old registered packetAt) (origin := mathEntry old registered packetAt 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

theorem no_paid_of_zero (zero : remaining (mathCurrent old registered packetAt depth).2.state.1 = 0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old registered packetAt depth)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero _ zero

theorem zero_next_history (zero : remaining (mathCurrent old registered packetAt depth).2.state.1 = 0) :
    (mathCurrent old registered packetAt (depth + 1)).2.state = (mathCurrent old registered packetAt depth).2.state :=
  (by change (targetCurrent registered packetAt (mathCurrent old registered packetAt depth)).2.state = _
      exact (math_next registered packetAt (mathCurrent old registered packetAt depth)).trans
        (mathTarget_eq_of_zero (mathCurrent old registered packetAt depth).2 zero))

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
