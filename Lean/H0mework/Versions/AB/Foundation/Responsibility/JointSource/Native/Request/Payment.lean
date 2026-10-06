import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Runtime
import H0mework.Foundation.Responsibility.JointSource.Native.Receipt
import H0mework.Foundation.Responsibility.JointSource.Progress
import H0mework.Versions.R2.Foundation.Responsibility.NoetherianClosure

/-! Actual canonical destination receipts pay the tracked mathematical debt.
The fixed-network process is a restriction of the existing inquiry nodes. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Payment

open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program)

private theorem finiteDepth (count : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit old program registered scope count).history = count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit old program registered scope count).history + 1 = count + 1
      rw [previous]

def postBirthProcess : SourceNativeLivingRootProcess (NewN old registered) where
  State := ULift.{u, 0} Nat
  stateAt := fun depth => ⟨NewV old program registered, targetRoot old program registered scope,
    mathVisit old program registered scope depth.down⟩
  stateAt_injective := by
    intro left right same
    have depths := congrArg (fun current : SourceNativeLivingRootCurrentAt (NewN old registered) =>
      match current.visit.history with
      | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
      | .postCofinal _ => none) same
    change some (ProductiveFiniteRootHistoryAt.causalDepth
      (finiteVisit old program registered scope (left.down + 1)).history) =
        some (ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit old program registered scope (right.down + 1)).history) at depths
    rw [finiteDepth, finiteDepth] at depths
    exact ULift.ext _ _ (Nat.add_right_cancel (Option.some.inj depths))
  initial := ⟨0⟩
  successorAt := by
    intro depth
    refine ⟨⟨depth.down + 1⟩, ?_, ?_⟩
    · change (⟨NewV old program registered, (targetRoot old program registered scope).toAuthoritativeRoot,
        mathVisit old program registered scope (depth.down + 1)⟩ : SourceNativeAuthoritativeRootCurrentAt (NewN old registered)) =
        (targetRoot old program registered scope).generatedNextCurrentAt (mathVisit old program registered scope depth.down)
      symm
      apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
      rfl
    · change HEq (targetRoot old program registered scope) (targetRoot old program registered scope)
      rfl

def canonicalSuccessor (depth : Nat) : SourceNativeLedgerGeneratedSuccessorAt
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old program registered scope depth)).occurrence
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old program registered scope depth)).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (mathVisit old program registered scope depth)).wholeLedgerWriteBack).get (by rfl)

theorem canonical_next (depth : Nat) : (canonicalSuccessor old program registered scope depth).targetCurrent =
    mathCurrent old program registered scope (depth + 1) := rfl

theorem destination_math (depth : Nat) :
    ((canonicalSuccessor old program registered scope depth).ledgerEvolution.destination
      (mathEntry old program registered scope depth)).1 = mathEntry old program registered scope (depth + 1) :=
  patch_destination_math program registered (mathCurrent old program registered scope depth)

def rowLineage (depth : Nat) : RootDebtLineageAt (NewN old registered)
    (mathEntry old program registered scope 0) (mathEntry old program registered scope depth) := by
  cases depth with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth =>
      exact (rowLineage depth).trans ((destination_math old program registered scope depth) ▸
        ((canonicalSuccessor old program registered scope depth).ledgerEvolution.destination
          (mathEntry old program registered scope depth)).2.toDebtLineage)

def debtCurrent (depth : Nat) :
    SourceNativeRootDebtCurrentAt (postBirthProcess old program registered scope)
      (mathEntry old program registered scope 0) where
  state := ⟨depth⟩
  entry := mathEntry old program registered scope depth
  sameDebt := rowLineage old program registered scope depth

def debtStep (depth : Nat) : SourceNativeRootDebtStepAt (debtCurrent old program registered scope depth) where
  targetEntry := ((canonicalSuccessor old program registered scope depth).ledgerEvolution.destination
    (mathEntry old program registered scope depth)).1
  evolution := ((canonicalSuccessor old program registered scope depth).ledgerEvolution.destination
    (mathEntry old program registered scope depth)).2
  sameDebtTarget_unique := by
    intro entry same
    have unique : entry = mathEntry old program registered scope (depth + 1) := by
      rcases entry with ⟨responsibility, opened⟩
      cases responsibility with
      | inl inherited => exact nomatch same.claim_eq
      | inr debt => cases debt; rcases opened with ⟨⟨proof⟩⟩; rfl
    exact unique.trans (destination_math old program registered scope depth).symm

theorem no_refill (depth : Nat) :
    (debtStep old program registered scope depth).targetEntry.progressBudget ≤
      (debtCurrent old program registered scope depth).budget :=
  (debtStep old program registered scope depth).progressBudget_not_refilled

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
  (mathCurrent old program registered scope depth).2.state)
variable (action : mathAction (mathCurrent old program registered scope depth).2 = .inr paid)

include action in
theorem canonical_paid_receipt :
    HEq (canonicalSuccessor old program registered scope depth).ledgerEvolution.destination
      (jointStepLedgerEvolution (law := Idle.law registered.input.environment registered.input.expression)
        (native program registered (mathCurrent old program registered scope depth)).baseLedger
        (mathCurrent old program registered scope depth).2.owner paid.2).destination :=
  paid_destination program registered (mathCurrent old program registered scope depth) paid action

def payment : SourceNativeRootDebtPaymentStepAt (debtCurrent old program registered scope depth) where
  step := debtStep old program registered scope depth
  strictDebit := by
    let actual := native program registered (mathCurrent old program registered scope depth)
    have nextState : (mathCurrent old program registered scope (depth + 1)).2.state = paid.1 :=
      actual.next_state.trans (by
        unfold mathTarget
        rw [action])
    have supportEq : supportAt registered (mathCurrent old program registered scope (depth + 1)) =
        (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf actual.targetOccurrence,
          some paid.1) :=
      Prod.ext (congrArg old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        actual.target_emitted.symm) (congrArg some nextState)
    have budgets := receipt_budget supportEq
      (canonical_paid_receipt old program registered scope depth paid action)
      (mathEntry old program registered scope depth)
    change ((canonicalSuccessor old program registered scope depth).ledgerEvolution.destination
      (mathEntry old program registered scope depth)).1.progressBudget <
        (mathEntry old program registered scope depth).progressBudget
    exact lt_of_eq_of_lt budgets (jointStepLedgerEvolution_debt_strict actual.baseLedger
      (mathCurrent old program registered scope depth).2.owner paid.2)

def generatePayment : SourceOperationExecutionDebt.Settlement (mathCurrent old program registered scope depth).2.state ⊕
    SourceNativeRootDebtPaymentStepAt (debtCurrent old program registered scope depth) := by
  cases selected : mathAction (mathCurrent old program registered scope depth).2 with
  | inl settled => exact .inl settled
  | inr actual => exact .inr (payment old program registered scope depth actual selected)

def paidContinuation : SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old program registered scope depth) :=
  .ofPayment .refl (payment old program registered scope depth paid action) .refl

theorem paidContinuation_wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process := postBirthProcess old program registered scope) (origin := mathEntry old program registered scope 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

theorem no_paid_of_zero (zero : remaining (mathCurrent old program registered scope depth).2.state.1 = 0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old program registered scope depth)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero _ zero

theorem zero_next_history (zero : remaining (mathCurrent old program registered scope depth).2.state.1 = 0) :
    (mathCurrent old program registered scope (depth + 1)).2.state =
      (mathCurrent old program registered scope depth).2.state :=
  (native program registered (mathCurrent old program registered scope depth)).next_state.trans
    (mathTarget_eq_of_zero (mathCurrent old program registered scope depth).2 zero)

section ActualRuntime

variable (inputs : old.Query → RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (owners : (query : old.Query) → (inputs query).input.owner = old.entryAt query)
variable (payments : (query : old.Query) →
  GeneratedStepAt (Idle.law (inputs query).input.environment (inputs query).input.expression)
    (initialEvent (inputs query)).state)
variable (actions : (query : old.Query) → mathAction (initialEvent (inputs query)) = .inr (payments query))
variable (audits : (query : old.Query) → (old.compileInquiry query).audit = .answered)

section UniqueQuery
variable [Unique old.Query]

theorem actual_node (count : Nat) :
    ((inquiryRuntime old program inputs scope owners payments actions audits).stateAt (count + 1)).engine.node =
      .active (mathPresentation old program (inputs default) scope count) :=
  stateAt_afterBirth_node old program inputs scope owners payments actions audits count

theorem postBirthProcess_actual (count : Nat) :
    ((inquiryRuntime old program inputs scope owners payments actions audits).stateAt (count + 1)).engine.node.erase =
      (⟨NewN old (inputs default),
        ⟨NewV old program (inputs default), (targetRoot old program (inputs default) scope).toAuthoritativeRoot,
          mathVisit old program (inputs default) scope count⟩⟩ : AnyAuthoritativeRootCurrent.{u}) := by
  rw [actual_node old program scope inputs owners payments actions audits]
  rfl

theorem macro_next_actual (count : Nat) :
    ((inquiryRuntime old program inputs scope owners payments actions audits).tickAt (count + 1)).next.node.erase =
      (⟨NewN old (inputs default),
        ⟨NewV old program (inputs default), (targetRoot old program (inputs default) scope).toAuthoritativeRoot,
          mathVisit old program (inputs default) scope (count + 1)⟩⟩ : AnyAuthoritativeRootCurrent.{u}) :=
  (congrArg (fun engine => engine.node.erase)
    (SourceNativeInquiryRuntime.stateAt_succ_engine
      (inquiryRuntime old program inputs scope owners payments actions audits) (count + 1))).symm.trans
        (postBirthProcess_actual old program scope inputs owners payments actions audits (count + 1))

end UniqueQuery

variable (input : Engine.SourceNativeInquiryRegisteredInputAt
  (Engine.initial (inquiryProcess old program inputs scope owners payments actions audits)))

theorem registered_actual_node (count : Nat) :
    ((inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).stateAt (count + 1)).engine.node =
      .active (mathPresentation old program (inputs input.query) scope count) :=
  registered_stateAt_afterBirth_node old program inputs scope owners payments actions audits input count

theorem registered_postBirthProcess_actual (count : Nat) :
    ((inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).stateAt (count + 1)).engine.node.erase =
      (⟨NewN old (inputs input.query),
        ⟨NewV old program (inputs input.query), (targetRoot old program (inputs input.query) scope).toAuthoritativeRoot,
          mathVisit old program (inputs input.query) scope count⟩⟩ : AnyAuthoritativeRootCurrent.{u}) := by
  rw [registered_actual_node old program scope inputs owners payments actions audits input]
  rfl

theorem registered_macro_next_actual (count : Nat) :
    ((inquiryRuntimeRegistered old program inputs scope owners payments actions audits input).tickAt (count + 1)).next.node.erase =
      (⟨NewN old (inputs input.query),
        ⟨NewV old program (inputs input.query), (targetRoot old program (inputs input.query) scope).toAuthoritativeRoot,
          mathVisit old program (inputs input.query) scope (count + 1)⟩⟩ : AnyAuthoritativeRootCurrent.{u}) :=
  (congrArg (fun engine => engine.node.erase)
    (SourceNativeInquiryRuntime.stateAt_succ_engine
      (inquiryRuntimeRegistered old program inputs scope owners payments actions audits input) (count + 1))).symm.trans
        (registered_postBirthProcess_actual old program scope inputs owners payments actions audits input (count + 1))

end ActualRuntime

end
end RootGeneratedDebtActivationJointSource.Native.Request.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
