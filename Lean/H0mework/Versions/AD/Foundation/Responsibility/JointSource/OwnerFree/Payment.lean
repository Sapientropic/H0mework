import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Calculation
import H0mework.Versions.R2.Foundation.Responsibility.NoetherianClosure

/-! The actual calculation patch supplies the unique same-debt successor.
Strict debit is read from the source-selected step; the existing process and
Noetherian consumer retain the complete clock, inventory and source law. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Payment
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin → Raw (Value:=Value) (Var:=Var) (sort:=sort))

def entry (count : Nat) := mathEntry old origin reader (finiteVisit old origin reader count).current

theorem destination_entry (count : Nat) :
    ((whole old origin reader (finiteVisit old origin reader count).current).destination
      (entry old origin reader count)).1 = entry old origin reader (count+1) :=
  destination_math old origin reader (finiteVisit old origin reader count).current

def lineage (count : Nat) : RootDebtLineageAt _ (entry old origin reader 0) (entry old origin reader count) := by
  induction count with
  | zero => exact ⟨rfl,rfl⟩
  | succ count prior =>
    exact prior.trans ((destination_entry old origin reader count) ▸
      ((whole old origin reader (finiteVisit old origin reader count).current).destination
        (entry old origin reader count)).2.toDebtLineage)

def debtCurrent (count : Nat) : SourceNativeRootDebtCurrentAt (process old origin reader) (entry old origin reader 0) where
  state := ⟨count⟩
  entry := entry old origin reader count
  sameDebt := lineage old origin reader count

def debtStep (count : Nat) : SourceNativeRootDebtStepAt (debtCurrent old origin reader count) where
  targetEntry := ((patch old origin reader (finiteVisit old origin reader count).current).toLedgerWriteEvolution.destination
    (entry old origin reader count)).1
  evolution := ((patch old origin reader (finiteVisit old origin reader count).current).toLedgerWriteEvolution.destination
    (entry old origin reader count)).2
  sameDebtTarget_unique := by
    intro alternative same
    rcases alternative with ⟨responsibility, opened⟩
    cases responsibility with
    | inl prior => exact nomatch same.claim_eq
    | inr debt =>
      cases debt
      rcases opened with ⟨⟨proof⟩⟩
      apply (destination_entry old origin reader count).symm.trans
      exact congrArg (fun write => (write.destination (entry old origin reader count)).1)
        (patch_fold old origin reader _).symm

def payment (count : Nat)
    (paid : GeneratedStepAt (law old origin reader) (finiteVisit old origin reader count).current)
    (selected : action old origin reader (finiteVisit old origin reader count).current = .inr paid) :
    SourceNativeRootDebtPaymentStepAt (debtCurrent old origin reader count) where
  step := debtStep old origin reader count
  strictDebit := by
    change (((patch old origin reader (finiteVisit old origin reader count).current).toLedgerWriteEvolution.destination
      (entry old origin reader count)).1).progressBudget < (entry old origin reader count).progressBudget
    have budgetRead := congrArg (fun write => (write.destination (entry old origin reader count)).1.progressBudget)
      (patch_fold old origin reader (finiteVisit old origin reader count).current)
    apply Eq.mp (congrArg (fun budget => budget < (entry old origin reader count).progressBudget) budgetRead.symm)
    have destinationRead := congrArg OpenResponsibilityAt.progressBudget
      (destination_math old origin reader (finiteVisit old origin reader count).current)
    apply Eq.mp (congrArg (fun budget => budget < (entry old origin reader count).progressBudget) destinationRead.symm)
    change remaining (nextState old origin reader (finiteVisit old origin reader count).current).1 <
      remaining (finiteVisit old origin reader count).current.1
    unfold nextState targetOf
    rw [selected]
    exact (law old origin reader).step_budget_lt paid.2

def generatePayment (count : Nat) :
    SourceOperationExecutionDebt.Settlement (finiteVisit old origin reader count).current ⊕
      SourceNativeRootDebtPaymentStepAt (debtCurrent old origin reader count) := by
  cases selected : action old origin reader (finiteVisit old origin reader count).current with
  | inl settled => exact .inl settled
  | inr paid => exact .inr (payment old origin reader count paid selected)

def paidContinuation (count : Nat)
    (paid : GeneratedStepAt (law old origin reader) (finiteVisit old origin reader count).current)
    (selected : action old origin reader (finiteVisit old origin reader count).current = .inr paid) :
    SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old origin reader count) :=
  .ofPayment .refl (payment old origin reader count paid selected) .refl

theorem wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process:=process old origin reader) (origin:=entry old origin reader 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

theorem no_refill (count : Nat) : (debtStep old origin reader count).targetEntry.progressBudget ≤
    (debtCurrent old origin reader count).budget := (debtStep old origin reader count).progressBudget_not_refilled

theorem no_paid_of_zero (count : Nat) (zero : (debtCurrent old origin reader count).budget=0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old origin reader count)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero _ zero

theorem current_state (count : Nat) : (finiteVisit old origin reader count).current =
    Completion.state old origin reader count := by
  change _ = (finiteVisit old origin reader (Completion.runtime old origin reader count).state.down).current
  exact congrArg (fun k => (finiteVisit old origin reader k).current)
    (Completion.runtime_depth old origin reader count).symm

def activePayment (count : Fin (remaining (raw old origin reader).expression)) :
    SourceNativeRootDebtPaymentStepAt (debtCurrent old origin reader count.1) := by
  cases selected : action old origin reader (finiteVisit old origin reader count.1).current with
  | inr paid => exact payment old origin reader count.1 paid selected
  | inl settled =>
    have zero := (law old origin reader).settlement_budget_zero settled
    change remaining (finiteVisit old origin reader count.1).current.1 = 0 at zero
    have budget := Completion.budget old origin reader count.1
    have current := current_state old origin reader count.1
    have stateBudget := congrArg (fun state : Current old origin reader => remaining state.1) current
    have actualBudget := stateBudget.trans budget
    omega

def activeContinuation (count : Fin (remaining (raw old origin reader).expression)) :
    SourceNativePaidRootDebtMacroContinuationAt (debtCurrent old origin reader count.1) :=
  .ofPayment .refl (activePayment old origin reader count) .refl

theorem budget (count : Nat) : (debtCurrent old origin reader count).budget =
    remaining (raw old origin reader).expression - count :=
  (congrArg (fun state : Current old origin reader => remaining state.1) (current_state old origin reader count)).trans
    (Completion.budget old origin reader count)

theorem endpoint_budget : (debtCurrent old origin reader (remaining (raw old origin reader).expression)).budget=0 := by
  exact (budget old origin reader _).trans (Nat.sub_self _)

theorem endpoint_no_paid : IsEmpty (SourceNativePaidRootDebtMacroContinuationAt
    (debtCurrent old origin reader (remaining (raw old origin reader).expression))) :=
  no_paid_of_zero old origin reader _ (endpoint_budget old origin reader)

end RootGeneratedDebtActivationJointSource.OwnerFree.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
