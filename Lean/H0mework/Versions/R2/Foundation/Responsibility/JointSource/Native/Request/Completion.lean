import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Math
import H0mework.Foundation.Responsibility.JointSource.Progress

/-! The existing canonical complete-native visits pay the entire expression.
Completion reads its original value from the actual paid history. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Completion

open SourceOperationEffects SourceOperationExecution RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program)

def event (count : Nat) := (finiteVisit old program registered scope count).current.2

theorem next_state (count : Nat) : (event old program registered scope (count + 1)).state =
    mathTarget (event old program registered scope count) :=
  (native program registered (finiteVisit old program registered scope count).current).next_state

theorem budget (count : Nat) : remaining (event old program registered scope count).state.1 =
    remaining registered.input.expression - count := by
  induction count with
  | zero => rfl
  | succ count prior =>
      rw [next_state, mathTarget_budget, prior, Nat.sub_sub]

theorem history_accounting (count : Nat) :
    (event old program registered scope count).state.2.length +
        remaining (event old program registered scope count).state.1 = remaining registered.input.expression :=
  (event old program registered scope count).state.2.remaining_eq.symm

def completedEvent := event old program registered scope (remaining registered.input.expression)

theorem completed_budget : remaining (completedEvent old program registered scope).state.1 = 0 := by
  rw [completedEvent, budget, Nat.sub_self]

def completed : SourceOperationExecutionDebt.Settlement (completedEvent old program registered scope).state :=
  localSettlement (completedEvent old program registered scope) (completed_budget old program registered scope)

theorem completed_value : (completed old program registered scope).1 =
    registered.input.expression.eval registered.input.environment :=
  local_completed_value (completedEvent old program registered scope) (completed old program registered scope)

theorem completed_history_length : (completedEvent old program registered scope).state.2.length =
    remaining registered.input.expression := by
  have account := history_accounting old program registered scope (remaining registered.input.expression)
  change (completedEvent old program registered scope).state.2.length +
    remaining (completedEvent old program registered scope).state.1 = _ at account
  simpa only [completed_budget, Nat.add_zero] using account

theorem completed_next_state :
    (event old program registered scope (remaining registered.input.expression + 1)).state =
      (completedEvent old program registered scope).state := by
  rw [next_state]
  exact mathTarget_eq_of_zero (completedEvent old program registered scope)
    (completed_budget old program registered scope)

end
end RootGeneratedDebtActivationJointSource.Native.Request.Completion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
