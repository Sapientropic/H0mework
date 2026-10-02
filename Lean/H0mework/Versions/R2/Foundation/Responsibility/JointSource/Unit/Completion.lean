import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Runtime
import H0mework.Foundation.Responsibility.JointSource.Unit.Progress

/-! The canonical ticks exhaust the source syntax budget and recover its value from the paid past. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects SourceOperationExecution DebtActivationWorld

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

def runtimeBudget (runtime : Runtime registered) : Nat :=
  remaining (runtimeCurrent registered runtime).2.state.1

theorem runtimeBudget_tick (runtime : Runtime registered) :
    runtimeBudget registered runtime.tick.next = runtimeBudget registered runtime - 1 := by
  unfold runtimeBudget
  rw [runtime_tick_math]
  exact mathTarget_budget _

theorem runtimeBudget_advance (runtime : Runtime registered) (count : Nat) :
    runtimeBudget registered (runtime.advance count) = runtimeBudget registered runtime - count := by
  induction count with
  | zero => simp only [LivingRuntimeState.advance, Nat.sub_zero]
  | succ count prior =>
      rw [LivingRuntimeState.advance, runtimeBudget_tick, prior, Nat.sub_sub]

def completionRuntime (runtime : Runtime registered) : Runtime registered :=
  runtime.advance (runtimeBudget registered runtime)

theorem completion_budget (runtime : Runtime registered) :
    runtimeBudget registered (completionRuntime registered runtime) = 0 := by
  rw [completionRuntime, runtimeBudget_advance, Nat.sub_self]

def completed (runtime : Runtime registered) :
    SourceOperationExecutionDebt.Settlement
      (runtimeCurrent registered (completionRuntime registered runtime)).2.state :=
  localSettlement _ (completion_budget registered runtime)

theorem completed_source_value (runtime : Runtime registered) :
    (completed registered runtime).1 =
      registered.input.expression.eval registered.input.environment :=
  local_completed_value _ (completed registered runtime)

theorem completed_next_state (runtime : Runtime registered) :
    (runtimeCurrent registered (completionRuntime registered runtime).tick.next).2.state =
      (runtimeCurrent registered (completionRuntime registered runtime)).2.state := by
  rw [runtime_tick_math]
  exact mathTarget_eq_of_zero _ (completion_budget registered runtime)

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
