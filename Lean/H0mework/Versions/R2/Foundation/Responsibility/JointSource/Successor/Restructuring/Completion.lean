import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Runtime
import H0mework.Foundation.Responsibility.JointSource.Progress

/-! The installed source's actual sealed ticks pay its complete expression.
The final value and full trace are read from the same generated history. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion CompilerFromPacketSourceLaw

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)
variable (packetAt : (current : V.Current) → Packet old.toLedgerRoot current)

def runtime (count : Nat) : Runtime old registered packetAt :=
  (initialRuntime old registered packetAt).advance count

theorem runtime_depth (count : Nat) : (runtime old registered packetAt count).state.down = count := by
  induction count with
  | zero => rfl
  | succ count prior =>
      change (runtime old registered packetAt count).state.down + 1 = count + 1
      exact congrArg (fun depth => depth + 1) prior

def event (count : Nat) := (runtimeCurrent old registered packetAt (runtime old registered packetAt count)).2

theorem next_state (count : Nat) : (event old registered packetAt (count + 1)).state =
    mathTarget (event old registered packetAt count) :=
  tick_math old registered packetAt (runtime old registered packetAt count)

theorem initial_state : (event old registered packetAt 0).state = (initialEvent registered).state := rfl

theorem budget (count : Nat) : remaining (event old registered packetAt count).state.1 =
    remaining registered.input.expression - count := by
  induction count with
  | zero => rfl
  | succ count prior =>
      rw [next_state, mathTarget_budget, prior, Nat.sub_sub]

theorem history_accounting (count : Nat) :
    (event old registered packetAt count).state.2.length +
      remaining (event old registered packetAt count).state.1 = remaining registered.input.expression :=
  (event old registered packetAt count).state.2.remaining_eq.symm

def completedRuntime := runtime old registered packetAt (remaining registered.input.expression)
def completedEvent := event old registered packetAt (remaining registered.input.expression)

theorem completed_budget : remaining (completedEvent old registered packetAt).state.1 = 0 := by
  rw [completedEvent, budget, Nat.sub_self]

def completed : SourceOperationExecutionDebt.Settlement (completedEvent old registered packetAt).state :=
  localSettlement (completedEvent old registered packetAt) (completed_budget old registered packetAt)

theorem completed_value : (completed old registered packetAt).1 =
    registered.input.expression.eval registered.input.environment :=
  local_completed_value (completedEvent old registered packetAt) (completed old registered packetAt)

theorem completed_history_length : (completedEvent old registered packetAt).state.2.length =
    remaining registered.input.expression := by
  have account := history_accounting old registered packetAt (remaining registered.input.expression)
  change (completedEvent old registered packetAt).state.2.length +
    remaining (completedEvent old registered packetAt).state.1 = _ at account
  simpa only [completed_budget, Nat.add_zero] using account

theorem completed_next_state :
    (event old registered packetAt (remaining registered.input.expression + 1)).state =
      (completedEvent old registered packetAt).state := by
  rw [next_state]
  exact mathTarget_eq_of_zero (completedEvent old registered packetAt) (completed_budget old registered packetAt)

end RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
