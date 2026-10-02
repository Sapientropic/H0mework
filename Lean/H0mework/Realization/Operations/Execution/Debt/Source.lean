import H0mework.Realization.Operations.Execution.Run
import H0mework.Foundation.Responsibility.DebtWorld

/-! The original source executor generates debt steps; state retains only its paid past trace. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationExecutionDebt

open SourceOperationEffects SourceOperationExecution DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

/-- Past execution prevents a leaf value from being substituted for the original source. -/
abbrev State (environment : Env Value Var) (source : Expr Value Var sort) : Type u :=
  Σ expression : Expr Value Var sort, Trace environment source expression

def initial (environment : Env Value Var) (source : Expr Value Var sort) : State environment source :=
  ⟨source, .nil source⟩

def advance {environment : Env Value Var} {source : Expr Value Var sort}
    (state : State environment source) {target : Expr Value Var sort}
    (step : Step environment state.1 target) : State environment source :=
  ⟨target, state.2.append (.single step)⟩

inductive Advance (environment : Env Value Var) (source : Expr Value Var sort) :
    State environment source → State environment source → Type u
  | paid {state : State environment source} {target : Expr Value Var sort}
      (step : Step environment state.1 target) : Advance environment source state (advance state step)

abbrev Settlement {environment : Env Value Var} {source : Expr Value Var sort}
    (state : State environment source) : Type u :=
  Σ value : Value sort, PLift (state.1 = .const value)

def law (environment : Env Value Var) (source : Expr Value Var sort) : DebtActivationLaw.{u} where
  DebtState := State environment source
  DebtId := PUnit
  DebtClaim := Expr Value Var sort
  debtId := PUnit.unit
  debtClaim := source
  budget := fun state => remaining state.1
  StepAt := Advance environment source
  step_budget_lt := by
    intro before after step
    cases step with
    | paid actual =>
        have debit := actual.remaining_eq
        simp only [advance]
        omega
  SettlementAt := Settlement
  settlement_budget_zero := by
    rintro state ⟨value, ⟨same⟩⟩
    rw [same]
    rfl
  ObstructionAt := fun _ => PEmpty

private def headAction (environment : Env Value Var) (source expression : Expr Value Var sort)
    (paidHistory : Trace environment source expression) (value : Value sort)
    (trace : Trace environment expression (.const value)) :
    Settlement (⟨expression, paidHistory⟩ : State environment source) ⊕
      GeneratedStepAt (law environment source) ⟨expression, paidHistory⟩ := by
  cases trace with
  | nil => exact .inl ⟨value, ⟨rfl⟩⟩
  | cons step tail =>
      exact .inr ⟨advance ⟨expression, paidHistory⟩ step,
        Advance.paid (environment := environment) (source := source)
          (state := ⟨expression, paidHistory⟩) step⟩

def generate (environment : Env Value Var) (source : Expr Value Var sort)
    (state : State environment source) :
    Settlement state ⊕ GeneratedStepAt (law environment source) state :=
  headAction environment source state.1 state.2 (state.1.eval environment) (execution environment state.1)

theorem completed_value {environment : Env Value Var} {source : Expr Value Var sort}
    (state : State environment source) (settled : Settlement state) :
    settled.1 = source.eval environment := by
  have sound := state.2.sound
  rw [settled.2.down] at sound
  exact sound.symm

end SourceOperationExecutionDebt
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
