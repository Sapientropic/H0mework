import H0mework.Foundation.Responsibility.JointSource.Source

/-! Exact debit and local completion are read from the already generated source action. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource

open SourceOperationEffects SourceOperationExecution DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable {registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin}

theorem mathTarget_budget {current : V.Current}
    (event : EventAt registered current) :
    remaining (mathTarget event).1 = remaining event.state.1 - 1 := by
  unfold mathTarget
  cases actionEq : mathAction event with
  | inl settled =>
      have zero := (law registered).settlement_budget_zero settled
      change remaining event.state.1 = 0 at zero
      simp only [zero, Nat.zero_sub]
  | inr paid =>
      rcases paid with ⟨next, advance⟩
      cases advance with
      | paid step =>
          have debit := step.remaining_eq
          dsimp only [SourceOperationExecutionDebt.advance]
          omega

def localSettlement {current : V.Current}
    (event : EventAt registered current) (zero : remaining event.state.1 = 0) :
    SourceOperationExecutionDebt.Settlement event.state := by
  cases shape : event.state.1 with
  | const value => exact ⟨value, ⟨shape⟩⟩
  | var name => simp only [shape, remaining] at zero; omega
  | add left right => simp only [shape, remaining] at zero; omega
  | linear operation value => simp only [shape, remaining] at zero; omega
  | bilinear operation left right => simp only [shape, remaining] at zero; omega

theorem mathTarget_eq_of_zero {current : V.Current}
    (event : EventAt registered current) (zero : remaining event.state.1 = 0) :
    mathTarget event = event.state := by
  unfold mathTarget
  cases actionEq : mathAction event with
  | inl settled => rfl
  | inr paid =>
      have strict := (law registered).step_budget_lt paid.2
      change remaining paid.1.1 < remaining event.state.1 at strict
      rw [zero] at strict
      exact False.elim (Nat.not_lt_zero _ strict)

end RootGeneratedDebtActivationJointSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
