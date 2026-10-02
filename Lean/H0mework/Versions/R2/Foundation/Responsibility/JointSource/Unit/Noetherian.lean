import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Completion
import H0mework.Versions.R2.Foundation.Responsibility.NoetherianClosure

/-! The canonical math row supplies an exact same-debt payment to the existing Noetherian consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

def mathOrigin := sourceRow registered ⟨origin, initialEvent registered⟩ 1

def mathCurrent (runtime : Runtime registered) :
    SourceNativeRootDebtCurrentAt (process registered) (mathOrigin registered) where
  state := runtime.state
  entry := sourceRow registered (runtimeCurrent registered runtime) 1
  sameDebt := ⟨rfl, rfl⟩

private theorem mathTarget_unique (runtime : Runtime registered)
    (entry : (process registered |>.stateAt ((process registered).successor runtime.state)).Entry)
    (same : RootDebtLineageAt (World registered) (mathCurrent registered runtime).entry entry) :
    entry = sourceRow registered (runtimeCurrent registered runtime.tick.next) 1 := by
  rcases entry with ⟨responsibility, opened⟩
  cases responsibility with
  | inl old => exact nomatch same.claim_eq
  | inr debt =>
      cases debt
      rcases opened with ⟨⟨opened⟩⟩
      rfl

private theorem destination_math (runtime : Runtime registered) :
    ((patch registered (runtimeCurrent registered runtime)).toLedgerWriteEvolution.destination
      (sourceRow registered (runtimeCurrent registered runtime) 1)).1 =
      sourceRow registered (runtimeCurrent registered runtime.tick.next) 1 := by
  change targetRow registered (runtimeCurrent registered runtime)
      ((rowInventory registered (runtimeCurrent registered runtime)).backward
        ((rowInventory registered (runtimeCurrent registered runtime)).forward 1)) = _
  rw [(rowInventory registered (runtimeCurrent registered runtime)).backward_forward]
  exact targetRow_inventory registered (runtimeCurrent registered runtime) 1

def mathStep (runtime : Runtime registered) : SourceNativeRootDebtStepAt (mathCurrent registered runtime) where
  targetEntry := ((patch registered (runtimeCurrent registered runtime)).toLedgerWriteEvolution.destination
    (sourceRow registered (runtimeCurrent registered runtime) 1)).1
  evolution := ((patch registered (runtimeCurrent registered runtime)).toLedgerWriteEvolution.destination
    (sourceRow registered (runtimeCurrent registered runtime) 1)).2
  sameDebtTarget_unique := fun entry same =>
    (mathTarget_unique registered runtime entry same).trans (destination_math registered runtime).symm

theorem mathCurrent_budget (runtime : Runtime registered) :
    (mathCurrent registered runtime).budget = runtimeBudget registered runtime := rfl

def mathPayment (runtime : Runtime registered) (positive : 0 < runtimeBudget registered runtime) :
    SourceNativeRootDebtPaymentStepAt (mathCurrent registered runtime) where
  step := mathStep registered runtime
  strictDebit := by
    change ((mathStep registered runtime).targetEntry).progressBudget <
      (mathCurrent registered runtime).entry.progressBudget
    change (((patch registered (runtimeCurrent registered runtime)).toLedgerWriteEvolution.destination
      (sourceRow registered (runtimeCurrent registered runtime) 1)).1).progressBudget < _
    rw [destination_math]
    change runtimeBudget registered runtime.tick.next < runtimeBudget registered runtime
    rw [runtimeBudget_tick]
    omega

def mathContinuation (runtime : Runtime registered) (positive : 0 < runtimeBudget registered runtime) :
    SourceNativePaidRootDebtMacroContinuationAt (mathCurrent registered runtime) :=
  .ofPayment .refl (mathPayment registered runtime positive) .refl

theorem mathPaidContinuation_wellFounded :
    WellFounded (SourceNativePaidRootDebtContinuationRel
      (process := process registered) (origin := mathOrigin registered)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
