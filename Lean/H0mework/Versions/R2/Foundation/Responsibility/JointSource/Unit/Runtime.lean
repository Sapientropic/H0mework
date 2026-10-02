import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Authority
import H0mework.Versions.R2.Foundation.Runtime.Activation

/-! The existing sealed runtime consumes the source's actual complete patch and joint next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

def finiteVisit : Nat → RootVisit (ledgerRoot registered).toRoot
  | 0 => (ledgerRoot registered).toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) : SourceNativeTemporalVisitAt (ledgerRoot registered) :=
  .finite (finiteVisit registered depth)

private def temporalDepth? (current : SourceNativeLivingRootCurrentAt (World registered)) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

private theorem temporalVisit_depth (depth : Nat) :
    temporalDepth? registered ⟨JointV registered, livingRoot registered, temporalVisit registered depth⟩ =
      some depth := by
  induction depth with
  | zero => rfl
  | succ depth prior =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (finiteVisit registered depth).history + 1) = some (depth + 1)
      have old : ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit registered depth).history = depth := Option.some.inj prior
      rw [old]

def process : SourceNativeLivingRootProcess (World registered) where
  State := Nat
  stateAt := fun depth => ⟨JointV registered, livingRoot registered, temporalVisit registered depth⟩
  stateAt_injective := by
    intro left right same
    have depthEq := congrArg (temporalDepth? registered) same
    rw [temporalVisit_depth registered left, temporalVisit_depth registered right] at depthEq
    exact Option.some.inj depthEq
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

abbrev Runtime := LivingRuntimeState (process registered)

def initialRuntime : Runtime registered := LivingRuntimeState.initial (process registered)

def runtimeCurrent (runtime : Runtime registered) : Current registered :=
  (finiteVisit registered runtime.state).current

theorem runtime_tick_ledger (runtime : Runtime registered) :
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((ledgerCompiler registered).compile (emitted registered (runtimeCurrent registered runtime))) :=
  HEq.rfl

theorem runtime_tick_patch (runtime : Runtime registered) :
    HEq runtime.tick.generated.currentPatch
      ((ledgerCompiler registered).compilePatch (emitted registered (runtimeCurrent registered runtime))) :=
  HEq.rfl

@[simp] theorem initialRuntime_current :
    runtimeCurrent registered (initialRuntime registered) = ⟨origin, initialEvent registered⟩ := rfl

theorem runtime_tick_next (runtime : Runtime registered) :
    runtimeCurrent registered runtime.tick.next =
      (JointV registered).nativeTarget (native registered (runtimeCurrent registered runtime)) := rfl

theorem runtime_tick_math (runtime : Runtime registered) :
    (runtimeCurrent registered runtime.tick.next).2.state =
      mathTarget (runtimeCurrent registered runtime).2 :=
  (native registered (runtimeCurrent registered runtime)).next_state

theorem runtime_tick_original (runtime : Runtime registered) :
    (runtimeCurrent registered runtime.tick.next).1 =
      CanonicalUnitArithmeticRoot.next (runtimeCurrent registered runtime).1 := rfl

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
