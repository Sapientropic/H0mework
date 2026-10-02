import H0mework.Foundation.Responsibility.JointSource.Source
import H0mework.Foundation.Responsibility.JointSource.Idle
import H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel

/-! The registered actual mathematical action pays the joint ledger, retaining the original native successor. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource

open SourceOperationEffects DebtActivationWorld DebtActivationLedger

variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin current : V.Current}
  {registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin}
  {event : EventAt registered current}

def PaymentAt (native : NativeAt event) : Type u :=
  match mathAction event with
  | .inl settled =>
      LedgerWriteEvolutionAt (ExtendedNetwork N (Idle.law registered.input.environment registered.input.expression))
        (activeLedger (lower.source.source.toRootSource.account.supportOf (lower.emitted current)) event.state)
        (activeLedger (lower.source.source.toRootSource.account.supportOf native.targetOccurrence) event.state) ×
      PLift (settled.1 = registered.input.expression.eval registered.input.environment)
  | .inr paid => LedgerWriteEvolutionAt
      (ExtendedNetwork N (Idle.law registered.input.environment registered.input.expression))
      (activeLedger (lower.source.source.toRootSource.account.supportOf (lower.emitted current)) event.state)
      (activeLedger (lower.source.source.toRootSource.account.supportOf native.targetOccurrence) paid.1)

def payment (native : NativeAt event) : PaymentAt native := by
  unfold PaymentAt
  cases mathEq : mathAction event with
  | inl settled => exact ⟨Idle.wholeEvolution native.baseLedger event.owner event.state settled,
      ⟨local_completed_value event settled⟩⟩
  | inr paid => exact jointStepLedgerEvolution native.baseLedger event.owner paid.2

theorem original_next (native : NativeAt event) :
    (lower.source.source.toRootSource.actual.compile (lower.emitted current)).nextCurrent? =
      some (V.nativeTarget native.write) := by
  rw [native.structural_eq]
  rfl

end RootGeneratedDebtActivationJointSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
