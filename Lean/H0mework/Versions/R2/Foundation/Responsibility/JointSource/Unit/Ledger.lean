import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Event

/-! The installed source event's whole image is the already generated joint payer at its actual target. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld DebtActivationLedger

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

private def consumePayment {N : WorldRelationNetwork} {V : Vocabulary}
    {lower : SourceNativeLedgerRootClosure N V} {origin current : V.Current}
    {registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin}
    {event : EventAt registered current} (generated : NativeAt event) :
    LedgerWriteEvolutionAt (ExtendedNetwork N (Idle.law registered.input.environment registered.input.expression))
      (activeLedger (lower.source.source.toRootSource.account.supportOf (lower.emitted current)) event.state)
      (activeLedger (lower.source.source.toRootSource.account.supportOf generated.targetOccurrence) (mathTarget event)) := by
  cases mathEq : mathAction event with
  | inl settled =>
      have paid := payment generated
      simp only [PaymentAt, mathEq] at paid
      simpa only [mathTarget, mathEq] using paid.1
  | inr actual =>
      have paid := payment generated
      simp only [PaymentAt, mathEq] at paid
      simpa only [mathTarget, mathEq] using paid

private def atTarget {W : WorldRelationNetwork} {initial target actual : W.Support}
    (same : target = actual) (rows : LedgerWriteEvolutionAt W ⟨initial⟩ ⟨target⟩) :
    LedgerWriteEvolutionAt W ⟨initial⟩ ⟨actual⟩ := same ▸ rows

def wholeEvolution (current : Current registered) :
    LedgerWriteEvolutionAt (World registered) ⟨supportAt registered current⟩
      ⟨supportAt registered ((JointV registered).nativeTarget (native registered current))⟩ := by
  let generated := native registered current
  have targetEq :
      (CanonicalUnitArithmeticRoot.source.toRootSource.account.supportOf generated.targetOccurrence,
        some (mathTarget current.2)) =
      supportAt registered ((JointV registered).nativeTarget generated) :=
    Prod.ext (congrArg (CanonicalUnitArithmeticRoot.source.toRootSource.account.supportOf)
      generated.target_emitted) (congrArg some generated.next_state.symm)
  exact atTarget targetEq (consumePayment generated)

def ledgerImage (current : Current registered) :
    SourceNativeLedgerEvolutionAt (source registered) (emitted registered current) :=
  .nativeWrite (native registered current) rfl (targetEvent registered current) (wholeEvolution registered current)

def compileLedger {current : Current registered}
    (occurrence : (source registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt (source registered) occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact ledgerImage registered current

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
