import H0mework.Foundation.Responsibility.JointSource.Compiler
import H0mework.Versions.R2.Arithmetic.UnitArithmetic.Root

/-! The original unit current and the actual paid mathematical work jointly form source input. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

abbrev Current := Sigma (EventAt registered)

/-- The fixed lower compiler generates this native image for every actual unit current. -/
def native (current : Current registered) : NativeAt current.2 :=
  (compileNative? current.2).get (by rfl)

abbrev World := ExtendedNetwork CanonicalUnitArithmeticRoot.N
  (Idle.law registered.input.environment registered.input.expression)

def supportAt (current : Current registered) : (World registered).Support :=
  ⟨CanonicalUnitArithmeticRoot.source.toRootSource.account.supportOf
    (CanonicalUnitArithmeticRoot.emitted current.1), some current.2.state⟩

def vocabulary : Vocabulary where
  Current := Current registered
  Anchor := CanonicalUnitArithmeticRoot.V.Anchor
  Incidence := CanonicalUnitArithmeticRoot.V.Incidence
  Lineage := CanonicalUnitArithmeticRoot.V.Lineage
  anchorAt := fun current => CanonicalUnitArithmeticRoot.V.anchorAt current.1
  incidenceAt := fun current => CanonicalUnitArithmeticRoot.V.incidenceAt current.1
  lineageAt := fun current => CanonicalUnitArithmeticRoot.V.lineageAt current.1
  NativeWriteAt := fun current => NativeAt current.2
  RelationWriteAt := fun current => CanonicalUnitArithmeticRoot.V.RelationWriteAt current.1
  ContinuedTransportAt := fun current => CanonicalUnitArithmeticRoot.V.ContinuedTransportAt current.1
  BorromeanRedirectAt := fun current => CanonicalUnitArithmeticRoot.V.BorromeanRedirectAt current.1
  FaithfulTerminalAt := fun current => CanonicalUnitArithmeticRoot.V.FaithfulTerminalAt current.1
  nativeTarget := fun {_current} generated =>
    ⟨CanonicalUnitArithmeticRoot.V.nativeTarget generated.write, generated.nextEvent⟩
  relationTarget := fun impossible => nomatch impossible
  continuedTarget := fun impossible => nomatch impossible
  redirectTarget := fun impossible => nomatch impossible

abbrev JointV := vocabulary registered

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
