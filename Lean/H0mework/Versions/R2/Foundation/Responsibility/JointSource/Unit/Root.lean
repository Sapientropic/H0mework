import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

def ledgerRoot : SourceNativeLedgerRootClosure (World registered) (JointV registered) where
  source := ledgerSource registered
  emitted := emitted registered
  compiler_commutes := by
    intro current
    rfl

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
