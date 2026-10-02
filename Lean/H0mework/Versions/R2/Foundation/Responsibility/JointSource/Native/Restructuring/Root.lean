import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Consumer
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

/-! The same emitted source and complete native compiler install the general
restructuring authority. Root closure consumes the existing commuting proof. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring
open SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (program : Program old.toLedgerRoot) {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)

def authoritativeRoot : SourceNativeAuthoritativeRootClosure (World registered) (JointV program registered) where
  source := authoritySource old program registered
  emitted := emitted program registered
  compiler_commutes := (ledgerRoot program registered).compiler_commutes

def livingRoot : SourceNativeLivingRootClosure (World registered) (JointV program registered) :=
  (authoritativeRoot old program registered).toLivingWithoutFaithfulTerminal (by
    intro current
    constructor
    intro terminal
    exact nomatch (program.emit current.1).structural_eq.symm.trans terminal.2)

theorem root_ledger_preserved : (authoritativeRoot old program registered).toLedgerRoot =
    ledgerRoot program registered := rfl

theorem living_ledger_preserved : (livingRoot old program registered).toAuthoritativeRoot.toLedgerRoot =
    ledgerRoot program registered := rfl

end RootGeneratedDebtActivationJointSource.Native.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
