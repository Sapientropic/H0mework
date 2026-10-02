import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Certificate

/-! General source-paid restructuring is installed on the existing native
whole-ledger compiler. The installer adds neither rows nor coverage selectors. -/

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

/-- The original occurrence generates its own exact classifier image. -/
def restructuringCertification {current : (JointV program registered).Current}
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (law old program registered)
      ((ledgerCompiler program registered).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact certificate old program registered current

def appendRestructuringCompiler : SourceNativeRestructuringLedgerCompiler (source program registered) where
  ledgerCompiler := ledgerCompiler program registered
  restructuringLaw := law old program registered
  certifyRestructuring := restructuringCertification old program registered

def restructuringSource : SourceNativeRestructuringLedgerSource (World registered) (JointV program registered) where
  source := source program registered
  compiler := appendRestructuringCompiler old program registered

def authoritySource : SourceNativeAuthoritySource (World registered) (JointV program registered) where
  restructuringSource := restructuringSource old program registered
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource old program registered) (by
    intro current
    constructor
    intro terminal
    exact nomatch (program.emit current.1).structural_eq.symm.trans terminal.2)
  lawSurface := .rootSemantic (World registered)
  projectionLaw := projectionLaw program registered old.source.projectionLaw

theorem compiler_preserved : (appendRestructuringCompiler old program registered).ledgerCompiler =
    ledgerCompiler program registered := rfl

theorem ledger_source_preserved : (restructuringSource old program registered).toLedgerSource =
    ledgerSource program registered := rfl

end RootGeneratedDebtActivationJointSource.Native.Restructuring
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
