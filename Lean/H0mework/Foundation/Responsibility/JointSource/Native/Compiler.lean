import H0mework.Foundation.Responsibility.JointSource.Native.Rows

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {lower : SourceNativeLedgerRootClosure N V} {origin : V.Current}
variable (program : Program lower)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) lower origin)

inductive RawIncidenceAt :
    {current : Current registered} →
    (occurrence : (source program registered).toRootSource.actual.OccurrenceAt current) →
    (World registered).Incidence → (World registered).Incidence → Type u
  | generated (current : Current registered) :
      RawIncidenceAt (emitted program registered current)
        ((World registered).incidenceAt (supportAt registered current))
        ((World registered).incidenceAt (supportAt registered (targetCurrent program registered current)))

def ledgerCompiler : SourceNativeLedgerCompiler (source program registered) where
  IncidenceTransitionAt := RawIncidenceAt program registered
  ExactTransitionAt := RawRowAt program registered
  exact_incidence := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    cases event
    exact .generated current
  exact_lineage := fun event => ((rowSource program registered).compileEvolution event).toDebtLineage.lineage_eq
  writeRowSource := rowSource program registered
  terminalRowSource := LedgerTerminalRowSourceAt.empty (source program registered)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact .nativeWrite (native program registered current) rfl (targetEvent program registered current)
      ((patch program registered current).toLedgerWriteEvolution)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨patch program registered current, rfl⟩

def ledgerSource : SourceNativeLedgerSource (World registered) (JointV program registered) where
  source := source program registered
  ledgerCompiler := ledgerCompiler program registered

theorem compile_emitted (current : Current registered) :
    (ledgerCompiler program registered).compile (emitted program registered current) =
      .nativeWrite (native program registered current) rfl (targetEvent program registered current)
        ((patch program registered current).toLedgerWriteEvolution) := rfl

theorem rows_size (current : Current registered) :
    (rows program registered current).size = (program.emit current.1).rows.size + 1 :=
  congrArg (fun size => size + 1) (oldRows_size program registered current)

def ledgerRoot : SourceNativeLedgerRootClosure (World registered) (JointV program registered) where
  source := ledgerSource program registered
  emitted := emitted program registered
  compiler_commutes := by
    intro current
    rfl

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
