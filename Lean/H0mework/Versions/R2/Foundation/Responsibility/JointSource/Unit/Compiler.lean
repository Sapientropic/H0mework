import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Rows

/-! The complete source-generated finite patch is the canonical whole image;
its rows consume the actual joint payer's destination receipts. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld DebtActivationLedger

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

private theorem dependentRead {A B : Type} {E : A → B → Type}
    (read : (value : A) → Sigma (E value)) {selected actual : A} (same : selected = actual) :
    (⟨(read selected).1, Eq.mp (congrArg (fun source => E source (read selected).1) same)
      (read selected).2⟩ : Sigma (E actual)) = read actual := by
  cases same
  rfl

theorem patch_destination (current : Current registered) :
    (patch registered current).toLedgerWriteEvolution.destination =
      (wholeEvolution registered current).destination := by
  funext entry
  exact dependentRead (wholeEvolution registered current).destination
    ((rowInventory registered current).forward_backward entry)

inductive RawIncidenceAt :
    {current : Current registered} →
    (occurrence : (source registered).toRootSource.actual.OccurrenceAt current) →
    (World registered).Incidence → (World registered).Incidence → Type
  | generated (current : Current registered) :
      RawIncidenceAt (emitted registered current)
        ((World registered).incidenceAt (supportAt registered current))
        ((World registered).incidenceAt (supportAt registered (targetCurrent registered current)))

def ledgerCompiler : SourceNativeLedgerCompiler (source registered) where
  IncidenceTransitionAt := RawIncidenceAt registered
  ExactTransitionAt := RawRowAt registered
  exact_incidence := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    cases event with
    | inventory index => exact .generated current
  exact_lineage := fun event => ((rowSource registered).compileEvolution event).toDebtLineage.lineage_eq
  writeRowSource := rowSource registered
  terminalRowSource := LedgerTerminalRowSourceAt.empty (source registered)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact .nativeWrite (native registered current) rfl (targetEvent registered current)
      ((patch registered current).toLedgerWriteEvolution)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨patch registered current, rfl⟩

def ledgerSource : SourceNativeLedgerSource (World registered) (JointV registered) where
  source := source registered
  ledgerCompiler := ledgerCompiler registered

theorem compile_emitted (current : Current registered) :
    (ledgerCompiler registered).compile (emitted registered current) =
      .nativeWrite (native registered current) rfl (targetEvent registered current)
        ((patch registered current).toLedgerWriteEvolution) := rfl

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
