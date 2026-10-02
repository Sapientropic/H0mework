import H0mework.Versions.R2.Foundation.Inquiry.ResidualCoface
import H0mework.Foundation.Inquiry.ObstructionLineage

/-!
# U7 calculus on the free residual world coface

Every existing U7 calculus extends functorially across the residual-world
coface.  Old obstructions retain their exact demands, events, rows and
dispositions.  A new residual obstruction generates its new causal row and
theory-audit receipt directly.  The construction does not decide or settle the
residual; it removes the circular requirement that an old obstruction value
must exist before obstruction-vocabulary extension can start.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedResidualAdmission

universe u

def extendU7
    {N : WorldRelationNetwork.{u}} (focus : N.Support) {Residual : Type u}
    (old : U7ProducerCalculus N) :
    U7ProducerCalculus (ExtendedNetwork N focus Residual) where
  DemandAt := by
    intro support obstruction
    cases obstruction with
    | inl obstruction => exact old.DemandAt obstruction
    | inr _ => exact PUnit
  generateDemand := by
    intro support obstruction
    cases obstruction with
    | inl obstruction => exact old.generateDemand obstruction
    | inr _ => exact PUnit.unit

def residualEntryAt
    {N : WorldRelationNetwork.{u}} {focus : N.Support} {Residual : Type u}
    {support : N.Support}
    (coordinate : Residual × ULift.{u, 0} (PLift (support = focus))) :
    OpenResponsibilityAt (ExtendedNetwork N focus Residual) support :=
  ⟨.inr coordinate.1, coordinate.2⟩

def residualExtensionReceiptAt
    {N : WorldRelationNetwork.{u}} {focus : N.Support} {Residual : Type u}
    {support : N.Support}
    (coordinate : Residual × ULift.{u, 0} (PLift (support = focus))) :
    (ExtendedNetwork N focus Residual).DispositionAt
      support .lawSurfaceExtension :=
  .inr coordinate

/-- Old row evolution is preserved literally in the residual coface. -/
def mapEntryEvolution
    {N : WorldRelationNetwork.{u}} {focus : N.Support} {Residual : Type u}
    {sourceSupport targetSupport : N.Support}
    {sourceEntry : OpenResponsibilityAt N sourceSupport}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (evolution : LedgerEntryEvolutionAt N sourceEntry targetEntry) :
    LedgerEntryEvolutionAt (ExtendedNetwork N focus Residual)
      (oldEntry sourceEntry) (oldEntry targetEntry) := by
  cases evolution with
  | carried support_eq entry_eq =>
      cases support_eq
      cases entry_eq
      exact .carried rfl HEq.rfl
  | maintained anchor_eq incidence_eq lineage_eq responsibility_eq claim_eq debit =>
      exact .maintained anchor_eq incidence_eq lineage_eq
        (congrArg Sum.inl responsibility_eq) (congrArg Sum.inl claim_eq) debit
  | transferred receipt lineage_eq claim_eq budget =>
      exact .transferred receipt lineage_eq (congrArg Sum.inl claim_eq) budget

def mapEntryTerminal
    {N : WorldRelationNetwork.{u}} {focus : N.Support} {Residual : Type u}
    {support : N.Support} {entry : OpenResponsibilityAt N support}
    (terminal : LedgerEntryTerminalAt N entry) :
    LedgerEntryTerminalAt (ExtendedNetwork N focus Residual)
      (oldEntry entry) :=
  ⟨terminal.receipt⟩

def mapObstructionDisposition
    {N : WorldRelationNetwork.{u}} {focus : N.Support} {Residual : Type u}
    {oldU7 : U7ProducerCalculus N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (disposition : U7ObstructionDispositionAt N oldU7 obstruction demand) :
    U7ObstructionDispositionAt (ExtendedNetwork N focus Residual)
      (extendU7 focus oldU7) (.inl obstruction) demand := by
  cases disposition with
  | settled receipt => exact .settled receipt
  | @redirected successor transition =>
      exact .redirected (successor := Sum.inl successor)
        { worldReceipt := transition.worldReceipt
          claim_eq := congrArg Sum.inl transition.claim_eq }
  | requiresTheoryAudit receipt => exact .requiresTheoryAudit (.inl receipt)

def extendU7Source
    {N : WorldRelationNetwork.{u}} (focus : N.Support) {Residual : Type u}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    U7ActualSuccessorSource (ExtendedNetwork N focus Residual)
      (extendU7 focus oldU7) where
  EventAt := by
    intro support obstruction demand
    cases obstruction with
    | inl obstruction =>
        exact oldCalculus.source.EventAt obstruction demand
    | inr coordinate =>
        exact SourceGeneratedU7DemandAt
          (extendU7 focus oldU7) (.inr coordinate) demand
  emit := by
    intro support obstruction
    cases obstruction with
    | inl obstruction => exact oldCalculus.source.emit obstruction
    | inr coordinate =>
        exact @SourceGeneratedU7DemandAt.canonical
          (ExtendedNetwork N focus Residual) (extendU7 focus oldU7)
          support (Sum.inr coordinate)
  demandGeneratedAt := by
    intro support obstruction demand event
    cases obstruction with
    | inl obstruction =>
        have authority := oldCalculus.source.demandGeneratedAt event
        have demand_eq := authority.payload_eq_generated
        subst demand
        exact @SourceGeneratedU7DemandAt.canonical
          (ExtendedNetwork N focus Residual) (extendU7 focus oldU7)
          support (Sum.inl obstruction)
    | inr coordinate => exact event
  demandEntryAt := by
    intro support obstruction demand event
    cases obstruction with
    | inl obstruction =>
        exact oldEntry (oldCalculus.source.demandEntryAt event)
    | inr coordinate => exact residualEntryAt coordinate

private def mapGeneratedU7
    {N : WorldRelationNetwork.{u}} (focus : N.Support) {Residual : Type u}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (event : oldCalculus.source.EventAt obstruction demand) :
    @GeneratedU7ObstructionEvolutionAt
      (ExtendedNetwork N focus Residual) (extendU7 focus oldU7)
      (extendU7Source focus oldU7 oldCalculus)
      support (Sum.inl obstruction) demand event := by
  let generated := oldCalculus.compile event
  cases generated with
  | mk disposition entryDisposition =>
      cases disposition with
      | settled receipt =>
          refine
            { disposition := .settled receipt
              demandEntryDisposition := ?_ }
          refine ⟨mapEntryTerminal entryDisposition.1, ?_⟩
          exact entryDisposition.2
      | @redirected successor transition =>
          refine
            { disposition := .redirected (successor := Sum.inl successor)
                { worldReceipt := transition.worldReceipt
                  claim_eq := congrArg Sum.inl transition.claim_eq }
              demandEntryDisposition := ?_ }
          rcases entryDisposition with ⟨evolution, property⟩
          cases evolution with
          | carried _ _ => exact False.elim property
          | maintained _ _ _ _ _ _ => exact False.elim property
          | transferred receipt lineage_eq claim_eq budget =>
              refine ⟨.transferred receipt lineage_eq
                (congrArg Sum.inl claim_eq) budget, ?_⟩
              change receipt = transition.worldReceipt
              exact property
      | requiresTheoryAudit receipt =>
          exact
            { disposition := .requiresTheoryAudit (.inl receipt)
              demandEntryDisposition := PUnit.unit }

/-- Total U7 extension.  New residual obstructions always enter the existing
theory-audit constructor with their exact generated row. -/
def extendU7Calculus
    {N : WorldRelationNetwork.{u}} (focus : N.Support) {Residual : Type u}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    U7ObstructionEvolutionCalculus (ExtendedNetwork N focus Residual)
      (extendU7 focus oldU7) where
  source := extendU7Source focus oldU7 oldCalculus
  compile := by
    intro support obstruction demand event
    cases obstruction with
    | inl obstruction =>
        exact mapGeneratedU7 focus oldU7 oldCalculus event
    | inr coordinate =>
        exact
          { disposition := .requiresTheoryAudit
              (residualExtensionReceiptAt coordinate)
            demandEntryDisposition := PUnit.unit }

theorem residual_u7_demand_entry
    {N : WorldRelationNetwork.{u}} (focus : N.Support) {Residual : Type u}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (residual : Residual) :
    U7ActualSuccessorSource.demandEntry
        ((extendU7Calculus focus oldU7 oldCalculus).source.emit
          (residualObstruction focus residual)) =
      residualEntry focus residual :=
  rfl

def residual_u7_theoryAudit
    {N : WorldRelationNetwork.{u}} (focus : N.Support) {Residual : Type u}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (residual : Residual) :
    SourceNativeU7TheoryAuditAt
      (extendU7Calculus focus oldU7 oldCalculus)
      ((extendU7Calculus focus oldU7 oldCalculus).source.emit
        (residualObstruction focus residual)) :=
  PUnit.unit

end RootGeneratedResidualAdmission
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
