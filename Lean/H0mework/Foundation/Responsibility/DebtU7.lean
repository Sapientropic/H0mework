import Mathlib.Logic.IsEmpty.Defs
import H0mework.Foundation.Responsibility.DebtWorldReadback
import H0mework.Foundation.Inquiry.ObstructionLineage

/-!
# U7 calculus for a debt-activation world

An existing U7 calculus extends functorially across `DebtActivationWorld`.
Old obstructions retain their exact demands, events, ledger rows, and
dispositions.  An active debt obstruction generates a unit demand carried by
the law-owned debt row and enters theory audit through its exact obstruction
receipt.  The inactive face cannot emit a debt event.

This file installs no root, emitter, future process, or U8 revision.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedDebtActivationU7

open DebtActivationWorld

universe u

def extendU7
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (old : U7ProducerCalculus N) :
    U7ProducerCalculus (ExtendedNetwork N law) where
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

def mapOldEntryEvolution
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    {sourceSupport targetSupport : N.Support}
    {state? : Option law.DebtState}
    {source : OpenResponsibilityAt N sourceSupport}
    {target : OpenResponsibilityAt N targetSupport}
    (evolution : LedgerEntryEvolutionAt N source target) :
    LedgerEntryEvolutionAt (ExtendedNetwork N law)
      (oldEntry (law := law) (state? := state?) source)
      (oldEntry (law := law) (state? := state?) target) := by
  cases evolution with
  | carried support_eq entry_eq =>
      cases support_eq
      cases entry_eq
      exact .carried rfl HEq.rfl
  | maintained anchor_eq incidence_eq lineage_eq responsibility_eq claim_eq debit =>
      exact .maintained anchor_eq incidence_eq lineage_eq
        (congrArg Sum.inl responsibility_eq) (congrArg Sum.inl claim_eq) debit
  | transferred receipt lineage_eq claim_eq budget =>
      exact .transferred (.inl receipt) lineage_eq
        (congrArg Sum.inl claim_eq) budget

def mapOldEntryTerminal
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    {support : N.Support} {state? : Option law.DebtState}
    {entry : OpenResponsibilityAt N support}
    (terminal : LedgerEntryTerminalAt N entry) :
    LedgerEntryTerminalAt (ExtendedNetwork N law)
      (oldEntry (law := law) (state? := state?) entry) :=
  ⟨baseSettlementReceipt (law := law) support terminal.receipt⟩

def mapOldObstructionDisposition
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    {oldU7 : U7ProducerCalculus N}
    {support : N.Support} {state? : Option law.DebtState}
    {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (disposition : U7ObstructionDispositionAt N oldU7 obstruction demand) :
    U7ObstructionDispositionAt (ExtendedNetwork N law) (extendU7 oldU7)
      (show (ExtendedNetwork N law).ObstructionAt ⟨support, state?⟩ from
        .inl obstruction) demand := by
  cases disposition with
  | settled receipt =>
      exact .settled (baseSettlementReceipt (law := law) support receipt)
  | @redirected successor transition =>
      exact .redirected (successor := Sum.inl successor)
        { worldReceipt := .inl transition.worldReceipt
          claim_eq := congrArg Sum.inl transition.claim_eq }
  | requiresTheoryAudit receipt =>
      exact .requiresTheoryAudit (.inl receipt)

def extendU7Source
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    U7ActualSuccessorSource (ExtendedNetwork N law) (extendU7 oldU7) where
  EventAt := by
    intro support obstruction demand
    cases obstruction with
    | inl obstruction =>
        exact oldCalculus.source.EventAt obstruction demand
    | inr active =>
        exact SourceGeneratedU7DemandAt (extendU7 oldU7) (.inr active) demand
  emit := by
    intro support obstruction
    cases obstruction with
    | inl obstruction => exact oldCalculus.source.emit obstruction
    | inr active =>
        exact @SourceGeneratedU7DemandAt.canonical
          (ExtendedNetwork N law) (extendU7 oldU7) support (.inr active)
  demandGeneratedAt := by
    intro support obstruction demand event
    cases obstruction with
    | inl obstruction =>
        have authority := oldCalculus.source.demandGeneratedAt event
        have demand_eq := authority.payload_eq_generated
        subst demand
        exact @SourceGeneratedU7DemandAt.canonical
          (ExtendedNetwork N law) (extendU7 oldU7) support (.inl obstruction)
    | inr _ => exact event
  demandEntryAt := by
    intro support obstruction demand event
    rcases support with ⟨support, state?⟩
    cases obstruction with
    | inl obstruction =>
        exact oldEntry (state? := state?)
          (oldCalculus.source.demandEntryAt event)
    | inr active =>
        cases state? with
        | none => exact nomatch active
        | some state => exact debtEntry (N := N) support state

def oldEvent
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {support : N.Support} {state? : Option law.DebtState}
    {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (event : oldCalculus.source.EventAt obstruction demand) :
    (extendU7Source (law := law) oldU7 oldCalculus).EventAt
      (show (ExtendedNetwork N law).ObstructionAt ⟨support, state?⟩ from
        .inl obstruction) demand :=
  event

private def mapOldGenerated
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    {support : N.Support} {state? : Option law.DebtState}
    {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (event : oldCalculus.source.EventAt obstruction demand) :
    @GeneratedU7ObstructionEvolutionAt
      (ExtendedNetwork N law) (extendU7 oldU7)
      (extendU7Source oldU7 oldCalculus)
      ⟨support, state?⟩ (.inl obstruction) demand (oldEvent event) := by
  let generated := oldCalculus.compile event
  rcases generated with ⟨disposition, entryDisposition⟩
  cases disposition with
  | settled receipt =>
      refine
        { disposition := .settled
            (baseSettlementReceipt (law := law) support receipt)
          demandEntryDisposition := ?_ }
      refine ⟨mapOldEntryTerminal (law := law) entryDisposition.1, ?_⟩
      exact congrArg (baseSettlementReceipt (law := law) support)
        entryDisposition.2
  | @redirected successor transition =>
      refine
        { disposition := .redirected (successor := Sum.inl successor)
            { worldReceipt := .inl transition.worldReceipt
              claim_eq := congrArg Sum.inl transition.claim_eq }
          demandEntryDisposition := ?_ }
      rcases entryDisposition with ⟨evolution, property⟩
      cases evolution with
      | carried _ _ => exact False.elim property
      | maintained _ _ _ _ _ _ => exact False.elim property
      | transferred receipt lineage_eq claim_eq budget =>
          refine ⟨.transferred (.inl receipt) lineage_eq
            (congrArg Sum.inl claim_eq) budget, ?_⟩
          exact congrArg Sum.inl property
  | requiresTheoryAudit receipt =>
      exact
        { disposition := .requiresTheoryAudit (.inl receipt)
          demandEntryDisposition := PUnit.unit }

def extendU7Calculus
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7) :
    U7ObstructionEvolutionCalculus (ExtendedNetwork N law)
      (extendU7 oldU7) where
  source := extendU7Source oldU7 oldCalculus
  compile := by
    intro support obstruction demand event
    rcases support with ⟨support, state?⟩
    cases obstruction with
    | inl obstruction =>
        exact mapOldGenerated oldU7 oldCalculus event
    | inr active =>
        cases state? with
        | none => exact nomatch active
        | some state =>
            exact
              { disposition := .requiresTheoryAudit
                  (debtObstructionReceipt (N := N) support active)
                demandEntryDisposition := PUnit.unit }

theorem old_demand_entry
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {support : N.Support} {state? : Option law.DebtState}
    {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (event : oldCalculus.source.EventAt obstruction demand) :
    U7ActualSuccessorSource.demandEntry
        (oldEvent (law := law) (state? := state?) event) =
      oldEntry (law := law) (state? := state?)
        (U7ActualSuccessorSource.demandEntry event) :=
  rfl

theorem old_compiled_disposition
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    {oldU7 : U7ProducerCalculus N}
    {oldCalculus : U7ObstructionEvolutionCalculus N oldU7}
    {support : N.Support} {state? : Option law.DebtState}
    {obstruction : N.ObstructionAt support}
    {demand : oldU7.DemandAt obstruction}
    (event : oldCalculus.source.EventAt obstruction demand) :
    ((extendU7Calculus (law := law) oldU7 oldCalculus).compile
      (oldEvent (law := law) (state? := state?) event)).disposition =
      mapOldObstructionDisposition (law := law) (state? := state?)
        (oldCalculus.compile event).disposition := by
  change
    (mapOldGenerated (law := law) (state? := state?) oldU7 oldCalculus
      event).disposition =
      mapOldObstructionDisposition (law := law) (state? := state?)
        (oldCalculus.compile event).disposition
  unfold mapOldGenerated mapOldObstructionDisposition
  generalize generated_eq : oldCalculus.compile event = generated
  rcases generated with ⟨disposition, entryDisposition⟩
  cases disposition <;> rfl

theorem debt_generateDemand
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    (extendU7 oldU7).generateDemand
        (debtObstruction (N := N) support obstruction) = PUnit.unit :=
  rfl

theorem debt_demand_entry
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    U7ActualSuccessorSource.demandEntry
        ((extendU7Calculus oldU7 oldCalculus).source.emit
          (debtObstruction (N := N) support obstruction)) =
      debtEntry (N := N) support state :=
  rfl

theorem debt_compiled_disposition
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    ((extendU7Calculus oldU7 oldCalculus).compile
      ((extendU7Calculus oldU7 oldCalculus).source.emit
        (debtObstruction (N := N) support obstruction))).disposition =
      .requiresTheoryAudit
        (debtObstructionReceipt (N := N) support obstruction) :=
  rfl

def debt_theoryAudit
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (support : N.Support) {state : law.DebtState}
    (obstruction : law.ObstructionAt state) :
    SourceNativeU7TheoryAuditAt (extendU7Calculus oldU7 oldCalculus)
      ((extendU7Calculus oldU7 oldCalculus).source.emit
        (debtObstruction (N := N) support obstruction)) :=
  PUnit.unit

theorem inactive_has_no_debt_event
    {N : WorldRelationNetwork.{u}} {law : DebtActivationLaw.{u}}
    (oldU7 : U7ProducerCalculus N)
    (oldCalculus : U7ObstructionEvolutionCalculus N oldU7)
    (support : N.Support) :
    IsEmpty
      (Sigma fun obstruction : ActiveAt law none law.ObstructionAt =>
        (extendU7Calculus oldU7 oldCalculus).source.EventAt
          (show (ExtendedNetwork N law).ObstructionAt ⟨support, none⟩ from
            .inr obstruction)
          ((extendU7 oldU7).generateDemand
            (show (ExtendedNetwork N law).ObstructionAt ⟨support, none⟩ from
              .inr obstruction))) := by
  constructor
  rintro ⟨obstruction, _event⟩
  exact nomatch obstruction

end RootGeneratedDebtActivationU7
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
