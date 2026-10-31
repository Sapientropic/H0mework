import H0mework.Foundation.Authority.EntryDisposition

/-!
# Source-generated causal-entry gate / death frontier

The existing total-disposition kernel already proves that every registered
causal entry either receives its whole-ledger successor or its exact terminal
discharge.  This module adds only a zero-field frontier tied to one root visit
and computed entry-indexed views of that authority.

It introduces no lifecycle, ledger, gate list, death enum, coverage witness or
future schedule.  In particular, substantive death requires an actual source
entry; a faithful terminal over an empty ledger cannot satisfy that Sigma.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Zero-field seal fixing one exact root and causal visit.  Occurrence,
complete source ledger and dispositions are all recomputed from those indices. -/
structure SourceGeneratedCompleteLedgerGateDeathFrontierAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root) : Type (u + 1) where
  private mk ::

def sourceGeneratedCompleteLedgerGateDeathFrontierAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root) :
    SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit :=
  ⟨⟩

namespace SourceGeneratedCompleteLedgerGateDeathFrontierAt

instance instSubsingleton
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root} :
    Subsingleton (SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit) :=
  ⟨fun left right => by cases left; cases right; rfl⟩

/-- Exact source event selected by the frontier indices. -/
def event
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (_frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit) :
    ExactTemporalCausalRootEventAt root visit :=
  root.exactTemporalCausalEventAt visit

/-- Complete source-ledger entry family at the same exact occurrence. -/
abbrev Entry
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (_frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit) :=
  OpenResponsibilityAt N
    (root.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))

/-- Canonical whole-ledger disposition read from the same exact event. -/
def entryDisposition
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit)
    (entry : frontier.Entry) : LedgerEntryDispositionAt N entry :=
  frontier.event.wholeLedgerWriteBack.entryDisposition entry

/-- Gate fibre computed from the one canonical entry disposition. -/
def GateAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit)
    (entry : frontier.Entry) : Type u :=
  match frontier.entryDisposition entry with
  | .evolved _ => PUnit
  | .terminal _ => PEmpty

/-- Death fibre computed from that same canonical entry disposition. -/
def DeathAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit)
    (entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) : Type u :=
  match frontier.entryDisposition entry with
  | .evolved _ => PEmpty
  | .terminal _ => PUnit

namespace GateAt

/-- Target row and exact evolution are recovered by eliminating the one
canonical disposition. -/
def destination
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit}
    {entry : frontier.Entry}
    (gate : frontier.GateAt entry) :
    Sigma fun targetSupport : N.Support =>
      Sigma fun targetEntry : OpenResponsibilityAt N targetSupport =>
        LedgerEntryEvolutionAt N entry targetEntry := by
  cases disposition_eq : frontier.entryDisposition entry with
  | evolved evolution => exact ⟨_, _, evolution⟩
  | terminal terminal =>
      unfold GateAt at gate
      rw [disposition_eq] at gate
      exact PEmpty.elim gate

end GateAt

namespace DeathAt

/-- Exact terminal receipt read from the same compiler image.  No receipt is
accepted by the public death mouth. -/
def receipt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit}
    {entry : frontier.Entry}
    (death : frontier.DeathAt entry) : LedgerEntryTerminalAt N entry := by
  cases disposition_eq : frontier.entryDisposition entry with
  | evolved evolution =>
      unfold DeathAt at death
      rw [disposition_eq] at death
      exact PEmpty.elim death
  | terminal terminal => exact terminal

end DeathAt

/-- Exact dichotomy for each actual source entry.  This is a theorem readout
of the existing compiler, not a stored outcome grammar. -/
theorem entry_exactlyOne
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit)
    (entry : frontier.Entry) :
    (Nonempty (frontier.GateAt entry) ∧ IsEmpty (frontier.DeathAt entry)) ∨
      (IsEmpty (frontier.GateAt entry) ∧ Nonempty (frontier.DeathAt entry)) := by
  cases disposition_eq : frontier.entryDisposition entry with
  | evolved evolution =>
      left
      constructor
      · unfold GateAt
        rw [disposition_eq]
        exact ⟨PUnit.unit⟩
      · unfold DeathAt
        rw [disposition_eq]
        infer_instance
  | terminal terminal =>
      right
      constructor
      · constructor
        intro gate
        unfold GateAt at gate
        rw [disposition_eq] at gate
        exact PEmpty.elim gate
      · unfold DeathAt
        rw [disposition_eq]
        exact ⟨PUnit.unit⟩

/-- A real death requires a real complete-ledger entry. -/
abbrev SubstantiveDeathAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit) :=
  Sigma fun entry : frontier.Entry => frontier.DeathAt entry

theorem substantiveDeath_isEmpty_of_entry_isEmpty
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (frontier : SourceGeneratedCompleteLedgerGateDeathFrontierAt root visit)
    (empty : IsEmpty frontier.Entry) :
    IsEmpty frontier.SubstantiveDeathAt :=
  ⟨fun death => empty.false death.1⟩

end SourceGeneratedCompleteLedgerGateDeathFrontierAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedCompleteLedgerGateDeathFrontierAt.entry_exactlyOne
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedCompleteLedgerGateDeathFrontierAt.substantiveDeath_isEmpty_of_entry_isEmpty
