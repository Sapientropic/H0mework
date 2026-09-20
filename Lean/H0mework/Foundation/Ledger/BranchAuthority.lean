import H0mework.Foundation.Ledger.PatchReadback

/-!
# Branch-level generated ledger authority

Packages continuing and terminal patches against one structural compiler result.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Generated patch corresponding to one structural compiler result.

The equality retained in each branch is only the static compatibility theorem
that folding its generated events reproduces the legacy total readout.  The
historical name remains for import compatibility. -/
def SourceNativeFiniteLedgerPatchAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u)
    (writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    (terminalRowSource : LedgerTerminalRowSourceAt source)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) : Type u :=
  match generated with
  | .nativeWrite _ _ targetOccurrence ledgerEvolution =>
      { patch : FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩
          //
        patch.toLedgerWriteEvolution = ledgerEvolution }
  | .relationWrite _ _ targetOccurrence ledgerEvolution =>
      { patch : FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩
          //
        patch.toLedgerWriteEvolution = ledgerEvolution }
  | .continuedTransport _ _ targetOccurrence ledgerEvolution =>
      { patch : FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩
          //
        patch.toLedgerWriteEvolution = ledgerEvolution }
  | .borromeanRedirect _ _ targetOccurrence ledgerEvolution =>
      { patch : FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩
          //
        patch.toLedgerWriteEvolution = ledgerEvolution }
  | .faithfulTerminal _ _ ledgerEvolution =>
      { patch : SourceGeneratedLedgerTerminalPatchAt terminalRowSource occurrence //
        patch.toLedgerTerminalEvolution = ledgerEvolution }
/-- Exact generated-entry readout carried by one branch-specific patch.

Continuing branches expose only the row selected by the same coverage map
that generated the folded world destination.  Stored but omitted rows are
inventory data, not a generated row.  The terminal readout remains total because its
patch carries an exact row for every live source entry. -/
def SourceNativeFiniteLedgerPatchGeneratedEntryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u)
    (writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    (terminalRowSource : LedgerTerminalRowSourceAt source)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type :=
  match generated with
  | .nativeWrite _ _ _ _ => patch.1.CanonicalGeneratedSourceRowAt entry
  | .relationWrite _ _ _ _ => patch.1.CanonicalGeneratedSourceRowAt entry
  | .continuedTransport _ _ _ _ => patch.1.CanonicalGeneratedSourceRowAt entry
  | .borromeanRedirect _ _ _ _ => patch.1.CanonicalGeneratedSourceRowAt entry
  | .faithfulTerminal _ _ _ => patch.1.CanonicalGeneratedEntryAt entry

/-- Canonical generated-entry producer for one branch-specific patch.

Continuing branches consult the fold's destination selector; terminal branches
consult the patch's total discharge index. -/
def sourceNativeFiniteLedgerPatchGeneratedEntry?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u)
    (writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    (terminalRowSource : LedgerTerminalRowSourceAt source)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) :
    Option (SourceNativeFiniteLedgerPatchGeneratedEntryAt source
      ExactTransitionAt writeRowSource terminalRowSource generated patch entry) :=
  match generated with
  | .nativeWrite _ _ _ _ => patch.1.canonicalGeneratedSourceRow? entry
  | .relationWrite _ _ _ _ => patch.1.canonicalGeneratedSourceRow? entry
  | .continuedTransport _ _ _ _ => patch.1.canonicalGeneratedSourceRow? entry
  | .borromeanRedirect _ _ _ _ => patch.1.canonicalGeneratedSourceRow? entry
  | .faithfulTerminal _ _ _ =>
      some (patch.1.canonicalGeneratedEntryAt entry)

/-- Exact generated-row membership is recognized by the same branch-specific
query used by the source ledger compiler. -/
theorem sourceNativeFiniteLedgerPatchGeneratedEntry?_isSome
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {terminalRowSource : LedgerTerminalRowSourceAt source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (row : SourceNativeFiniteLedgerPatchGeneratedEntryAt source
      ExactTransitionAt writeRowSource terminalRowSource generated patch entry) :
    (sourceNativeFiniteLedgerPatchGeneratedEntry? source ExactTransitionAt
      writeRowSource terminalRowSource generated patch entry).isSome = true := by
  cases generated with
  | nativeWrite => exact patch.1.canonicalGeneratedSourceRow?_isSome entry row
  | relationWrite => exact patch.1.canonicalGeneratedSourceRow?_isSome entry row
  | continuedTransport =>
      exact patch.1.canonicalGeneratedSourceRow?_isSome entry row
  | borromeanRedirect =>
      exact patch.1.canonicalGeneratedSourceRow?_isSome entry row
  | faithfulTerminal => rfl

/-- Whole-ledger semantic effect strong enough to require an exact canonical
entry row.

Terminal discharge is total by construction.  In every continuing branch the
effect is an actual transfer in the ledger evolution generated by the same
source occurrence.  This contract mentions neither a row nor an index. -/
def SourceNativeLedgerTerminalOrTransferredAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Prop :=
  match generated with
  | .faithfulTerminal _ _ _ => True
  | .nativeWrite _ _ _ ledgerEvolution
  | .relationWrite _ _ _ ledgerEvolution
  | .continuedTransport _ _ _ ledgerEvolution
  | .borromeanRedirect _ _ _ ledgerEvolution =>
      FiniteGeneratedLedgerWritePatchAt.ledgerEntryIsTransferred
        (ledgerEvolution.destination entry).2 = true

/-- Terminal or genuinely transferred demand semantics force a canonical patch
row for the exact entry.  The proof derives it from the existing
coverage fold; it does not accept membership, an index, or causal authority
from a downstream caller. -/
def sourceNativeFiniteLedgerPatchGeneratedEntry_of_terminalOrTransferred
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {terminalRowSource : LedgerTerminalRowSourceAt source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (effect : SourceNativeLedgerTerminalOrTransferredAt generated entry) :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt source ExactTransitionAt
      writeRowSource terminalRowSource generated patch entry := by
  cases generated with
  | faithfulTerminal terminal structural_eq ledgerEvolution =>
      exact patch.1.canonicalGeneratedEntryAt entry
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      apply patch.1.canonicalGeneratedSourceRow_of_transferred entry
      rw [patch.2]
      exact effect
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      apply patch.1.canonicalGeneratedSourceRow_of_transferred entry
      rw [patch.2]
      exact effect
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      apply patch.1.canonicalGeneratedSourceRow_of_transferred entry
      rw [patch.2]
      exact effect
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      apply patch.1.canonicalGeneratedSourceRow_of_transferred entry
      rw [patch.2]
      exact effect

/-- Whole-ledger meaning of one exact generated-entry token.

For every continuing branch the selected generated row must be exactly the
target and evolution used by the source compiler's folded world ledger.
The terminal branch has no successor row and therefore satisfies this readout
trivially. -/
def SourceNativeFiniteLedgerPatchGeneratedEntryAt.CommutesWithWorld
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {terminalRowSource : LedgerTerminalRowSourceAt source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    {patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (authority : SourceNativeFiniteLedgerPatchGeneratedEntryAt source
      ExactTransitionAt writeRowSource terminalRowSource generated patch entry) :
    Prop :=
  match generated with
  | .nativeWrite _ _ _ ledgerEvolution =>
      authority.targetEntry = (ledgerEvolution.destination entry).1 ∧
        HEq authority.row.evolution (ledgerEvolution.destination entry).2
  | .relationWrite _ _ _ ledgerEvolution =>
      authority.targetEntry = (ledgerEvolution.destination entry).1 ∧
        HEq authority.row.evolution (ledgerEvolution.destination entry).2
  | .continuedTransport _ _ _ ledgerEvolution =>
      authority.targetEntry = (ledgerEvolution.destination entry).1 ∧
        HEq authority.row.evolution (ledgerEvolution.destination entry).2
  | .borromeanRedirect _ _ _ ledgerEvolution =>
      authority.targetEntry = (ledgerEvolution.destination entry).1 ∧
        HEq authority.row.evolution (ledgerEvolution.destination entry).2
  | .faithfulTerminal _ _ ledgerEvolution =>
      authority.terminal = ledgerEvolution.discharge entry

/-- Equality of whole-ledger evolutions preserves the dependent evolution
stored at each exact destination incidence. -/
theorem LedgerWriteEvolutionAt.destination_evolution_heq
    {N : WorldRelationNetwork.{u}}
    {source target : CompleteLiveLedgerAt N}
    {left right : LedgerWriteEvolutionAt N source target}
    (evolution_eq : left = right)
    (entry : source.Entry) :
    HEq (left.destination entry).2 (right.destination entry).2 := by
  cases evolution_eq
  rfl

/-- Every token emitted by the canonical generated-entry producer commutes
with the exact source compiler world evolution. -/
theorem SourceNativeFiniteLedgerPatchGeneratedEntryAt.commutes_with_world
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {terminalRowSource : LedgerTerminalRowSourceAt source}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    {patch : SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
      writeRowSource terminalRowSource generated}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (authority : SourceNativeFiniteLedgerPatchGeneratedEntryAt source
      ExactTransitionAt writeRowSource terminalRowSource generated patch entry) :
    authority.CommutesWithWorld := by
  cases generated with
  | nativeWrite payload source_eq targetOccurrence ledgerEvolution =>
      constructor
      · exact authority.target_eq_fold.trans
          (congrArg (fun evolution => (evolution.destination entry).1) patch.2)
      · exact authority.evolution_heq_fold.trans
          (LedgerWriteEvolutionAt.destination_evolution_heq patch.2 entry)
  | relationWrite payload source_eq targetOccurrence ledgerEvolution =>
      constructor
      · exact authority.target_eq_fold.trans
          (congrArg (fun evolution => (evolution.destination entry).1) patch.2)
      · exact authority.evolution_heq_fold.trans
          (LedgerWriteEvolutionAt.destination_evolution_heq patch.2 entry)
  | continuedTransport payload source_eq targetOccurrence ledgerEvolution =>
      constructor
      · exact authority.target_eq_fold.trans
          (congrArg (fun evolution => (evolution.destination entry).1) patch.2)
      · exact authority.evolution_heq_fold.trans
          (LedgerWriteEvolutionAt.destination_evolution_heq patch.2 entry)
  | borromeanRedirect payload source_eq targetOccurrence ledgerEvolution =>
      constructor
      · exact authority.target_eq_fold.trans
          (congrArg (fun evolution => (evolution.destination entry).1) patch.2)
      · exact authority.evolution_heq_fold.trans
          (LedgerWriteEvolutionAt.destination_evolution_heq patch.2 entry)
  | faithfulTerminal payload source_eq ledgerEvolution =>
      exact authority.terminal_eq_fold.trans
        (congrArg (fun evolution => evolution.discharge entry) patch.2)

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
