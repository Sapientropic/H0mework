import H0mework.Foundation.Ledger.BranchAuthority

/-!
# Source-native ledger compiler and root closure

Installs branch authority into the fixed source compiler and emitted root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Canonical ledger compiler owned by one source-native event law.

`compile` consumes only the exact occurrence.  It cannot inspect the whole
emitter or a future world.  Exact incidence authority is carried by generated
finite rows or one generated remainder/support-settlement event. -/
structure SourceNativeLedgerCompiler
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V) : Type (u + 1) where
  IncidenceTransitionAt :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      N.Incidence → N.Incidence → Type u
  ExactTransitionAt :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u
  exact_incidence :
    {current : V.Current} →
      {occurrence : source.toRootSource.actual.OccurrenceAt current} →
      {targetSupport : N.Support} →
      {sourceEntry : OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence)} →
      {targetEntry : OpenResponsibilityAt N targetSupport} →
      ExactTransitionAt occurrence sourceEntry targetEntry →
      IncidenceTransitionAt occurrence
        (N.incidenceAt (source.toRootSource.account.supportOf occurrence))
        (N.incidenceAt targetSupport)
  exact_lineage :
    {current : V.Current} →
      {occurrence : source.toRootSource.actual.OccurrenceAt current} →
      {targetSupport : N.Support} →
      {sourceEntry : OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence)} →
      {targetEntry : OpenResponsibilityAt N targetSupport} →
      ExactTransitionAt occurrence sourceEntry targetEntry →
      N.lineageAt (source.toRootSource.account.supportOf occurrence) =
        N.lineageAt targetSupport
  writeRowSource : LedgerWriteRowSourceAt source ExactTransitionAt
  terminalRowSource : LedgerTerminalRowSourceAt source
  compile :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      SourceNativeLedgerEvolutionAt source occurrence
  compilePatch :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      SourceNativeFiniteLedgerPatchAt source ExactTransitionAt
        writeRowSource terminalRowSource
        (compile occurrence)

/-- Compiler-level terminal/transfer splice.  The exact occurrence fixes both
the whole-ledger evolution and its generated patch before this function sees the
semantic effect. -/
def SourceNativeLedgerCompiler.canonicalGeneratedEntry_of_terminalOrTransferred
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (effect : SourceNativeLedgerTerminalOrTransferredAt
      (compiler.compile occurrence) entry) :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt source
      compiler.ExactTransitionAt compiler.writeRowSource
      compiler.terminalRowSource (compiler.compile occurrence)
      (compiler.compilePatch occurrence) entry :=
  sourceNativeFiniteLedgerPatchGeneratedEntry_of_terminalOrTransferred
    (compiler.compilePatch occurrence) entry effect

/-- Complete identity of a source-native structural law together with its
canonical occurrence-local whole-ledger compiler. -/
structure SourceNativeLedgerSource
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  source : SourceNativeSource N V
  ledgerCompiler : SourceNativeLedgerCompiler source

/-- A source-native root whose generated successor occurrence is required to
be the occurrence emitted by the same root at the target current. -/
structure SourceNativeLedgerRootClosure
    (N : WorldRelationNetwork.{u}) (V : Vocabulary.{u}) : Type (u + 1) where
  source : SourceNativeLedgerSource N V
  emitted : (current : V.Current) →
    source.source.toRootSource.actual.OccurrenceAt current
  compiler_commutes : (current : V.Current) →
    (source.ledgerCompiler.compile (emitted current)).CommutesWith emitted

/-- The canonical source-native ledger output at one emitted occurrence. -/
def SourceNativeLedgerRootClosure.generatedLedgerAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) (current : V.Current) :
    SourceNativeLedgerEvolutionAt root.source.source (root.emitted current) :=
  root.source.ledgerCompiler.compile (root.emitted current)

/-- The authoritative generated patch at one emitted occurrence.  The
whole-ledger table is recovered only by folding its source events. -/
def SourceNativeLedgerRootClosure.generatedPatchAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) (current : V.Current) :
    SourceNativeFiniteLedgerPatchAt root.source.source
      root.source.ledgerCompiler.ExactTransitionAt
      root.source.ledgerCompiler.writeRowSource
      root.source.ledgerCompiler.terminalRowSource
      (root.generatedLedgerAt current) :=
  root.source.ledgerCompiler.compilePatch (root.emitted current)

/-- Forget the ledger compiler while retaining source-native support and the
complete affected-inventory presentation. -/
def SourceNativeLedgerRootClosure.toInventoryRoot
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) :
    SourceNativeRootClosure N V where
  source := root.source.source
  emitted := root.emitted

/-- Compatibility view of the complete source-native root.

This projection deliberately forgets the affected-inventory and ledger
compiler.  It is useful for older root readouts, but authority layers which
must distinguish source compilers keep the original
`SourceNativeLedgerRootClosure` in their type index. -/
def SourceNativeLedgerRootClosure.toRoot
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V) : RootClosure N V :=
  root.toInventoryRoot.toRoot

/-- The exact target entry generated by the root world at a continuing
current.  `next_eq` identifies the already generated structural target; the
entry itself is projected from the same source-native whole-ledger evolution.
No target payload is accepted at this mouth. -/
def SourceNativeLedgerRootClosure.canonicalTargetEntryAtNext
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    {current next : V.Current}
    (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (sourceEntry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted current))) :
    OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted next)) := by
  cases generated_eq : root.generatedLedgerAt current with
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.nativeTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.nativeTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .nativeWrite write structural_eq targetOccurrence ledgerEvolution from
            generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.relationTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.relationTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .relationWrite write structural_eq targetOccurrence ledgerEvolution from
            generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.continuedTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.continuedTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .continuedTransport write structural_eq targetOccurrence ledgerEvolution from
            generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.redirectTarget write = next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted current)).nextCurrent? = some next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.redirectTarget write) := by
        have commutes := root.compiler_commutes current
        rw [show root.source.ledgerCompiler.compile (root.emitted current) =
          .borromeanRedirect write structural_eq targetOccurrence ledgerEvolution from
            generated_eq] at commutes
        exact commutes
      cases target_eq
      cases occurrence_eq
      exact (ledgerEvolution.destination sourceEntry).1
  | faithfulTerminal terminal structural_eq ledgerEvolution =>
      change
        (root.source.source.toRootSource.actual.compile
          (root.emitted current)).nextCurrent? = some next at next_eq
      rw [structural_eq] at next_eq
      contradiction

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
