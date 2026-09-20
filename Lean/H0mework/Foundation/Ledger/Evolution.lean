import H0mework.Foundation.Authority.Receipt
import H0mework.Foundation.Source.SupportInventory

/-!
# Source-native root-ledger compiler

The structural root emits occurrences but carries no ledger receipt.  This
module adds the unique authority-bearing ledger layer for source-native roots.

An exact support-indexed occurrence is compiled locally into its structural
branch, its canonical successor occurrence, and its complete ledger
evolution.  The compiler never receives the global emitter function.  A root
then proves that the generated successor is the same occurrence emitted at
the target current.  Only this commuting compiler image has whole-ledger
authority.

`ExactLedgerWriteCertificationAt` certifies both total directions of every
continuing ledger evolution.  Every source entry has an exact target and every
target entry has an exact origin.  Each exact pair preserves the declared
incidence transition and lineage, so a weak transfer receipt cannot clone one
entry into unrelated targets or rewrite target lineage.

Terminal discharge is equally source-native: the exact occurrence emitted by
the root must compile to the terminal branch and generate the complete
entry-indexed `LedgerTerminalEvolutionAt`; it is not a second raw-world field.
Other inhabitants of the source event family are not emitted occurrences and
therefore cannot veto or authorize that terminal.

This is an additive constructive adapter.  It does not change the
compatibility root kernel or require a bijective update.  Legitimate
split/merge remains possible when the exact occurrence certifies every
participating source/target pair.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- The canonical ledger output of one exact source-native occurrence.

Every constructor is tied by `structural_eq` to the branch already generated
by the source's actual-event compiler.  Continuing constructors additionally
generate the exact successor occurrence used to index their target ledger;
terminal generates the complete entry-indexed discharge. -/
inductive SourceNativeLedgerEvolutionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) : Type u
  | nativeWrite
      (write : V.NativeWriteAt current)
      (structural_eq :
        source.toRootSource.actual.compile occurrence = .nativeWrite write)
      (targetOccurrence :
        source.toRootSource.actual.OccurrenceAt (V.nativeTarget write))
      (ledgerEvolution :
        LedgerWriteEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩)
  | relationWrite
      (write : V.RelationWriteAt current)
      (structural_eq :
        source.toRootSource.actual.compile occurrence = .relationWrite write)
      (targetOccurrence :
        source.toRootSource.actual.OccurrenceAt (V.relationTarget write))
      (ledgerEvolution :
        LedgerWriteEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩)
  | continuedTransport
      (write : V.ContinuedTransportAt current)
      (structural_eq :
        source.toRootSource.actual.compile occurrence =
          .continuedTransport write)
      (targetOccurrence :
        source.toRootSource.actual.OccurrenceAt (V.continuedTarget write))
      (ledgerEvolution :
        LedgerWriteEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩)
  | borromeanRedirect
      (write : V.BorromeanRedirectAt current)
      (structural_eq :
        source.toRootSource.actual.compile occurrence =
          .borromeanRedirect write)
      (targetOccurrence :
        source.toRootSource.actual.OccurrenceAt (V.redirectTarget write))
      (ledgerEvolution :
        LedgerWriteEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩
          ⟨source.toRootSource.account.supportOf targetOccurrence⟩)
  | faithfulTerminal
      (terminal : V.FaithfulTerminalAt current)
      (structural_eq :
        source.toRootSource.actual.compile occurrence =
          .faithfulTerminal terminal)
      (ledgerEvolution :
        LedgerTerminalEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩)

/-- Whole-ledger disposition of one exact source entry at this occurrence.

This is a readout of the canonical ledger compiler image.  Continuing
branches return the compiler-selected target entry and row; terminal returns
the exact discharge. -/
def SourceNativeLedgerEvolutionAt.entryDisposition
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) :
    LedgerEntryDispositionAt N entry :=
  match generated with
  | .nativeWrite _ _ _ ledgerEvolution =>
      .evolved (ledgerEvolution.destination entry).2
  | .relationWrite _ _ _ ledgerEvolution =>
      .evolved (ledgerEvolution.destination entry).2
  | .continuedTransport _ _ _ ledgerEvolution =>
      .evolved (ledgerEvolution.destination entry).2
  | .borromeanRedirect _ _ _ ledgerEvolution =>
      .evolved (ledgerEvolution.destination entry).2
  | .faithfulTerminal _ _ ledgerEvolution =>
      .terminal (ledgerEvolution.discharge entry)

/-- The occurrence generated by the local ledger compiler is the exact
occurrence emitted by this root at the structural target current.  Terminal
has no target occurrence and therefore commutes trivially. -/
def SourceNativeLedgerEvolutionAt.CommutesWith
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (emitted : (current : V.Current) →
      source.toRootSource.actual.OccurrenceAt current)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  match generated with
  | .nativeWrite write _ targetOccurrence _ =>
      targetOccurrence = emitted (V.nativeTarget write)
  | .relationWrite write _ targetOccurrence _ =>
      targetOccurrence = emitted (V.relationTarget write)
  | .continuedTransport write _ targetOccurrence _ =>
      targetOccurrence = emitted (V.continuedTarget write)
  | .borromeanRedirect write _ targetOccurrence _ =>
      targetOccurrence = emitted (V.redirectTarget write)
  | .faithfulTerminal _ _ _ => True

/-- Zero-information witness that one source-ledger compiler image has an
actual successor.  Target current, target occurrence and whole-ledger
evolution are read from the indexed compiler image. -/
def SourceNativeLedgerGeneratedSuccessorAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    (generated : SourceNativeLedgerEvolutionAt source occurrence) : Type u :=
  match generated with
  | .faithfulTerminal .. => PEmpty
  | .nativeWrite ..
  | .relationWrite ..
  | .continuedTransport ..
  | .borromeanRedirect .. => PUnit

namespace SourceNativeLedgerGeneratedSuccessorAt

/-- Construct the successor token exactly when the compiler image continues. -/
def ofGenerated?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) :
    Option (SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :=
  match generated with
  | .faithfulTerminal .. => none
  | .nativeWrite ..
  | .relationWrite ..
  | .continuedTransport ..
  | .borromeanRedirect .. => some PUnit.unit

/-- Target current generated by the same source compiler image. -/
def targetCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (_successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    V.Current :=
  match generated with
  | .nativeWrite write .. => V.nativeTarget write
  | .relationWrite write .. => V.relationTarget write
  | .continuedTransport write .. => V.continuedTarget write
  | .borromeanRedirect write .. => V.redirectTarget write
  | .faithfulTerminal .. => nomatch _successor

/-- Target occurrence generated by the same source compiler image. -/
def targetOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    source.toRootSource.actual.OccurrenceAt successor.targetCurrent :=
  match generated with
  | .nativeWrite _ _ targetOccurrence _ => targetOccurrence
  | .relationWrite _ _ targetOccurrence _ => targetOccurrence
  | .continuedTransport _ _ targetOccurrence _ => targetOccurrence
  | .borromeanRedirect _ _ targetOccurrence _ => targetOccurrence
  | .faithfulTerminal .. => nomatch successor

/-- Whole-ledger evolution carried by the same successor. -/
def ledgerEvolution
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    LedgerWriteEvolutionAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩
      ⟨source.toRootSource.account.supportOf successor.targetOccurrence⟩ :=
  match generated with
  | .nativeWrite _ _ _ ledgerEvolution => ledgerEvolution
  | .relationWrite _ _ _ ledgerEvolution => ledgerEvolution
  | .continuedTransport _ _ _ ledgerEvolution => ledgerEvolution
  | .borromeanRedirect _ _ _ ledgerEvolution => ledgerEvolution
  | .faithfulTerminal .. => nomatch successor

/-- The structural compiler target is the generated successor current. -/
theorem next_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {generated : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    (source.toRootSource.actual.compile occurrence).nextCurrent? =
      some successor.targetCurrent := by
  cases generated with
  | nativeWrite _ structural_eq _ _ => rw [structural_eq]; rfl
  | relationWrite _ structural_eq _ _ => rw [structural_eq]; rfl
  | continuedTransport _ structural_eq _ _ => rw [structural_eq]; rfl
  | borromeanRedirect _ structural_eq _ _ => rw [structural_eq]; rfl
  | faithfulTerminal => exact nomatch successor

end SourceNativeLedgerGeneratedSuccessorAt

/-- Pairwise source-native certification of a total whole-ledger evolution.
The fields account for every source destination and every target origin; they
do not require those maps to be inverse or injective. -/
structure ExactLedgerWriteCertificationAt
    (N : WorldRelationNetwork.{u})
    (source target : CompleteLiveLedgerAt N)
    (ExactTransitionAt : source.Entry → target.Entry → Type u)
    (evolution : LedgerWriteEvolutionAt N source target) : Type u where
  destination : (sourceEntry : source.Entry) →
    ExactTransitionAt sourceEntry (evolution.destination sourceEntry).1
  origin : (targetEntry : target.Entry) →
    ExactTransitionAt (evolution.origin targetEntry).1 targetEntry


end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
