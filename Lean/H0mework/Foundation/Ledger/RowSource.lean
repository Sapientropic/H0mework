import H0mework.Foundation.Ledger.Evolution

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-! ## Finite source-generated incidence patches

The total `destination` / `origin` tables above remain compatibility readouts,
not patch inputs.  Authority consists of finitely many generated exceptional
rows plus either an identity remainder or one event compiled by a source-fixed
remainder law. -/

/-- Source-fixed compiler for one transported ledger remainder.  Its one
event generates both the total compatibility evolution and exact pairwise
certification. -/
structure LedgerTransportedRemainderSourceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u) : Type (u + 1) where
  OccurrenceAt :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      N.Support → Type u
  emit? :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      (targetSupport : N.Support) →
        Option (OccurrenceAt occurrence targetSupport)
  compileEvolution :
    {current : V.Current} →
      {occurrence : source.toRootSource.actual.OccurrenceAt current} →
      {targetSupport : N.Support} →
      OccurrenceAt occurrence targetSupport →
        LedgerWriteEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩
          ⟨targetSupport⟩
  compileExact :
    {current : V.Current} →
      {occurrence : source.toRootSource.actual.OccurrenceAt current} →
      {targetSupport : N.Support} →
      (event : OccurrenceAt occurrence targetSupport) →
        ExactLedgerWriteCertificationAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩
          ⟨targetSupport⟩ (ExactTransitionAt occurrence)
          (compileEvolution event)

namespace LedgerTransportedRemainderSourceAt

def empty
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u) :
    LedgerTransportedRemainderSourceAt source ExactTransitionAt where
  OccurrenceAt := fun _ _ => PEmpty
  emit? := fun _ _ => none
  compileEvolution := fun {_} {_} {_} event => nomatch event
  compileExact := fun {_} {_} {_} event => nomatch event

end LedgerTransportedRemainderSourceAt

/-- Source-fixed compiler law for exact continuing incidence rows.

This law belongs to the root source before any occurrence is emitted.  A
finite patch never stores this compiler; it stores only exact emitted events
and their already compiled receipts. -/
structure LedgerWriteRowSourceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u) : Type (u + 1) where
  IncidenceOccurrenceAt :
    {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      (sourceEntry : OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence)) →
      (targetEntry : OpenResponsibilityAt N targetSupport) → Type u
  compileEvolution :
    {current : V.Current} →
      {occurrence : source.toRootSource.actual.OccurrenceAt current} →
      {targetSupport : N.Support} →
      {sourceEntry : OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence)} →
      {targetEntry : OpenResponsibilityAt N targetSupport} →
      IncidenceOccurrenceAt occurrence sourceEntry targetEntry →
      LedgerEntryEvolutionAt N sourceEntry targetEntry
  compileExact :
    {current : V.Current} →
      {occurrence : source.toRootSource.actual.OccurrenceAt current} →
      {targetSupport : N.Support} →
      {sourceEntry : OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence)} →
      {targetEntry : OpenResponsibilityAt N targetSupport} →
      IncidenceOccurrenceAt occurrence sourceEntry targetEntry →
      ExactTransitionAt occurrence sourceEntry targetEntry
  /-- Optional source-fixed transported-remainder compiler.  Existing finite
  sources inherit the empty event family without changing semantics. -/
  transportedRemainderSource :
    LedgerTransportedRemainderSourceAt source ExactTransitionAt :=
      LedgerTransportedRemainderSourceAt.empty source ExactTransitionAt

/-- One exact continuing row already generated by the fixed row source.
The private constructor prevents a patch from installing a second compiler. -/
structure GeneratedLedgerWriteRowAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt N targetSupport) : Type u where
  private mk ::
  event : rowSource.IncidenceOccurrenceAt occurrence sourceEntry targetEntry
  evolution : LedgerEntryEvolutionAt N sourceEntry targetEntry
  evolution_eq : rowSource.compileEvolution event = evolution
  exact : ExactTransitionAt occurrence sourceEntry targetEntry
  exact_eq : rowSource.compileExact event = exact

/-- One transported remainder generated by the fixed row source.  The only
stored datum is its exact source event; total evolution and exact pairwise
certification are compiler readbacks from that event. -/
structure GeneratedLedgerTransportedRemainderAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    (target : CompleteLiveLedgerAt N) : Type u where
  private mk ::
  event : rowSource.transportedRemainderSource.OccurrenceAt
    occurrence target.support
  selected : rowSource.transportedRemainderSource.emit?
    occurrence target.support = some event

namespace LedgerWriteRowSourceAt

/-- Source law with no continuing incidence events.  It is useful for branches
whose finite patch is the empty identity remainder. -/
def empty
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeSource N V)
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u) :
    LedgerWriteRowSourceAt source ExactTransitionAt where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun {_} {_} {_} {_} {_} event => nomatch event
  compileExact := fun {_} {_} {_} {_} {_} event => nomatch event

/-- Compile one exact incidence event with the already fixed source law. -/
def generate
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {targetSupport : N.Support}
    {sourceEntry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (event : rowSource.IncidenceOccurrenceAt occurrence sourceEntry targetEntry) :
    GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry where
  event := event
  evolution := rowSource.compileEvolution event
  evolution_eq := rfl
  exact := rowSource.compileExact event
  exact_eq := rfl

/-- Canonical receipt compiler for one fixed source row and exact endpoints. -/
def authorityCompiler
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt N targetSupport) :
    CanonicalReceiptAuthority.Compiler
      (rowSource.IncidenceOccurrenceAt occurrence sourceEntry targetEntry)
      (LedgerEntryEvolutionAt N sourceEntry targetEntry ×
        ExactTransitionAt occurrence sourceEntry targetEntry) where
  compile := fun event =>
    ⟨rowSource.compileEvolution event, rowSource.compileExact event⟩

/-- Read the unique transported-remainder event selected by the fixed source.
No raw event enters this authority mouth. -/
def generateTransportedRemainder?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    (target : CompleteLiveLedgerAt N) :
    Option (GeneratedLedgerTransportedRemainderAt
      rowSource occurrence target) :=
  match selected : rowSource.transportedRemainderSource.emit?
      occurrence target.support with
  | none => none
  | some event => some ⟨event, selected⟩

/-- Seal one transported remainder from the exact event selected by the
source-owned `emit?` compiler.  This is the dependent, non-`Option.get` form
of `generateTransportedRemainder?`; it still requires the canonical selection
equation and therefore cannot admit a caller-only raw remainder event. -/
def generateTransportedRemainder
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    (target : CompleteLiveLedgerAt N)
    (event : rowSource.transportedRemainderSource.OccurrenceAt
      occurrence target.support)
    (selected : rowSource.transportedRemainderSource.emit?
      occurrence target.support = some event) :
    GeneratedLedgerTransportedRemainderAt rowSource occurrence target where
  event := event
  selected := selected

/-- Canonical compiler for the whole transported remainder. -/
def transportedRemainderAuthorityCompiler
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    (rowSource : LedgerWriteRowSourceAt source ExactTransitionAt)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    (target : CompleteLiveLedgerAt N) :
    CanonicalReceiptAuthority.Compiler
      (rowSource.transportedRemainderSource.OccurrenceAt
        occurrence target.support)
      (Sigma fun evolution : LedgerWriteEvolutionAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩ target =>
        ExactLedgerWriteCertificationAt N
          ⟨source.toRootSource.account.supportOf occurrence⟩ target
          (ExactTransitionAt occurrence) evolution) where
  compile := fun event =>
    ⟨rowSource.transportedRemainderSource.compileEvolution event,
      rowSource.transportedRemainderSource.compileExact event⟩

end LedgerWriteRowSourceAt

namespace GeneratedLedgerWriteRowAt

/-- The exact generated row as a canonical source receipt. -/
def isCanonical
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {rowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {targetSupport : N.Support}
    {sourceEntry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    CanonicalReceiptAuthority.CanonicalReceipt
      (rowSource.authorityCompiler sourceEntry targetEntry)
      ⟨row.evolution, row.exact⟩ where
  actualEvent := row.event
  compile_eq := Prod.ext row.evolution_eq row.exact_eq

end GeneratedLedgerWriteRowAt

namespace GeneratedLedgerTransportedRemainderAt

def evolution
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {rowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N}
    (generated : GeneratedLedgerTransportedRemainderAt
      rowSource occurrence target) :
    LedgerWriteEvolutionAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩ target :=
  rowSource.transportedRemainderSource.compileEvolution generated.event

def exact
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {rowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N}
    (generated : GeneratedLedgerTransportedRemainderAt
      rowSource occurrence target) :
    ExactLedgerWriteCertificationAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩ target
      (ExactTransitionAt occurrence) generated.evolution :=
  rowSource.transportedRemainderSource.compileExact generated.event

def isCanonical
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    {ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u}
    {rowSource : LedgerWriteRowSourceAt source ExactTransitionAt}
    {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {target : CompleteLiveLedgerAt N}
    (generated : GeneratedLedgerTransportedRemainderAt
      rowSource occurrence target) :
    CanonicalReceiptAuthority.CanonicalReceipt
      (rowSource.transportedRemainderAuthorityCompiler occurrence target)
      ⟨generated.evolution, generated.exact⟩ where
  actualEvent := generated.event
  compile_eq := rfl

end GeneratedLedgerTransportedRemainderAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
