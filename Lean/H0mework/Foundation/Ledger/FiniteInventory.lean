import H0mework.Foundation.Ledger.RowSource

/-!
# Finite ledger incidence inventories

Finite generated rows and exact identity/complete coverage data.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- A finite family of already generated exact incidence rows. -/
structure FiniteGeneratedLedgerWriteRowsAt
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
  size : Nat
  sourceEntryAt : Fin size →
    OpenResponsibilityAt N (source.toRootSource.account.supportOf occurrence)
  targetEntryAt : Fin size → target.Entry
  rowAt : (index : Fin size) →
    GeneratedLedgerWriteRowAt rowSource occurrence
      (sourceEntryAt index) (targetEntryAt index)

namespace FiniteGeneratedLedgerWriteRowsAt

/-- Generated ledger evolution of one exact finite row. -/
def evolutionAt
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
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence
      ⟨source.toRootSource.account.supportOf occurrence⟩)
    (index : Fin rows.size) :
    LedgerEntryEvolutionAt N (rows.sourceEntryAt index)
      (rows.targetEntryAt index) :=
  (rows.rowAt index).evolution

/-- Generated exact transition certificate of one finite row. -/
def exactAt
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
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target)
    (index : Fin rows.size) :
    ExactTransitionAt occurrence (rows.sourceEntryAt index)
      (rows.targetEntryAt index) :=
  (rows.rowAt index).exact

end FiniteGeneratedLedgerWriteRowsAt

/-- Finite changed rows on one unchanged support.  `none` is not an unknown
answer: it is definitionally the exact identity carry.  A `some` index must
point back to the queried dependent entry, so the lookup functions cannot hide
an unrelated Boolean oracle. -/
structure LedgerIdentityRemainderCoverageAt
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
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence
      ⟨source.toRootSource.account.supportOf occurrence⟩) :
    Type u where
  destinationIndex : (entry : OpenResponsibilityAt N
    (source.toRootSource.account.supportOf occurrence)) →
      Option { index : Fin rows.size // rows.sourceEntryAt index = entry }
  originIndex : (entry : OpenResponsibilityAt N
    (source.toRootSource.account.supportOf occurrence)) →
      Option { index : Fin rows.size // rows.targetEntryAt index = entry }

/-- Finite exceptional rows over one generated transported remainder.  A
`none` selector is not an unknown answer: it delegates to the single
source-generated remainder event carried by the patch. -/
structure LedgerTransportedRemainderCoverageAt
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
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target) :
    Type u where
  destinationIndex : (entry : OpenResponsibilityAt N
    (source.toRootSource.account.supportOf occurrence)) →
      Option { index : Fin rows.size // rows.sourceEntryAt index = entry }
  originIndex : (entry : target.Entry) →
      Option { index : Fin rows.size // rows.targetEntryAt index = entry }

/-- A cross-support patch must enumerate the complete source and target
fibres.  The index maps are constrained by dependent entry equality, so a
finite patch cannot cover an actually infinite ledger. -/
structure LedgerCompleteFiniteCoverageAt
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
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target) :
    Type u where
  destinationIndex : OpenResponsibilityAt N
    (source.toRootSource.account.supportOf occurrence) → Fin rows.size
  originIndex : target.Entry → Fin rows.size
  destination_sound : (entry : OpenResponsibilityAt N
    (source.toRootSource.account.supportOf occurrence)) →
    rows.sourceEntryAt (destinationIndex entry) = entry
  origin_sound : (entry : target.Entry) →
    rows.targetEntryAt (originIndex entry) = entry

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
