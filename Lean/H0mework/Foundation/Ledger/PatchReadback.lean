import H0mework.Foundation.Ledger.PatchSelection

/-!
# Canonical patch readback

Recovers fold-aligned target, evolution, and exact-transition coordinates.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Target incidence of the exact row selected by the fold. -/
def FiniteGeneratedLedgerWritePatchAt.CanonicalGeneratedSourceRowAt.targetEntry
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
    {patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (selected : patch.CanonicalGeneratedSourceRowAt entry) : target.Entry :=
  match patch with
  | .identityRemainder rows _ => rows.targetEntryAt selected.indexed.1
  | .complete rows coverage => rows.targetEntryAt (coverage.destinationIndex entry)
  | .transportedRemainder rows _ remainder =>
      match selected with
      | .inl exceptional => rows.targetEntryAt exceptional.indexed.1
      | .inr _ => (remainder.evolution.destination entry).1

/-- Uniform exact row readout of either a finite exceptional event or the one
generated transported-remainder event.  Authority remains in the selection
token; this record only exposes its dependent evolution and exact transition. -/
structure CanonicalGeneratedLedgerWriteRowReadoutAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V}
    (ExactTransitionAt :
      {current : V.Current} →
      (occurrence : source.toRootSource.actual.OccurrenceAt current) →
      {targetSupport : N.Support} →
      OpenResponsibilityAt N
        (source.toRootSource.account.supportOf occurrence) →
      OpenResponsibilityAt N targetSupport → Type u)
    {current : V.Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt N targetSupport) : Type u where
  evolution : LedgerEntryEvolutionAt N sourceEntry targetEntry
  exact : ExactTransitionAt occurrence sourceEntry targetEntry

/-- The exact generated row readout selected by the fold. -/
def FiniteGeneratedLedgerWritePatchAt.CanonicalGeneratedSourceRowAt.row
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
    {patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (selected : patch.CanonicalGeneratedSourceRowAt entry) :
    CanonicalGeneratedLedgerWriteRowReadoutAt ExactTransitionAt occurrence
      entry selected.targetEntry := by
  cases patch with
  | identityRemainder rows coverage =>
      let generated := Eq.mp
        (congrArg
          (fun sourceEntry =>
            GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry
              (rows.targetEntryAt selected.indexed.1))
          selected.indexed.property)
        (rows.rowAt selected.indexed.1)
      exact ⟨generated.evolution, generated.exact⟩
  | complete rows coverage =>
      let generated := Eq.mp
        (congrArg
          (fun sourceEntry =>
            GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry
              (rows.targetEntryAt (coverage.destinationIndex entry)))
          (coverage.destination_sound entry))
        (rows.rowAt (coverage.destinationIndex entry))
      exact ⟨generated.evolution, generated.exact⟩
  | transportedRemainder rows coverage remainder =>
      rcases selected with exceptional | transported
      · let generated := Eq.mp
          (congrArg
            (fun sourceEntry =>
              GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry
                (rows.targetEntryAt exceptional.indexed.1))
            exceptional.indexed.property)
          (rows.rowAt exceptional.indexed.1)
        exact ⟨generated.evolution, generated.exact⟩
      · exact
          ⟨(remainder.evolution.destination entry).2,
            remainder.exact.destination entry⟩

/-- Casting the source endpoint of a generated row casts its evolution by the
same equality.  This keeps the row receipt and the whole-ledger fold in one
dependent equality rather than comparing endpoint projections afterward. -/
theorem GeneratedLedgerWriteRowAt.castSource_evolution_heq
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
    {sourceEntry sourceEntry' : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    {targetEntry : OpenResponsibilityAt N targetSupport}
    (source_eq : sourceEntry = sourceEntry')
    (row : GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry) :
    HEq
      (Eq.mp
        (congrArg
          (fun sourceEntry =>
            GeneratedLedgerWriteRowAt rowSource occurrence sourceEntry targetEntry)
          source_eq)
        row).evolution
      (Eq.mp
        (congrArg
          (fun sourceEntry =>
            LedgerEntryEvolutionAt N sourceEntry targetEntry)
          source_eq)
        row.evolution) := by
  cases source_eq
  rfl

/-- The selected target is exactly the destination used by the world fold. -/
theorem FiniteGeneratedLedgerWritePatchAt.CanonicalGeneratedSourceRowAt.target_eq_fold
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
    {patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (selected : patch.CanonicalGeneratedSourceRowAt entry) :
    selected.targetEntry =
      (patch.toLedgerWriteEvolution.destination entry).1 := by
  cases patch with
  | identityRemainder rows coverage =>
      rcases selected with ⟨indexed, selected_eq⟩
      rcases indexed with ⟨index, source_eq⟩
      cases source_eq
      dsimp only [CanonicalGeneratedSourceRowAt.targetEntry,
        toLedgerWriteEvolution, identityRemainderEvolution]
      rw [selected_eq]
  | complete rows coverage =>
      rfl
  | transportedRemainder rows coverage remainder =>
      rcases selected with exceptional | transported
      · rcases exceptional with ⟨indexed, selected_eq⟩
        rcases indexed with ⟨index, source_eq⟩
        cases source_eq
        dsimp only [CanonicalGeneratedSourceRowAt.targetEntry,
          toLedgerWriteEvolution, transportedRemainderEvolution]
        rw [selected_eq]
      · rcases transported with ⟨omitted⟩
        dsimp only [CanonicalGeneratedSourceRowAt.targetEntry,
          toLedgerWriteEvolution, transportedRemainderEvolution]
        rw [omitted]

/-- Exact transition readback at the literal destination selected by the
whole-ledger fold. -/
def FiniteGeneratedLedgerWritePatchAt.CanonicalGeneratedSourceRowAt.exactAtFold
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
    {patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (selected : patch.CanonicalGeneratedSourceRowAt entry) :
    ExactTransitionAt occurrence entry
      (patch.toLedgerWriteEvolution.destination entry).1 :=
  selected.target_eq_fold ▸ selected.row.exact

/-- The selected row evolution is definitionally the evolution used by the
same world-fold destination. -/
theorem FiniteGeneratedLedgerWritePatchAt.CanonicalGeneratedSourceRowAt.evolution_heq_fold
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
    {patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target}
    {entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)}
    (selected : patch.CanonicalGeneratedSourceRowAt entry) :
    HEq selected.row.evolution
      (patch.toLedgerWriteEvolution.destination entry).2 := by
  cases patch with
  | identityRemainder rows coverage =>
      rcases selected with ⟨indexed, selected_eq⟩
      rcases indexed with ⟨index, source_eq⟩
      cases source_eq
      dsimp only [CanonicalGeneratedSourceRowAt.row,
        CanonicalGeneratedSourceRowAt.targetEntry,
        toLedgerWriteEvolution, identityRemainderEvolution,
        FiniteGeneratedLedgerWriteRowsAt.evolutionAt]
      rw [selected_eq]
      rfl
  | complete rows coverage =>
      dsimp only [CanonicalGeneratedSourceRowAt.row,
        CanonicalGeneratedSourceRowAt.targetEntry,
        toLedgerWriteEvolution, completeEvolution]
      exact GeneratedLedgerWriteRowAt.castSource_evolution_heq
        (coverage.destination_sound entry)
        (rows.rowAt (coverage.destinationIndex entry))
  | transportedRemainder rows coverage remainder =>
      rcases selected with exceptional | transported
      · rcases exceptional with ⟨indexed, selected_eq⟩
        rcases indexed with ⟨index, source_eq⟩
        cases source_eq
        dsimp only [CanonicalGeneratedSourceRowAt.row,
          CanonicalGeneratedSourceRowAt.targetEntry,
          toLedgerWriteEvolution, transportedRemainderEvolution]
        rw [selected_eq]
        rfl
      · rcases transported with ⟨omitted⟩
        dsimp only [CanonicalGeneratedSourceRowAt.row,
          CanonicalGeneratedSourceRowAt.targetEntry,
          toLedgerWriteEvolution, transportedRemainderEvolution]
        rw [omitted]

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
