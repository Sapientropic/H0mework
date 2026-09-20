import H0mework.Foundation.Ledger.TerminalPatch

/-!
# Canonical patch selection authority

Selects finite exceptional or generated-remainder authority from the fold's own selectors.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Stored source-entry membership in a finite continuing patch.

This is only an inventory readout.  A stored row may be omitted by an
identity-remainder selector, so membership alone carries no lifecycle or
causal authority. -/
def FiniteGeneratedLedgerWritePatchAt.GeneratedSourceEntryAt
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
    (patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type :=
  match patch with
  | .identityRemainder rows _ =>
      { index : Fin rows.size // rows.sourceEntryAt index = entry }
  | .complete rows _ =>
      { index : Fin rows.size // rows.sourceEntryAt index = entry }
  | .transportedRemainder rows _ _ =>
      { index : Fin rows.size // rows.sourceEntryAt index = entry }

/-- Selection token for one identity-remainder row.

The constructor is private: external consumers cannot turn arbitrary stored
membership into authority by submitting a `row_is_selected` proof.  The only
public producer below reads the same destination selector used by the ledger
fold. -/
structure IdentitySelectedSourceRowAt
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
    {rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence
      ⟨source.toRootSource.account.supportOf occurrence⟩}
    (coverage : LedgerIdentityRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type where
  private mk ::
  indexed : { index : Fin rows.size // rows.sourceEntryAt index = entry }
  selected : coverage.destinationIndex entry = some indexed

/-- Selection token for a complete patch.  Complete coverage fixes the source
row index definitionally through `destinationIndex`; there is no optional
membership choice left for a consumer. -/
structure CompleteSelectedSourceRowAt
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
    {rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target}
    (_coverage : LedgerCompleteFiniteCoverageAt rows)
    (_entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type where
  private mk ::

structure TransportedExceptionalSelectedSourceRowAt
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
    {rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target}
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type where
  private mk ::
  indexed : { index : Fin rows.size // rows.sourceEntryAt index = entry }
  selected : coverage.destinationIndex entry = some indexed

structure TransportedRemainderSelectedSourceRowAt
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
    {rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target}
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type where
  private mk ::
  omitted : coverage.destinationIndex entry = none

abbrev TransportedSelectedSourceRowAt
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
    {rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target}
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type :=
  TransportedExceptionalSelectedSourceRowAt coverage entry ⊕
    TransportedRemainderSelectedSourceRowAt coverage entry

/-- The exact source row selected by the same coverage function used to fold
the finite patch into the world ledger. -/
def FiniteGeneratedLedgerWritePatchAt.CanonicalGeneratedSourceRowAt
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
    (patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) : Type :=
  match patch with
  | .identityRemainder _ coverage =>
      IdentitySelectedSourceRowAt coverage entry
  | .complete _ coverage => CompleteSelectedSourceRowAt coverage entry
  | .transportedRemainder _ coverage _ =>
      TransportedSelectedSourceRowAt coverage entry

/-- Canonical source-row producer.  An omitted identity-remainder row returns
`none`; a complete patch always returns the row fixed by its coverage map. -/
def FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?
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
    (patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence)) :
    Option (patch.CanonicalGeneratedSourceRowAt entry) :=
  match patch with
  | .identityRemainder _ coverage =>
      match h : coverage.destinationIndex entry with
      | none => none
      | some indexed => some (IdentitySelectedSourceRowAt.mk indexed h)
  | .complete _ coverage => some CompleteSelectedSourceRowAt.mk
  | .transportedRemainder _ coverage _ =>
      match h : coverage.destinationIndex entry with
      | none => some (.inr (TransportedRemainderSelectedSourceRowAt.mk h))
      | some indexed =>
          some (.inl (TransportedExceptionalSelectedSourceRowAt.mk indexed h))

/-- A canonical source row is always recovered by the same destination
selector that generated the finite patch. -/
theorem FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?_isSome
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
    (patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (row : patch.CanonicalGeneratedSourceRowAt entry) :
    (patch.canonicalGeneratedSourceRow? entry).isSome = true := by
  cases patch with
  | complete => rfl
  | identityRemainder rows coverage =>
      simp only [FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?]
      split
      · rename_i hnone
        exact False.elim
          (Option.some_ne_none _ (row.selected.symm.trans hnone))
      · rfl
  | transportedRemainder rows coverage remainder =>
      simp only [FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow?]
      split <;> rfl

/-- A transferred whole-ledger destination cannot be hidden in the identity
remainder of a finite patch.

For a complete patch the source row is already fixed by total coverage.  For
an identity-remainder patch, omission means definitionally that the entry was
carried unchanged; a genuine transfer therefore forces the same destination
selector to expose its canonical generated row. -/
def FiniteGeneratedLedgerWritePatchAt.canonicalGeneratedSourceRow_of_transferred
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
    (patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (transferred : ledgerEntryIsTransferred
      (patch.toLedgerWriteEvolution.destination entry).2 = true) :
    patch.CanonicalGeneratedSourceRowAt entry := by
  cases patch with
  | complete rows coverage =>
      exact CompleteSelectedSourceRowAt.mk
  | identityRemainder rows coverage =>
      cases h : coverage.destinationIndex entry with
      | some indexed =>
          exact IdentitySelectedSourceRowAt.mk indexed h
      | none =>
          change ledgerEntryIsTransferred
            ((identityRemainderEvolution rows coverage).destination entry).2 =
              true at transferred
          have carried := identityRemainder_destination_isNotTransferred
            rows coverage entry h
          rw [transferred] at carried
          contradiction
  | transportedRemainder rows coverage remainder =>
      cases h : coverage.destinationIndex entry with
      | some indexed =>
          exact .inl (TransportedExceptionalSelectedSourceRowAt.mk indexed h)
      | none =>
          exact .inr (TransportedRemainderSelectedSourceRowAt.mk h)

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
