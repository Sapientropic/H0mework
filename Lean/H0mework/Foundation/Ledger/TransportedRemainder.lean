import H0mework.Foundation.Ledger.FiniteInventory

/-!
# Transported-remainder ledger patches

Folds finite exceptional rows over identity, complete, or generated remainder coverage.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Authoritative finite write patch.  Same-support writes have identity
remainder; cross-support writes may use finite complete coverage or one
source-generated transported remainder. -/
inductive FiniteGeneratedLedgerWritePatchAt
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
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    CompleteLiveLedgerAt N → Type u
  | identityRemainder
      (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence
        ⟨source.toRootSource.account.supportOf occurrence⟩)
      (coverage : LedgerIdentityRemainderCoverageAt rows) :
      FiniteGeneratedLedgerWritePatchAt rowSource occurrence
        ⟨source.toRootSource.account.supportOf occurrence⟩
  | complete
      {target : CompleteLiveLedgerAt N}
      (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target)
      (coverage : LedgerCompleteFiniteCoverageAt rows) :
      FiniteGeneratedLedgerWritePatchAt rowSource occurrence target
  | transportedRemainder
      {target : CompleteLiveLedgerAt N}
      (rows : FiniteGeneratedLedgerWriteRowsAt rowSource occurrence target)
      (coverage : LedgerTransportedRemainderCoverageAt rows)
      (remainder : GeneratedLedgerTransportedRemainderAt
        rowSource occurrence target) :
      FiniteGeneratedLedgerWritePatchAt rowSource occurrence target

namespace FiniteGeneratedLedgerWritePatchAt

/-- Empty finite patch on one ledger.  Every entry is definitionally carried;
no incidence event is manufactured for an unchanged row. -/
def identity
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
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt rowSource occurrence
      ⟨source.toRootSource.account.supportOf occurrence⟩ :=
  .identityRemainder
    { size := 0
      sourceEntryAt := Fin.elim0
      targetEntryAt := Fin.elim0
      rowAt := fun index => Fin.elim0 index }
    { destinationIndex := fun _ => none
      originIndex := fun _ => none }

/-- Fold an identity-remainder patch into the old total compatibility readout.
This helper is kept separate so the public fold has constructor equations that
reduce without passing through a tactic-generated dependent eliminator. -/
def identityRemainderEvolution
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
    (coverage : LedgerIdentityRemainderCoverageAt rows) :
    LedgerWriteEvolutionAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩
      ⟨source.toRootSource.account.supportOf occurrence⟩ :=
  {
    destination := fun entry =>
      match coverage.destinationIndex entry with
      | none => ⟨entry, .carried rfl HEq.rfl⟩
      | some indexed => by
          exact indexed.property ▸
            ⟨rows.targetEntryAt indexed.1, (rows.rowAt indexed.1).evolution⟩
    origin := fun entry =>
      match coverage.originIndex entry with
      | none => ⟨entry, .carried rfl HEq.rfl⟩
      | some indexed => by
          exact indexed.property ▸
            ⟨rows.sourceEntryAt indexed.1, (rows.rowAt indexed.1).evolution⟩
  }

/-- Fold a completely enumerated finite patch into the old total readout. -/
def completeEvolution
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
    (coverage : LedgerCompleteFiniteCoverageAt rows) :
    LedgerWriteEvolutionAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩ target :=
  {
    destination := fun entry => by
      let index := coverage.destinationIndex entry
      have source_eq := coverage.destination_sound entry
      have evolution : LedgerEntryEvolutionAt N entry (rows.targetEntryAt index) :=
        Eq.mp
          (congrArg
            (fun sourceEntry =>
              LedgerEntryEvolutionAt N sourceEntry (rows.targetEntryAt index))
            source_eq)
          ((rows.rowAt index).evolution)
      exact ⟨rows.targetEntryAt index, evolution⟩
    origin := fun entry => by
      let index := coverage.originIndex entry
      have target_eq := coverage.origin_sound entry
      have evolution : LedgerEntryEvolutionAt N (rows.sourceEntryAt index) entry :=
        Eq.mp
          (congrArg
            (fun targetEntry =>
              LedgerEntryEvolutionAt N (rows.sourceEntryAt index) targetEntry)
            target_eq)
          ((rows.rowAt index).evolution)
      exact ⟨rows.sourceEntryAt index, evolution⟩
  }

/-- Fold finite exceptional rows over one source-generated transported
remainder.  No total map enters through the patch constructor. -/
def transportedRemainderEvolution
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
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (remainder : GeneratedLedgerTransportedRemainderAt
      rowSource occurrence target) :
    LedgerWriteEvolutionAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩ target :=
  {
    destination := fun entry =>
      match coverage.destinationIndex entry with
      | none => remainder.evolution.destination entry
      | some indexed => by
          exact indexed.property ▸
            ⟨rows.targetEntryAt indexed.1, (rows.rowAt indexed.1).evolution⟩
    origin := fun entry =>
      match coverage.originIndex entry with
      | none => remainder.evolution.origin entry
      | some indexed => by
          exact indexed.property ▸
            ⟨rows.sourceEntryAt indexed.1, (rows.rowAt indexed.1).evolution⟩
  }

/-- Fold generated exceptional rows and their selected remainder into the old
total compatibility readout.  No raw total answer table enters the patch. -/
def toLedgerWriteEvolution
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
    (patch : FiniteGeneratedLedgerWritePatchAt rowSource occurrence target) :
    LedgerWriteEvolutionAt N
      ⟨source.toRootSource.account.supportOf occurrence⟩ target :=
  match patch with
  | .identityRemainder rows coverage =>
      identityRemainderEvolution rows coverage
  | .complete rows coverage => completeEvolution rows coverage
  | .transportedRemainder rows coverage remainder =>
      transportedRemainderEvolution rows coverage remainder

@[simp] theorem toLedgerWriteEvolution_identityRemainder
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
    (coverage : LedgerIdentityRemainderCoverageAt rows) :
    toLedgerWriteEvolution
        (FiniteGeneratedLedgerWritePatchAt.identityRemainder rows coverage) =
      identityRemainderEvolution rows coverage :=
  rfl

/-- Static branch readout used to audit a compatibility fold without erasing
the exact dependent endpoints carried by the evolution itself. -/
def ledgerEntryIsTransferred
    {N : WorldRelationNetwork.{u}}
    {sourceSupport targetSupport : N.Support}
    {sourceEntry : OpenResponsibilityAt N sourceSupport}
    {targetEntry : OpenResponsibilityAt N targetSupport} :
    LedgerEntryEvolutionAt N sourceEntry targetEntry → Bool
  | .carried _ _ => false
  | .maintained .. => false
  | .transferred _ _ _ _ => true

/-- An unmentioned destination incidence in an identity-remainder patch is
really carried; it cannot conceal a transfer receipt in the compatibility
readout.  This is a static fold theorem, not renewal authority for the entry. -/
theorem identityRemainder_destination_isNotTransferred
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
    (coverage : LedgerIdentityRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N
      (source.toRootSource.account.supportOf occurrence))
    (index_eq : coverage.destinationIndex entry = none) :
    ledgerEntryIsTransferred
        ((identityRemainderEvolution rows coverage).destination entry).2 = false := by
  dsimp only [identityRemainderEvolution]
  rw [index_eq]
  rfl

end FiniteGeneratedLedgerWritePatchAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
