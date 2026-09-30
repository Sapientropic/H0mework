import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.GeneratedRows

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def Presentation.finiteRows {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    (rows : FiniteGeneratedLedgerWriteRowsAt compiler.writeRowSource event ⟨target⟩) :
    FiniteGeneratedLedgerWriteRowsAt (p.writeRowSource compiler) (p.eventEquiv source current event)
      ⟨p.support target⟩ where
  size := rows.size
  sourceEntryAt := fun i => p.ledger event.1 (rows.sourceEntryAt i)
  targetEntryAt := fun i => p.ledger target (rows.targetEntryAt i)
  rowAt := fun i => p.writeRow compiler (rows.rowAt i)

/-- The original chosen index is retained, including `none` and duplicate
stored rows. Only its dependent endpoint equality is transported. -/
def mapSelection {A B : Type} {k : Nat} (e : A ≃ B) (entryAt : Fin k → A)
    (selection : (a : A) → Option {i : Fin k // entryAt i = a}) (b : B) :
    Option {i : Fin k // e (entryAt i) = b} :=
  Equiv.piCongrLeft (fun b => Option {i : Fin k // e (entryAt i) = b}) e (fun a => (selection a).map
    (fun i => ⟨i.val, congrArg e i.property⟩)) b

theorem mapSelection_at {A B : Type} {k : Nat} (e : A ≃ B) (entryAt : Fin k → A)
    (selection : (a : A) → Option {i : Fin k // entryAt i = a}) (a : A) :
    mapSelection e entryAt selection (e a) =
      (selection a).map (fun i => ⟨i.val, congrArg e i.property⟩) :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem mapSelection_index {A B : Type} {k : Nat} (e : A ≃ B) (entryAt : Fin k → A)
    (selection : (a : A) → Option {i : Fin k // entryAt i = a}) (a : A) :
    (mapSelection e entryAt selection (e a)).map Subtype.val = (selection a).map Subtype.val := by
  simp only [mapSelection_at, Option.map_map]
  rfl

def Presentation.identityCoverage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current}
    {rows : FiniteGeneratedLedgerWriteRowsAt compiler.writeRowSource event ⟨event.1⟩}
    (coverage : LedgerIdentityRemainderCoverageAt rows) :
    LedgerIdentityRemainderCoverageAt (p.finiteRows compiler rows) where
  destinationIndex := mapSelection (p.ledger event.1) rows.sourceEntryAt coverage.destinationIndex
  originIndex := mapSelection (p.ledger event.1) rows.targetEntryAt coverage.originIndex

def Presentation.remainderCoverage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    {rows : FiniteGeneratedLedgerWriteRowsAt compiler.writeRowSource event ⟨target⟩}
    (coverage : LedgerTransportedRemainderCoverageAt rows) :
    LedgerTransportedRemainderCoverageAt (p.finiteRows compiler rows) where
  destinationIndex := mapSelection (p.ledger event.1) rows.sourceEntryAt coverage.destinationIndex
  originIndex := mapSelection (p.ledger target) rows.targetEntryAt coverage.originIndex

def Presentation.completeCoverage {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : N.Support}
    {rows : FiniteGeneratedLedgerWriteRowsAt compiler.writeRowSource event ⟨target⟩}
    (coverage : LedgerCompleteFiniteCoverageAt rows) :
    LedgerCompleteFiniteCoverageAt (p.finiteRows compiler rows) where
  destinationIndex := fun entry => coverage.destinationIndex ((p.ledger event.1).symm entry)
  originIndex := fun entry => coverage.originIndex ((p.ledger target).symm entry)
  destination_sound := fun entry =>
    (congrArg (p.ledger event.1) (coverage.destination_sound ((p.ledger event.1).symm entry))).trans
      ((p.ledger event.1).apply_symm_apply entry)
  origin_sound := fun entry =>
    (congrArg (p.ledger target) (coverage.origin_sound ((p.ledger target).symm entry))).trans
      ((p.ledger target).apply_symm_apply entry)

def Presentation.writePatch {N G : WorldRelationNetwork.{0}} (p : Presentation N G)
    {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) {current : V.Current}
    {event : source.toRootSource.actual.OccurrenceAt current} {target : CompleteLiveLedgerAt N}
    (patch : FiniteGeneratedLedgerWritePatchAt compiler.writeRowSource event target) :
    FiniteGeneratedLedgerWritePatchAt (p.writeRowSource compiler) (p.eventEquiv source current event)
      ⟨p.support target.support⟩ := by
  cases patch with
  | identityRemainder rows coverage =>
      exact .identityRemainder (p.finiteRows compiler rows) (p.identityCoverage compiler coverage)
  | complete rows coverage =>
      exact .complete (p.finiteRows compiler rows) (p.completeCoverage compiler coverage)
  | transportedRemainder rows coverage remainder =>
      exact .transportedRemainder (p.finiteRows compiler rows) (p.remainderCoverage compiler coverage)
        (p.remainder compiler remainder)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
