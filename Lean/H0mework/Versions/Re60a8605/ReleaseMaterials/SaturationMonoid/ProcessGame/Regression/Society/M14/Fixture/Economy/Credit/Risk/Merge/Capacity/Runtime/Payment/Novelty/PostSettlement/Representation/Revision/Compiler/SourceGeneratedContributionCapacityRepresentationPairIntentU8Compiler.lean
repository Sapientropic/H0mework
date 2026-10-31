import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Revision.Lifecycle.SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle

/-!
# Pair-intent U8 whole-ledger compiler

The revised root runs on the canonical minimal coface.  Its complete ledger
has four rows: the three inherited target rows through `cofaceLedgerRetract`
and the single generated obstruction entry.  Every native write carries all
four rows through one complete finite patch.  No total answer table or second
ledger is retained.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ComplementObservation Lifecycle Universal Relations Exchange
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle

def representationIntentU8NativeTarget : Bool → Bool
  | false => true
  | true => true

def representationIntentU8Vocabulary
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructiveRoot.Vocabulary where
  Current := Bool
  Anchor := (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Anchor
  Incidence :=
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Incidence
  Lineage := (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Lineage
  anchorAt := fun _ =>
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).anchorAt
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).cofaceSupport
  incidenceAt := fun _ =>
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).incidenceAt
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).cofaceSupport
  lineageAt := fun _ =>
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).lineageAt
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).cofaceSupport
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => representationIntentU8NativeTarget current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev RepresentationIntentU8VAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  representationIntentU8Vocabulary oldVisit sourceIndex boundary

structure SourceGeneratedRepresentationIntentU8EventAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (current : Bool)
    (support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support) :
    Type where
  private mk ::
  supportExact : PLift
    (support =
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).cofaceSupport)
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness

def representationIntentU8EventLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeEventAlgebra
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) where
  EventAt := SourceGeneratedRepresentationIntentU8EventAt oldVisit sourceIndex
    boundary
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_} {support} _ =>
    OpenResponsibilityAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) support
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event.supportExact.down
    rfl
  incidence_commutes := by
    intro current support event
    cases event.supportExact.down
    rfl
  lineage_commutes := by
    intro current support event
    cases event.supportExact.down
    rfl

def representationIntentU8Source
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeSource
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) where
  initial := false
  law := representationIntentU8EventLaw oldVisit sourceIndex boundary

def representationIntentU8Emitted
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (current : Bool) :
    (representationIntentU8Source oldVisit sourceIndex boundary
      ).toRootSource.actual.OccurrenceAt current :=
  ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary).cofaceSupport,
    ⟨PLift.up rfl, exactSourceGeneratedLossAllocationMaterialWitness, rfl⟩⟩

theorem representationIntentU8Occurrence_eq_emitted
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    occurrence = representationIntentU8Emitted oldVisit sourceIndex boundary
      current := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  cases event.materialExact
  cases event
  rfl

def representationIntentU8Ledger
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    CompleteLiveLedgerAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) :=
  ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary).cofaceSupport⟩

def representationIntentU8InheritedEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (index : Fin 3) :
    (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry :=
  (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
    ).cofaceLedgerRetract.forward
      (representationIntentEntryAt oldVisit sourceIndex boundary index)

def representationIntentU8GeneratedEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry :=
  (RepresentationIntentCofaceAt oldVisit sourceIndex boundary).obstructionEntry

def representationIntentU8EntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Fin 4 → (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry :=
  Fin.lastCases
    (representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary)
    (representationIntentU8InheritedEntryAt oldVisit sourceIndex boundary)

def representationIntentU8EntryIndex
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry → Fin 4
  | ⟨.inl oldResponsibility, isOpen⟩ =>
      Fin.castSucc
        (representationIntentEntryIndex oldVisit sourceIndex boundary
          ⟨oldResponsibility, isOpen⟩)
  | ⟨.inr _direction, _aligned⟩ => Fin.last 3

@[simp] theorem representationIntentU8EntryAt_inherited
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (index : Fin 3) :
    representationIntentU8EntryAt oldVisit sourceIndex boundary
        (Fin.castSucc index) =
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
        ).cofaceLedgerRetract.forward
        (representationIntentEntryAt oldVisit sourceIndex boundary index) := by
  unfold representationIntentU8EntryAt
  rw [Fin.lastCases_castSucc]
  rfl

@[simp] theorem representationIntentU8EntryAt_generated
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    representationIntentU8EntryAt oldVisit sourceIndex boundary (Fin.last 3) =
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
        ).obstructionEntry := by
  unfold representationIntentU8EntryAt
  rw [Fin.lastCases_last]
  rfl

theorem representationIntentU8EntryAt_index
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (entry : (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry) :
    representationIntentU8EntryAt oldVisit sourceIndex boundary
        (representationIntentU8EntryIndex oldVisit sourceIndex boundary entry) =
      entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      have oldEntryEq := representationIntentEntryAt_index oldVisit sourceIndex
        boundary (⟨oldResponsibility, isOpen⟩ :
          (RepresentationIntentLedgerAt oldVisit sourceIndex boundary).Entry)
      simp only [representationIntentU8EntryIndex,
        representationIntentU8EntryAt, Fin.lastCases_castSucc]
      unfold representationIntentU8InheritedEntryAt
      rw [oldEntryEq]
      rfl
  | inr direction =>
      cases direction
      cases isOpen
      simp only [representationIntentU8EntryIndex,
        representationIntentU8EntryAt, Fin.lastCases_last]
      rfl

def RepresentationIntentU8ExactTransitionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    {current : Bool} →
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) →
    {targetSupport :
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support} →
    OpenResponsibilityAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      ((representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) targetSupport →
      Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) sourceEntry
      targetEntry

def representationIntentU8WriteRowSource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    LedgerWriteRowSourceAt
      (representationIntentU8Source oldVisit sourceIndex boundary)
      (RepresentationIntentU8ExactTransitionAt oldVisit sourceIndex boundary) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) sourceEntry
      targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

def representationIntentU8Rows
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt
      (representationIntentU8WriteRowSource oldVisit sourceIndex boundary)
      occurrence (representationIntentU8Ledger oldVisit sourceIndex boundary) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact
    { size := 4
      sourceEntryAt :=
        representationIntentU8EntryAt oldVisit sourceIndex boundary
      targetEntryAt :=
        representationIntentU8EntryAt oldVisit sourceIndex boundary
      rowAt := fun _ =>
        (representationIntentU8WriteRowSource oldVisit sourceIndex boundary
          ).generate (.carried rfl HEq.rfl) }

def representationIntentU8Patch
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt
      (representationIntentU8WriteRowSource oldVisit sourceIndex boundary)
      occurrence (representationIntentU8Ledger oldVisit sourceIndex boundary) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact .complete
    (representationIntentU8Rows oldVisit sourceIndex boundary
      ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
        ).cofaceSupport, event⟩)
    { destinationIndex :=
        representationIntentU8EntryIndex oldVisit sourceIndex boundary
      originIndex :=
        representationIntentU8EntryIndex oldVisit sourceIndex boundary
      destination_sound :=
        representationIntentU8EntryAt_index oldVisit sourceIndex boundary
      origin_sound :=
        representationIntentU8EntryAt_index oldVisit sourceIndex boundary }

def representationIntentU8Evolution
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    LedgerWriteEvolutionAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (representationIntentU8Ledger oldVisit sourceIndex boundary)
      (representationIntentU8Ledger oldVisit sourceIndex boundary) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact (representationIntentU8Patch oldVisit sourceIndex boundary
    ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
      ).cofaceSupport, event⟩).toLedgerWriteEvolution

@[simp] theorem representationIntentU8Evolution_destination
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current)
    (entry : (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry) :
    ((representationIntentU8Evolution oldVisit sourceIndex boundary occurrence
      ).destination entry).1 = entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  change representationIntentU8EntryAt oldVisit sourceIndex boundary
      (representationIntentU8EntryIndex oldVisit sourceIndex boundary entry) =
    entry
  exact representationIntentU8EntryAt_index oldVisit sourceIndex boundary entry

@[simp] theorem representationIntentU8Evolution_origin
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current)
    (entry : (representationIntentU8Ledger oldVisit sourceIndex boundary).Entry) :
    ((representationIntentU8Evolution oldVisit sourceIndex boundary occurrence
      ).origin entry).1 = entry := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  change representationIntentU8EntryAt oldVisit sourceIndex boundary
      (representationIntentU8EntryIndex oldVisit sourceIndex boundary entry) =
    entry
  exact representationIntentU8EntryAt_index oldVisit sourceIndex boundary entry

def representationIntentU8LedgerCompiler
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLedgerCompiler
      (representationIntentU8Source oldVisit sourceIndex boundary) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt :=
    RepresentationIntentU8ExactTransitionAt oldVisit sourceIndex boundary
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := by
    intro current occurrence targetSupport sourceEntry targetEntry evolution
    cases evolution with
    | carried support_eq entry_eq =>
        cases support_eq
        cases entry_eq
        rfl
    | maintained _ _ lineage_eq _ _ _ => exact lineage_eq
    | transferred _ lineage_eq _ _ => exact lineage_eq
  writeRowSource :=
    representationIntentU8WriteRowSource oldVisit sourceIndex boundary
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (representationIntentU8Source oldVisit sourceIndex boundary)
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact .nativeWrite PUnit.unit rfl
      (representationIntentU8Emitted oldVisit sourceIndex boundary
        (representationIntentU8NativeTarget current))
      (representationIntentU8Evolution oldVisit sourceIndex boundary
        ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
          ).cofaceSupport, event⟩)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.supportExact.down
    exact ⟨representationIntentU8Patch oldVisit sourceIndex boundary
      ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
        ).cofaceSupport, event⟩, rfl⟩

theorem representationIntentU8Compiler_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (current : Bool) :
    SourceNativeLedgerEvolutionAt.CommutesWith
      (representationIntentU8Emitted oldVisit sourceIndex boundary)
      ((representationIntentU8LedgerCompiler oldVisit sourceIndex boundary
        ).compile
          (representationIntentU8Emitted oldVisit sourceIndex boundary current)) := by
  cases current <;> rfl

def representationIntentU8RestructuringVocabulary
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    RestructuringVocabulary where
  base := RepresentationIntentU8LifecycleV oldVisit sourceIndex boundary
  DescendantAt := fun _ parentIncidence parentContent childIncidence
      childContent =>
    PLift (parentIncidence = childIncidence) ×
      PLift (parentContent = childContent)
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ parentContent childContent =>
    PLift (parentContent = childContent)
  RenameAt := fun _ oldContent newContent => PLift (oldContent = newContent)

def representationIntentU8RestructuringLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLedgerRestructuringLaw
      (representationIntentU8Source oldVisit sourceIndex boundary) where
  vocabulary :=
    representationIntentU8RestructuringVocabulary oldVisit sourceIndex boundary
  sourceEventAt := fun occurrence =>
    ((representationIntentU8Source oldVisit sourceIndex boundary
      ).toRootSource.account.supportOf occurrence,
      occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence support entry
    exact representationIntentU8ObligationAt oldVisit sourceIndex boundary
      occurrence.2.materialWitness entry
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by intros; rfl
  anchor_commutes := by intros; rfl
  incidence_commutes := by intros; rfl
  lineage_commutes := by intros; rfl
  obligationAt_injective := by
    intro current occurrence support left right obligation_eq
    exact representationIntentU8ObligationAt_injective oldVisit sourceIndex
      boundary occurrence.2.materialWitness obligation_eq

def representationIntentU8RestructuringCertification
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : Bool}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (representationIntentU8RestructuringLaw oldVisit sourceIndex boundary)
      ((representationIntentU8LedgerCompiler oldVisit sourceIndex boundary
        ).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right origin_eq =>
      (representationIntentU8Evolution_origin oldVisit sourceIndex boundary
        ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
          ).cofaceSupport, event⟩ left).symm.trans
        (origin_eq.trans
          (representationIntentU8Evolution_origin oldVisit sourceIndex boundary
            ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
              ).cofaceSupport, event⟩ right)))
    (fun left right destination_eq =>
      (representationIntentU8Evolution_destination oldVisit sourceIndex boundary
        ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
          ).cofaceSupport, event⟩ left).symm.trans
        (destination_eq.trans
          (representationIntentU8Evolution_destination oldVisit sourceIndex
            boundary
            ⟨(RepresentationIntentCofaceAt oldVisit sourceIndex boundary
              ).cofaceSupport, event⟩ right)))

def representationIntentU8RestructuringCompiler
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRestructuringLedgerCompiler
      (representationIntentU8Source oldVisit sourceIndex boundary) where
  ledgerCompiler :=
    representationIntentU8LedgerCompiler oldVisit sourceIndex boundary
  restructuringLaw :=
    representationIntentU8RestructuringLaw oldVisit sourceIndex boundary
  certifyRestructuring :=
    representationIntentU8RestructuringCertification oldVisit sourceIndex
      boundary

def representationIntentU8RestructuringSource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeRestructuringLedgerSource
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) where
  source := representationIntentU8Source oldVisit sourceIndex boundary
  compiler := representationIntentU8RestructuringCompiler oldVisit sourceIndex
    boundary

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler.representationIntentU8EntryAt_index
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler.representationIntentU8LedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler.representationIntentU8RestructuringSource
