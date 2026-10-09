import H0mework.Versions.R9c73a630.Chemistry.LAlanineWork.FieldActionWorld

/-! # The existing ledger compiler receives source-generated field updates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def fieldVocabulary : ConstructiveRoot.Vocabulary where
  Current := FieldCurrent
  Anchor := FieldN.Anchor
  Incidence := FieldSupport
  Lineage := FieldN.Lineage
  anchorAt := fun _ => Source.key
  incidenceAt := fieldCurrentSupport
  lineageAt := fun _ => Source.key
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => fieldNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev FieldV := fieldVocabulary

structure FieldEventAt (current : FieldCurrent) (support : FieldSupport) : Type where
  supportExact : support = fieldCurrentSupport current

def fieldEventLaw : SourceNativeEventAlgebra FieldN FieldV where
  EventAt := FieldEventAt
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.supportExact
    exact fieldInventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.supportExact.symm
  lineage_commutes := fun _ => rfl

def fieldSource : SourceNativeSource FieldN FieldV where
  initial := .ingress
  law := fieldEventLaw

def fieldEmitted (current : FieldCurrent) : fieldSource.toRootSource.actual.OccurrenceAt current :=
  ⟨fieldCurrentSupport current, ⟨rfl⟩⟩

structure FieldExactTransitionAt (current : FieldCurrent) (support : FieldSupport) : Type where
  targetExact : support = fieldCurrentSupport (fieldNext current)

def fieldWriteRowSource : LedgerWriteRowSourceAt fieldSource (by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact FieldExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact FieldExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change FieldEventAt current support at sourceEvent
    cases sourceEvent.supportExact
    cases event.targetExact
    cases fieldEntry_unique _ sourceEntry
    cases fieldEntry_unique _ targetEntry
    cases current
    all_goals exact .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  compileExact := fun event => event

def fieldOccurrenceEntry {current : FieldCurrent}
    (occurrence : fieldSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt FieldN occurrence.1 :=
  fieldSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def fieldGeneratedRows {current : FieldCurrent}
    (occurrence : fieldSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt fieldWriteRowSource occurrence
      (⟨fieldCurrentSupport (fieldNext current)⟩ : CompleteLiveLedgerAt FieldN) where
  size := 1
  sourceEntryAt := fun _ => fieldOccurrenceEntry occurrence
  targetEntryAt := fun _ => fieldEntry (fieldCurrentSupport (fieldNext current))
  rowAt := fun _ => fieldWriteRowSource.generate ⟨rfl⟩

def fieldGeneratedCoverage {current : FieldCurrent}
    (occurrence : fieldSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (fieldGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change fieldOccurrenceEntry occurrence = entry
    exact (fieldSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (fieldEntry_unique _ entry).symm

def fieldGeneratedPatch {current : FieldCurrent}
    (occurrence : fieldSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt fieldWriteRowSource occurrence
      (⟨fieldCurrentSupport (fieldNext current)⟩ : CompleteLiveLedgerAt FieldN) :=
  .complete (fieldGeneratedRows occurrence) (fieldGeneratedCoverage occurrence)

def fieldGeneratedEvolution {current : FieldCurrent}
    (occurrence : fieldSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt fieldSource occurrence :=
  .nativeWrite PUnit.unit rfl (fieldEmitted (fieldNext current))
    (fieldGeneratedPatch occurrence).toLedgerWriteEvolution

def fieldLedgerCompiler : SourceNativeLedgerCompiler fieldSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact FieldExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := fieldWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := fieldGeneratedEvolution
  compilePatch := fun occurrence => ⟨fieldGeneratedPatch occurrence, rfl⟩

end

end LAlanine40K2025.Thermal.Work.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
