import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadActionWorld

/-! # The existing ledger compiler receives source-generated load updates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def loadVocabulary : ConstructiveRoot.Vocabulary where
  Current := LoadCurrent
  Anchor := LoadN.Anchor
  Incidence := LoadSupport
  Lineage := LoadN.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := loadCurrentSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => loadNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev LoadV := loadVocabulary

structure LoadEventAt (current : LoadCurrent) (support : LoadSupport) : Type where
  supportExact : support = loadCurrentSupport current

def loadEventLaw : SourceNativeEventAlgebra LoadN LoadV where
  EventAt := LoadEventAt
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.supportExact
    exact loadInventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.supportExact.symm
  lineage_commutes := fun _ => rfl

def loadSource : SourceNativeSource LoadN LoadV where
  initial := .ingress
  law := loadEventLaw

def loadEmitted (current : LoadCurrent) : loadSource.toRootSource.actual.OccurrenceAt current :=
  ⟨loadCurrentSupport current, ⟨rfl⟩⟩

structure LoadExactTransitionAt (current : LoadCurrent) (support : LoadSupport) : Type where
  targetExact : support = loadCurrentSupport (loadNext current)

def loadWriteRowSource : LedgerWriteRowSourceAt loadSource (by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact LoadExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact LoadExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change LoadEventAt current support at sourceEvent
    cases sourceEvent.supportExact
    cases event.targetExact
    cases loadEntry_unique _ sourceEntry
    cases loadEntry_unique _ targetEntry
    cases current
    all_goals exact .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  compileExact := fun event => event

def loadOccurrenceEntry {current : LoadCurrent}
    (occurrence : loadSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt LoadN occurrence.1 :=
  loadSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def loadGeneratedRows {current : LoadCurrent}
    (occurrence : loadSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt loadWriteRowSource occurrence
      (⟨loadCurrentSupport (loadNext current)⟩ : CompleteLiveLedgerAt LoadN) where
  size := 1
  sourceEntryAt := fun _ => loadOccurrenceEntry occurrence
  targetEntryAt := fun _ => loadEntry (loadCurrentSupport (loadNext current))
  rowAt := fun _ => loadWriteRowSource.generate ⟨rfl⟩

def loadGeneratedCoverage {current : LoadCurrent}
    (occurrence : loadSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (loadGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change loadOccurrenceEntry occurrence = entry
    exact (loadSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (loadEntry_unique _ entry).symm

def loadGeneratedPatch {current : LoadCurrent}
    (occurrence : loadSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt loadWriteRowSource occurrence
      (⟨loadCurrentSupport (loadNext current)⟩ : CompleteLiveLedgerAt LoadN) :=
  .complete (loadGeneratedRows occurrence) (loadGeneratedCoverage occurrence)

def loadGeneratedEvolution {current : LoadCurrent}
    (occurrence : loadSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt loadSource occurrence :=
  .nativeWrite PUnit.unit rfl (loadEmitted (loadNext current))
    (loadGeneratedPatch occurrence).toLedgerWriteEvolution

def loadLedgerCompiler : SourceNativeLedgerCompiler loadSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact LoadExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := loadWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := loadGeneratedEvolution
  compilePatch := fun occurrence => ⟨loadGeneratedPatch occurrence, rfl⟩

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
