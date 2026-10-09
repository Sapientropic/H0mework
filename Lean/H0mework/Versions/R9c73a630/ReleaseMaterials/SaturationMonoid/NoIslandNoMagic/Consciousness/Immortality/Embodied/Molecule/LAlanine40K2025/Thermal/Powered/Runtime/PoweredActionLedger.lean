import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Runtime.PoweredActionWorld

/-! # The existing ledger compiler receives source-generated powered updates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def poweredVocabulary : ConstructiveRoot.Vocabulary where
  Current := PoweredCurrent
  Anchor := PoweredN.Anchor
  Incidence := PoweredSupport
  Lineage := PoweredN.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := poweredCurrentSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => poweredNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev PoweredV := poweredVocabulary

structure PoweredEventAt (current : PoweredCurrent) (support : PoweredSupport) : Type where
  supportExact : support = poweredCurrentSupport current

def poweredEventLaw : SourceNativeEventAlgebra PoweredN PoweredV where
  EventAt := PoweredEventAt
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.supportExact
    exact poweredInventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.supportExact.symm
  lineage_commutes := fun _ => rfl

def poweredSource : SourceNativeSource PoweredN PoweredV where
  initial := .ingress
  law := poweredEventLaw

def poweredEmitted (current : PoweredCurrent) : poweredSource.toRootSource.actual.OccurrenceAt current :=
  ⟨poweredCurrentSupport current, ⟨rfl⟩⟩

structure PoweredExactTransitionAt (current : PoweredCurrent) (support : PoweredSupport) : Type where
  targetExact : support = poweredCurrentSupport (poweredNext current)

def poweredWriteRowSource : LedgerWriteRowSourceAt poweredSource (by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact PoweredExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact PoweredExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PoweredEventAt current support at sourceEvent
    cases sourceEvent.supportExact
    cases event.targetExact
    cases poweredEntry_unique _ sourceEntry
    cases poweredEntry_unique _ targetEntry
    cases current
    all_goals exact .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  compileExact := fun event => event

def poweredOccurrenceEntry {current : PoweredCurrent}
    (occurrence : poweredSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt PoweredN occurrence.1 :=
  poweredSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def poweredGeneratedRows {current : PoweredCurrent}
    (occurrence : poweredSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt poweredWriteRowSource occurrence
      (⟨poweredCurrentSupport (poweredNext current)⟩ : CompleteLiveLedgerAt PoweredN) where
  size := 1
  sourceEntryAt := fun _ => poweredOccurrenceEntry occurrence
  targetEntryAt := fun _ => poweredEntry (poweredCurrentSupport (poweredNext current))
  rowAt := fun _ => poweredWriteRowSource.generate ⟨rfl⟩

def poweredGeneratedCoverage {current : PoweredCurrent}
    (occurrence : poweredSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (poweredGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change poweredOccurrenceEntry occurrence = entry
    exact (poweredSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (poweredEntry_unique _ entry).symm

def poweredGeneratedPatch {current : PoweredCurrent}
    (occurrence : poweredSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt poweredWriteRowSource occurrence
      (⟨poweredCurrentSupport (poweredNext current)⟩ : CompleteLiveLedgerAt PoweredN) :=
  .complete (poweredGeneratedRows occurrence) (poweredGeneratedCoverage occurrence)

def poweredGeneratedEvolution {current : PoweredCurrent}
    (occurrence : poweredSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt poweredSource occurrence :=
  .nativeWrite PUnit.unit rfl (poweredEmitted (poweredNext current))
    (poweredGeneratedPatch occurrence).toLedgerWriteEvolution

def poweredLedgerCompiler : SourceNativeLedgerCompiler poweredSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact PoweredExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := poweredWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := poweredGeneratedEvolution
  compilePatch := fun occurrence => ⟨poweredGeneratedPatch occurrence, rfl⟩

end

end LAlanine40K2025.Thermal.Powered.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
