import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime
noncomputable section

def pointerWriteRowSource : LedgerWriteRowSourceAt pointerSource (by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reservoirSupport)) where
  IncidenceOccurrenceAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reservoirSupport)
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PLift (support = reservoirSupport) at sourceEvent
    cases sourceEvent.down
    cases event.down
    cases recoveryEntry_unique _ sourceEntry
    cases recoveryEntry_unique _ targetEntry
    exact .carried rfl HEq.rfl
  compileExact := fun event => event

def pointerOccurrenceEntry {current : PointerCurrent}
    (occurrence : pointerSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt RecoveryN occurrence.1 :=
  pointerSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def pointerGeneratedRows {current : PointerCurrent}
    (occurrence : pointerSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt pointerWriteRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) where
  size := 1
  sourceEntryAt := fun _ => pointerOccurrenceEntry occurrence
  targetEntryAt := fun _ => recoveryEntry reservoirSupport
  rowAt := fun _ => pointerWriteRowSource.generate ⟨rfl⟩

def pointerGeneratedCoverage {current : PointerCurrent}
    (occurrence : pointerSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (pointerGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change pointerOccurrenceEntry occurrence = entry
    exact (pointerSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (recoveryEntry_unique _ entry).symm

def pointerGeneratedPatch {current : PointerCurrent}
    (occurrence : pointerSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt pointerWriteRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) :=
  .complete (pointerGeneratedRows occurrence) (pointerGeneratedCoverage occurrence)

def pointerGeneratedEvolution {current : PointerCurrent}
    (occurrence : pointerSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt pointerSource occurrence :=
  .nativeWrite PUnit.unit rfl (pointerEmitted (pointerNext current))
    (pointerGeneratedPatch occurrence).toLedgerWriteEvolution

def pointerLedgerCompiler : SourceNativeLedgerCompiler pointerSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reservoirSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := pointerWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := pointerGeneratedEvolution
  compilePatch := fun occurrence => ⟨pointerGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
