import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime
noncomputable section

def reservoirWriteRowSource : LedgerWriteRowSourceAt reservoirSource (by
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

def reservoirOccurrenceEntry {current : ReservoirCurrent}
    (occurrence : reservoirSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt RecoveryN occurrence.1 :=
  reservoirSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def reservoirGeneratedRows {current : ReservoirCurrent}
    (occurrence : reservoirSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt reservoirWriteRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) where
  size := 1
  sourceEntryAt := fun _ => reservoirOccurrenceEntry occurrence
  targetEntryAt := fun _ => recoveryEntry reservoirSupport
  rowAt := fun _ => reservoirWriteRowSource.generate ⟨rfl⟩

def reservoirGeneratedCoverage {current : ReservoirCurrent}
    (occurrence : reservoirSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (reservoirGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change reservoirOccurrenceEntry occurrence = entry
    exact (reservoirSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (recoveryEntry_unique _ entry).symm

def reservoirGeneratedPatch {current : ReservoirCurrent}
    (occurrence : reservoirSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt reservoirWriteRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) :=
  .complete (reservoirGeneratedRows occurrence) (reservoirGeneratedCoverage occurrence)

def reservoirGeneratedEvolution {current : ReservoirCurrent}
    (occurrence : reservoirSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt reservoirSource occurrence :=
  .nativeWrite PUnit.unit rfl (reservoirEmitted (reservoirNext current))
    (reservoirGeneratedPatch occurrence).toLedgerWriteEvolution

def reservoirLedgerCompiler : SourceNativeLedgerCompiler reservoirSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reservoirSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := reservoirWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := reservoirGeneratedEvolution
  compilePatch := fun occurrence => ⟨reservoirGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
