import H0mework.Chemistry.LAlanineElectronicFrame.RuntimeElectronicFrameSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def electronicFrameWriteRowSource : LedgerWriteRowSourceAt electronicFrameSource (by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = electronicFrameSupport)) where
  IncidenceOccurrenceAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = electronicFrameSupport)
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PLift (support = electronicFrameSupport) at sourceEvent
    cases sourceEvent.down
    cases event.down
    cases entryAt_unique sourceEntry
    cases entryAt_unique targetEntry
    exact .carried rfl HEq.rfl
  compileExact := fun event => event

def electronicFrameOccurrenceEntry {current : ElectronicFrameCurrent}
    (occurrence : electronicFrameSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N occurrence.1 :=
  electronicFrameSource.law.affectedInventoryPresentation occurrence.2 |>.forward ()

def electronicFrameGeneratedRows {current : ElectronicFrameCurrent}
    (occurrence : electronicFrameSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt electronicFrameWriteRowSource occurrence
      (⟨electronicFrameSupport⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => electronicFrameOccurrenceEntry occurrence
  targetEntryAt := fun _ => entryAt electronicFrameSupport
  rowAt := fun _ => electronicFrameWriteRowSource.generate ⟨rfl⟩

def electronicFrameGeneratedCoverage {current : ElectronicFrameCurrent}
    (occurrence : electronicFrameSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (electronicFrameGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change electronicFrameOccurrenceEntry occurrence = entry
    exact (electronicFrameSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (entryAt_unique entry).symm

def electronicFrameGeneratedPatch {current : ElectronicFrameCurrent}
    (occurrence : electronicFrameSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt electronicFrameWriteRowSource occurrence
      (⟨electronicFrameSupport⟩ : CompleteLiveLedgerAt N) :=
  .complete (electronicFrameGeneratedRows occurrence) (electronicFrameGeneratedCoverage occurrence)

def electronicFrameGeneratedEvolution {current : ElectronicFrameCurrent}
    (occurrence : electronicFrameSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt electronicFrameSource occurrence := by
  cases current with
  | ingress =>
      exact SourceNativeLedgerEvolutionAt.nativeWrite (source := electronicFrameSource)
        (occurrence := occurrence) PUnit.unit rfl (electronicFrameEmitted (electronicFrameNext .ingress))
        (electronicFrameGeneratedPatch occurrence).toLedgerWriteEvolution
  | ready held =>
      exact SourceNativeLedgerEvolutionAt.continuedTransport (source := electronicFrameSource)
        (occurrence := occurrence) PUnit.unit rfl (electronicFrameEmitted (.ready held))
        (electronicFrameGeneratedPatch occurrence).toLedgerWriteEvolution

def electronicFrameLedgerCompiler : SourceNativeLedgerCompiler electronicFrameSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = electronicFrameSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := electronicFrameWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := electronicFrameGeneratedEvolution
  compilePatch := by
    intro current occurrence
    cases current <;> exact ⟨electronicFrameGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.ElectronicFrame.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
