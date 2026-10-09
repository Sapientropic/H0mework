import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime.World

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open scoped ComplexOrder MatrixOrder
noncomputable section

def writeRowSource : LedgerWriteRowSourceAt source (by
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

def occurrenceEntry {current : State}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt RecoveryN occurrence.1 :=
  source.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def generatedRows {current : State}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt writeRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) where
  size := 1
  sourceEntryAt := fun _ => occurrenceEntry occurrence
  targetEntryAt := fun _ => recoveryEntry reservoirSupport
  rowAt := fun _ => writeRowSource.generate ⟨rfl⟩

def generatedCoverage {current : State}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (generatedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change occurrenceEntry occurrence = entry
    exact (source.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (recoveryEntry_unique _ entry).symm

def generatedPatch {current : State}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) :=
  .complete (generatedRows occurrence) (generatedCoverage occurrence)

def generatedEvolution {current : State}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt source occurrence :=
  SourceNativeLedgerEvolutionAt.nativeWrite (source := source) (occurrence := occurrence)
    PUnit.unit rfl (emitted (nextState current)) (generatedPatch occurrence).toLedgerWriteEvolution

def ledgerCompiler : SourceNativeLedgerCompiler source where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reservoirSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := generatedEvolution
  compilePatch := by
    intro current occurrence
    exact ⟨generatedPatch occurrence,rfl⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
