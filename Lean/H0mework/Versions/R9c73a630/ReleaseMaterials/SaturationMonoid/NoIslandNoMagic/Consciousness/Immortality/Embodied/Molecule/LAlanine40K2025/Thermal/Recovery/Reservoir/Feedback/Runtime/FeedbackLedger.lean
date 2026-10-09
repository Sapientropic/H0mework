import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime
noncomputable section

def feedbackWriteRowSource : LedgerWriteRowSourceAt feedbackSource (by
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

def feedbackOccurrenceEntry {current : FeedbackCurrent}
    (occurrence : feedbackSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt RecoveryN occurrence.1 :=
  feedbackSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def feedbackGeneratedRows {current : FeedbackCurrent}
    (occurrence : feedbackSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt feedbackWriteRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) where
  size := 1
  sourceEntryAt := fun _ => feedbackOccurrenceEntry occurrence
  targetEntryAt := fun _ => recoveryEntry reservoirSupport
  rowAt := fun _ => feedbackWriteRowSource.generate ⟨rfl⟩

def feedbackGeneratedCoverage {current : FeedbackCurrent}
    (occurrence : feedbackSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (feedbackGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change feedbackOccurrenceEntry occurrence = entry
    exact (feedbackSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (recoveryEntry_unique _ entry).symm

def feedbackGeneratedPatch {current : FeedbackCurrent}
    (occurrence : feedbackSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt feedbackWriteRowSource occurrence
      (⟨reservoirSupport⟩ : CompleteLiveLedgerAt RecoveryN) :=
  .complete (feedbackGeneratedRows occurrence) (feedbackGeneratedCoverage occurrence)

def feedbackGeneratedEvolution {current : FeedbackCurrent}
    (occurrence : feedbackSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt feedbackSource occurrence :=
  .nativeWrite PUnit.unit rfl (feedbackEmitted (feedbackNext current))
    (feedbackGeneratedPatch occurrence).toLedgerWriteEvolution

def feedbackLedgerCompiler : SourceNativeLedgerCompiler feedbackSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reservoirSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := feedbackWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := feedbackGeneratedEvolution
  compilePatch := fun occurrence => ⟨feedbackGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
