import H0mework.Chemistry.LAlanineReentry.RuntimeRuntimeSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def reentryWriteRowSource : LedgerWriteRowSourceAt reentrySource (by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reentrySupport)) where
  IncidenceOccurrenceAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reentrySupport)
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PLift (support = reentrySupport) at sourceEvent
    cases sourceEvent.down
    cases event.down
    cases entryAt_unique sourceEntry
    cases entryAt_unique targetEntry
    exact .carried rfl HEq.rfl
  compileExact := fun event => event

def reentryOccurrenceEntry {current : ReentryCurrent}
    (occurrence : reentrySource.toRootSource.actual.OccurrenceAt current) : OpenResponsibilityAt N occurrence.1 :=
  reentrySource.law.affectedInventoryPresentation occurrence.2 |>.forward ()

def reentryGeneratedRows {current : ReentryCurrent}
    (occurrence : reentrySource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt reentryWriteRowSource occurrence (⟨reentrySupport⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => reentryOccurrenceEntry occurrence
  targetEntryAt := fun _ => entryAt reentrySupport
  rowAt := fun _ => reentryWriteRowSource.generate ⟨rfl⟩

def reentryGeneratedCoverage {current : ReentryCurrent}
    (occurrence : reentrySource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (reentryGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change reentryOccurrenceEntry occurrence = entry
    exact (reentrySource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (entryAt_unique entry).symm

def reentryGeneratedPatch {current : ReentryCurrent}
    (occurrence : reentrySource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt reentryWriteRowSource occurrence (⟨reentrySupport⟩ : CompleteLiveLedgerAt N) :=
  .complete (reentryGeneratedRows occurrence) (reentryGeneratedCoverage occurrence)

def reentryGeneratedEvolution {current : ReentryCurrent}
    (occurrence : reentrySource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt reentrySource occurrence := by
  cases current with
  | ingress =>
      exact SourceNativeLedgerEvolutionAt.nativeWrite (source := reentrySource)
        (occurrence := occurrence) PUnit.unit rfl (reentryEmitted (reentryNext .ingress))
        (reentryGeneratedPatch occurrence).toLedgerWriteEvolution
  | ready result =>
      exact SourceNativeLedgerEvolutionAt.continuedTransport (source := reentrySource)
        (occurrence := occurrence) PUnit.unit rfl (reentryEmitted (.ready result))
        (reentryGeneratedPatch occurrence).toLedgerWriteEvolution

def reentryLedgerCompiler : SourceNativeLedgerCompiler reentrySource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = reentrySupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := reentryWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := reentryGeneratedEvolution
  compilePatch := by
    intro current occurrence
    cases current <;> exact ⟨reentryGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
