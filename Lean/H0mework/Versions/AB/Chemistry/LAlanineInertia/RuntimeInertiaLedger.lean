import H0mework.Versions.AB.Chemistry.LAlanineInertia.RuntimeInertiaSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def inertiaWriteRowSource : LedgerWriteRowSourceAt inertiaSource (by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = inertiaSupport)) where
  IncidenceOccurrenceAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = inertiaSupport)
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PLift (support = inertiaSupport) at sourceEvent
    cases sourceEvent.down
    cases event.down
    cases entryAt_unique sourceEntry
    cases entryAt_unique targetEntry
    exact .carried rfl HEq.rfl
  compileExact := fun event => event

def inertiaOccurrenceEntry {current : InertiaCurrent}
    (occurrence : inertiaSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N occurrence.1 :=
  inertiaSource.law.affectedInventoryPresentation occurrence.2 |>.forward ()

def inertiaGeneratedRows {current : InertiaCurrent}
    (occurrence : inertiaSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt inertiaWriteRowSource occurrence (⟨inertiaSupport⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => inertiaOccurrenceEntry occurrence
  targetEntryAt := fun _ => entryAt inertiaSupport
  rowAt := fun _ => inertiaWriteRowSource.generate ⟨rfl⟩

def inertiaGeneratedCoverage {current : InertiaCurrent}
    (occurrence : inertiaSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (inertiaGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change inertiaOccurrenceEntry occurrence = entry
    exact (inertiaSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (entryAt_unique entry).symm

def inertiaGeneratedPatch {current : InertiaCurrent}
    (occurrence : inertiaSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt inertiaWriteRowSource occurrence (⟨inertiaSupport⟩ : CompleteLiveLedgerAt N) :=
  .complete (inertiaGeneratedRows occurrence) (inertiaGeneratedCoverage occurrence)

def inertiaGeneratedEvolution {current : InertiaCurrent}
    (occurrence : inertiaSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt inertiaSource occurrence := by
  cases current with
  | ingress =>
    exact .nativeWrite PUnit.unit rfl (inertiaEmitted (inertiaNext .ingress))
      (inertiaGeneratedPatch occurrence).toLedgerWriteEvolution
  | ready material =>
    exact .continuedTransport PUnit.unit rfl (inertiaEmitted (.ready material))
      (inertiaGeneratedPatch occurrence).toLedgerWriteEvolution

def inertiaLedgerCompiler : SourceNativeLedgerCompiler inertiaSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = inertiaSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := inertiaWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := inertiaGeneratedEvolution
  compilePatch := by
    intro current occurrence
    cases current <;> exact ⟨inertiaGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.Inertia.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
