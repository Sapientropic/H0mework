import H0mework.Versions.AB.Chemistry.LAlanineHeldForce.RuntimeHeldForceSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def heldForceWriteRowSource : LedgerWriteRowSourceAt heldForceSource (by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = heldForceSupport)) where
  IncidenceOccurrenceAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = heldForceSupport)
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PLift (support = heldForceSupport) at sourceEvent
    cases sourceEvent.down
    cases event.down
    cases entryAt_unique sourceEntry
    cases entryAt_unique targetEntry
    exact .carried rfl HEq.rfl
  compileExact := fun event => event

def heldForceOccurrenceEntry {current : HeldForceCurrent}
    (occurrence : heldForceSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N occurrence.1 :=
  heldForceSource.law.affectedInventoryPresentation occurrence.2 |>.forward ()

def heldForceGeneratedRows {current : HeldForceCurrent}
    (occurrence : heldForceSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt heldForceWriteRowSource occurrence
      (⟨heldForceSupport⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => heldForceOccurrenceEntry occurrence
  targetEntryAt := fun _ => entryAt heldForceSupport
  rowAt := fun _ => heldForceWriteRowSource.generate ⟨rfl⟩

def heldForceGeneratedCoverage {current : HeldForceCurrent}
    (occurrence : heldForceSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (heldForceGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change heldForceOccurrenceEntry occurrence = entry
    exact (heldForceSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (entryAt_unique entry).symm

def heldForceGeneratedPatch {current : HeldForceCurrent}
    (occurrence : heldForceSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt heldForceWriteRowSource occurrence
      (⟨heldForceSupport⟩ : CompleteLiveLedgerAt N) :=
  .complete (heldForceGeneratedRows occurrence) (heldForceGeneratedCoverage occurrence)

def heldForceGeneratedEvolution {current : HeldForceCurrent}
    (occurrence : heldForceSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt heldForceSource occurrence := by
  cases current with
  | ingress =>
      exact SourceNativeLedgerEvolutionAt.nativeWrite (source := heldForceSource)
        (occurrence := occurrence) PUnit.unit rfl (heldForceEmitted (heldForceNext .ingress))
        (heldForceGeneratedPatch occurrence).toLedgerWriteEvolution
  | ready response =>
      exact SourceNativeLedgerEvolutionAt.continuedTransport (source := heldForceSource)
        (occurrence := occurrence) PUnit.unit rfl (heldForceEmitted (.ready response))
        (heldForceGeneratedPatch occurrence).toLedgerWriteEvolution

def heldForceLedgerCompiler : SourceNativeLedgerCompiler heldForceSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = heldForceSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := heldForceWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := heldForceGeneratedEvolution
  compilePatch := by
    intro current occurrence
    cases current <;> exact ⟨heldForceGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.HeldForce.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
