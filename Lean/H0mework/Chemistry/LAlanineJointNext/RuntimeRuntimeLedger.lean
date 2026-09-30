import H0mework.Chemistry.LAlanineJointNext.RuntimeRuntimeSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

def jointWriteRowSource : LedgerWriteRowSourceAt jointSource (by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = jointSupport)) where
  IncidenceOccurrenceAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = jointSupport)
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change PLift (support = jointSupport) at sourceEvent
    cases sourceEvent.down
    cases event.down
    cases entryAt_unique sourceEntry
    cases entryAt_unique targetEntry
    exact .carried rfl HEq.rfl
  compileExact := fun event => event

def jointOccurrenceEntry {current : JointCurrent}
    (occurrence : jointSource.toRootSource.actual.OccurrenceAt current) : OpenResponsibilityAt N occurrence.1 :=
  jointSource.law.affectedInventoryPresentation occurrence.2 |>.forward ()

def jointGeneratedRows {current : JointCurrent}
    (occurrence : jointSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt jointWriteRowSource occurrence (⟨jointSupport⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => jointOccurrenceEntry occurrence
  targetEntryAt := fun _ => entryAt jointSupport
  rowAt := fun _ => jointWriteRowSource.generate ⟨rfl⟩

def jointGeneratedCoverage {current : JointCurrent}
    (occurrence : jointSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (jointGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change jointOccurrenceEntry occurrence = entry
    exact (jointSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (entryAt_unique entry).symm

def jointGeneratedPatch {current : JointCurrent}
    (occurrence : jointSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt jointWriteRowSource occurrence (⟨jointSupport⟩ : CompleteLiveLedgerAt N) :=
  .complete (jointGeneratedRows occurrence) (jointGeneratedCoverage occurrence)

def jointGeneratedEvolution {current : JointCurrent}
    (occurrence : jointSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt jointSource occurrence := by
  cases current with
  | ingress =>
      exact SourceNativeLedgerEvolutionAt.nativeWrite (source := jointSource)
        (occurrence := occurrence) PUnit.unit rfl (jointEmitted (jointNext .ingress))
        (jointGeneratedPatch occurrence).toLedgerWriteEvolution
  | ready result =>
      exact SourceNativeLedgerEvolutionAt.continuedTransport (source := jointSource)
        (occurrence := occurrence) PUnit.unit rfl (jointEmitted (.ready result))
        (jointGeneratedPatch occurrence).toLedgerWriteEvolution

def jointLedgerCompiler : SourceNativeLedgerCompiler jointSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro _ _ targetSupport _ _
    exact PLift (targetSupport = jointSupport)
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := jointWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := jointGeneratedEvolution
  compilePatch := by
    intro current occurrence
    cases current <;> exact ⟨jointGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
