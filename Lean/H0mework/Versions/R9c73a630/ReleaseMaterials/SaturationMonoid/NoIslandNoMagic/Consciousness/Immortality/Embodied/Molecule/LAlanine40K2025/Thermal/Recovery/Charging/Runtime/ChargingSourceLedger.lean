import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Producer.SourceGeneratedWholePCCharging

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Load.Source Load.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source

noncomputable section

/-- The existing world, incidence, responsibility, and current type are retained. -/
def chargingCurrentState : RecoveryCurrent → LoadState
  | .ingress => receivedState
  | .running state => state

def chargingCurrentSupport (current : RecoveryCurrent) : RecoverySupport := .inr (chargingCurrentState current)

def chargingNext (current : RecoveryCurrent) : RecoveryCurrent :=
  .running (match current with
    | .ingress => chargedFirst
    | .running state => loadStateNext state)

def chargingVocabulary : ConstructiveRoot.Vocabulary :=
  { recoveryVocabulary with
    incidenceAt := chargingCurrentSupport
    nativeTarget := fun {current} _ => chargingNext current }

abbrev ChargingV := chargingVocabulary

def chargingEventLaw : SourceNativeEventAlgebra RecoveryN ChargingV where
  EventAt := fun current support => RecoveryEventAt (.running (chargingCurrentState current)) support
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.supportExact
    exact recoveryInventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.supportExact.symm
  lineage_commutes := fun _ => rfl

def chargingSource : SourceNativeSource RecoveryN ChargingV where
  initial := .ingress
  law := chargingEventLaw

def chargingEmitted (current : RecoveryCurrent) : chargingSource.toRootSource.actual.OccurrenceAt current :=
  ⟨chargingCurrentSupport current, ⟨rfl⟩⟩

def chargingWriteRowSource : LedgerWriteRowSourceAt chargingSource (by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact PLift (targetSupport = chargingCurrentSupport (chargingNext current))) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact PLift (targetSupport = chargingCurrentSupport (chargingNext current))
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change RecoveryEventAt (.running (chargingCurrentState current)) support at sourceEvent
    cases sourceEvent.supportExact
    cases event.down
    cases recoveryEntry_unique _ sourceEntry
    cases recoveryEntry_unique _ targetEntry
    exact .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  compileExact := fun event => event

def chargingOccurrenceEntry {current : RecoveryCurrent}
    (occurrence : chargingSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt RecoveryN occurrence.1 :=
  chargingSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def chargingGeneratedRows {current : RecoveryCurrent}
    (occurrence : chargingSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt chargingWriteRowSource occurrence
      (⟨chargingCurrentSupport (chargingNext current)⟩ : CompleteLiveLedgerAt RecoveryN) where
  size := 1
  sourceEntryAt := fun _ => chargingOccurrenceEntry occurrence
  targetEntryAt := fun _ => recoveryEntry (chargingCurrentSupport (chargingNext current))
  rowAt := fun _ => chargingWriteRowSource.generate ⟨rfl⟩

def chargingGeneratedCoverage {current : RecoveryCurrent}
    (occurrence : chargingSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (chargingGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change chargingOccurrenceEntry occurrence = entry
    exact (chargingSource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (recoveryEntry_unique _ entry).symm

def chargingGeneratedPatch {current : RecoveryCurrent}
    (occurrence : chargingSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt chargingWriteRowSource occurrence
      (⟨chargingCurrentSupport (chargingNext current)⟩ : CompleteLiveLedgerAt RecoveryN) :=
  .complete (chargingGeneratedRows occurrence) (chargingGeneratedCoverage occurrence)

def chargingGeneratedEvolution {current : RecoveryCurrent}
    (occurrence : chargingSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt chargingSource occurrence :=
  .nativeWrite PUnit.unit rfl (chargingEmitted (chargingNext current))
    (chargingGeneratedPatch occurrence).toLedgerWriteEvolution

def chargingLedgerCompiler : SourceNativeLedgerCompiler chargingSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact PLift (targetSupport = chargingCurrentSupport (chargingNext current))
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := chargingWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := chargingGeneratedEvolution
  compilePatch := fun occurrence => ⟨chargingGeneratedPatch occurrence, rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Charging.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
