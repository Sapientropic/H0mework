import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionWorld

/-! # The existing ledger compiler receives source-generated recovery updates -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def recoveryVocabulary : ConstructiveRoot.Vocabulary where
  Current := RecoveryCurrent
  Anchor := RecoveryN.Anchor
  Incidence := RecoverySupport
  Lineage := RecoveryN.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := recoveryCurrentSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => recoveryNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev RecoveryV := recoveryVocabulary

structure RecoveryEventAt (current : RecoveryCurrent) (support : RecoverySupport) : Type where
  supportExact : support = recoveryCurrentSupport current

def recoveryEventLaw : SourceNativeEventAlgebra RecoveryN RecoveryV where
  EventAt := RecoveryEventAt
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

def recoverySource : SourceNativeSource RecoveryN RecoveryV where
  initial := .ingress
  law := recoveryEventLaw

def recoveryEmitted (current : RecoveryCurrent) : recoverySource.toRootSource.actual.OccurrenceAt current :=
  ⟨recoveryCurrentSupport current, ⟨rfl⟩⟩

structure RecoveryExactTransitionAt (current : RecoveryCurrent) (support : RecoverySupport) : Type where
  targetExact : support = recoveryCurrentSupport (recoveryNext current)

def recoveryWriteRowSource : LedgerWriteRowSourceAt recoverySource (by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact RecoveryExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact RecoveryExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change RecoveryEventAt current support at sourceEvent
    cases sourceEvent.supportExact
    cases event.targetExact
    cases recoveryEntry_unique _ sourceEntry
    cases recoveryEntry_unique _ targetEntry
    cases current
    all_goals exact .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  compileExact := fun event => event

def recoveryOccurrenceEntry {current : RecoveryCurrent}
    (occurrence : recoverySource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt RecoveryN occurrence.1 :=
  recoverySource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def recoveryGeneratedRows {current : RecoveryCurrent}
    (occurrence : recoverySource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt recoveryWriteRowSource occurrence
      (⟨recoveryCurrentSupport (recoveryNext current)⟩ : CompleteLiveLedgerAt RecoveryN) where
  size := 1
  sourceEntryAt := fun _ => recoveryOccurrenceEntry occurrence
  targetEntryAt := fun _ => recoveryEntry (recoveryCurrentSupport (recoveryNext current))
  rowAt := fun _ => recoveryWriteRowSource.generate ⟨rfl⟩

def recoveryGeneratedCoverage {current : RecoveryCurrent}
    (occurrence : recoverySource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (recoveryGeneratedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun entry => by
    change recoveryOccurrenceEntry occurrence = entry
    exact (recoverySource.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry => (recoveryEntry_unique _ entry).symm

def recoveryGeneratedPatch {current : RecoveryCurrent}
    (occurrence : recoverySource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt recoveryWriteRowSource occurrence
      (⟨recoveryCurrentSupport (recoveryNext current)⟩ : CompleteLiveLedgerAt RecoveryN) :=
  .complete (recoveryGeneratedRows occurrence) (recoveryGeneratedCoverage occurrence)

def recoveryGeneratedEvolution {current : RecoveryCurrent}
    (occurrence : recoverySource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt recoverySource occurrence :=
  .nativeWrite PUnit.unit rfl (recoveryEmitted (recoveryNext current))
    (recoveryGeneratedPatch occurrence).toLedgerWriteEvolution

def recoveryLedgerCompiler : SourceNativeLedgerCompiler recoverySource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact RecoveryExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := recoveryWriteRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := recoveryGeneratedEvolution
  compilePatch := fun occurrence => ⟨recoveryGeneratedPatch occurrence, rfl⟩

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
