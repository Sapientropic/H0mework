import H0mework.Physics.MotherDeclarationsAll.SourceOriginSource

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable (law : Law) (material : Material)

abbrev Current := GeneralSourceEvolution.State (input material).1
abbrev OccurrenceAt (current : Current material) := (sourceAt law material).toRootSource.actual.OccurrenceAt current

def target {current : Current material} (occurrence : OccurrenceAt law material current) : Current material :=
  next law (input material).1 current occurrence.2.center

structure ExactTransitionAt {current : Current material} (occurrence : OccurrenceAt law material current)
    (targetSupport : Current material) : Type where
  target_eq : targetSupport = target law material occurrence

def rowSource : LedgerWriteRowSourceAt (sourceAt law material) (fun {_} occurrence {targetSupport} _ _ =>
    ExactTransitionAt law material occurrence targetSupport) where
  IncidenceOccurrenceAt := fun {_} occurrence {targetSupport} _ _ => ExactTransitionAt law material occurrence targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change EventAt (input material).1 current support at sourceEvent
    cases sourceEvent.support_eq
    cases event.target_eq
    cases entry_unique _ _ sourceEntry
    cases entry_unique _ _ targetEntry
    exact .transferred sourceEvent.center rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def occurrenceEntry {current : Current material} (occurrence : OccurrenceAt law material current) :
    OpenResponsibilityAt (network (input material).1) occurrence.1 :=
  ((sourceAt law material).law.affectedInventoryPresentation occurrence.2).forward PUnit.unit

def rows {current : Current material} (occurrence : OccurrenceAt law material current) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource law material) occurrence
      (⟨target law material occurrence⟩ : CompleteLiveLedgerAt (network (input material).1)) where
  size := 1
  sourceEntryAt := fun _ => occurrenceEntry law material occurrence
  targetEntryAt := fun _ => entry (input material).1 (target law material occurrence)
  rowAt := fun _ => (rowSource law material).generate ⟨rfl⟩

def coverage {current : Current material} (occurrence : OccurrenceAt law material current) :
    LedgerCompleteFiniteCoverageAt (rows law material occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun value =>
    ((sourceAt law material).law.affectedInventoryPresentation occurrence.2).forward_backward value
  origin_sound := fun value => (entry_unique _ _ value).symm

def patch {current : Current material} (occurrence : OccurrenceAt law material current) :
    FiniteGeneratedLedgerWritePatchAt (rowSource law material) occurrence
      (⟨target law material occurrence⟩ : CompleteLiveLedgerAt (network (input material).1)) :=
  .complete (rows law material occurrence) (coverage law material occurrence)

def evolution {current : Current material} (occurrence : OccurrenceAt law material current) :
    SourceNativeLedgerEvolutionAt (sourceAt law material) occurrence :=
  .nativeWrite occurrence.2.center rfl (emitted law material (target law material occurrence))
    (patch law material occurrence).toLedgerWriteEvolution

def compiler : SourceNativeLedgerCompiler (sourceAt law material) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := fun occurrence targetSupport _ _ => ExactTransitionAt law material occurrence targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := rowSource law material
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := evolution law material
  compilePatch := fun occurrence => ⟨patch law material occurrence, rfl⟩

def ledgerSource : SourceNativeLedgerSource (network (input material).1) (vocabulary law (input material).1) where
  source := sourceAt law material
  ledgerCompiler := compiler law material

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin
