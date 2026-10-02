import H0mework.Foundation.Ledger.SourceCompiler
import H0mework.Versions.R2.Arithmetic.FockResponsibility.DebtU7Admission

/-!
# Source-generated audit ledger for one occurrence-debt U7 row

For one exact projected-return failure, the activated occurrence debt support
has exactly two rows: the inherited canonical arithmetic row and the live
occurrence debt row.  A failure-indexed self audit event presents this whole
fibre and generates the identity whole-ledger patch.  The event contains no
caller row table, target, U7 branch or terminal.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOccurrenceDebtU7AuditSource

open CanonicalUnitArithmeticGlobalGoldbachDisposition
open CanonicalUnitArithmeticOperationalFirstResidualProducer
open DebtActivationWorld
open ParticleWaveFockOccurrenceDebtU7Admission
open ParticleWaveFockOperationalProvenanceRecurrence

noncomputable section

def auditVocabulary (failure : FirstResidualOccurrence) : Vocabulary where
  Current := PUnit
  Anchor := PUnit
  Incidence := CanonicalUnitArithmeticRoot.N.Incidence
  Lineage := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := fun _ => focus failure
  lineageAt := fun _ => PUnit.unit
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun _ => PUnit.unit
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev AuditV (failure : FirstResidualOccurrence) := auditVocabulary failure

inductive AuditEventAt (failure : FirstResidualOccurrence) :
    (AuditV failure).Current → (DebtN failure).Support → Type
  | emitted : AuditEventAt failure PUnit.unit (activeSupport failure)

def activePresentation (failure : FirstResidualOccurrence) :
    ConstructivePresentation (Option Unit)
      (OpenResponsibilityAt (DebtN failure) (activeSupport failure)) :=
  activeInventoryPresentation
    (N := CanonicalUnitArithmeticRoot.N) (law := Law failure)
    (returnedHistoryState failure)
    (CanonicalUnitArithmeticRoot.rootLedgerInventoryPresentation
      (focus failure))

def eventAlgebra (failure : FirstResidualOccurrence) :
    SourceNativeEventAlgebra (DebtN failure) (AuditV failure) where
  EventAt := AuditEventAt failure
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun {_current} {_support} _event => Option Unit
  affectedInventoryPresentation := by
    intro current support event
    cases event
    exact activePresentation failure
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event
    rfl
  incidence_commutes := by
    intro current support event
    cases event
    rfl
  lineage_commutes := by
    intro current support event
    cases event
    rfl

def source (failure : FirstResidualOccurrence) :
    SourceNativeSource (DebtN failure) (AuditV failure) where
  initial := PUnit.unit
  law := eventAlgebra failure

def emitted (failure : FirstResidualOccurrence) :
    (current : (AuditV failure).Current) →
      (source failure).toRootSource.actual.OccurrenceAt current
  | PUnit.unit => ⟨activeSupport failure, .emitted⟩

abbrev ledger (failure : FirstResidualOccurrence) :
    CompleteLiveLedgerAt (DebtN failure) :=
  ⟨activeSupport failure⟩

def rowCoordinate : Fin 2 → Option Unit
  | ⟨0, _⟩ => none
  | ⟨_ + 1, _⟩ => some ()

def rowIndex : Option Unit → Fin 2
  | none => ⟨0, by omega⟩
  | some _ => ⟨1, by omega⟩

@[simp] theorem rowCoordinate_rowIndex (coordinate : Option Unit) :
    rowCoordinate (rowIndex coordinate) = coordinate := by
  cases coordinate <;> rfl

structure ExactTransitionAt (failure : FirstResidualOccurrence)
    {current : (AuditV failure).Current}
    (occurrence : (source failure).toRootSource.actual.OccurrenceAt current)
    {targetSupport : (DebtN failure).Support}
    (sourceEntry : OpenResponsibilityAt (DebtN failure)
      ((source failure).toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt (DebtN failure) targetSupport) : Type where
  support_eq :
    (source failure).toRootSource.account.supportOf occurrence = targetSupport
  entry_eq : HEq sourceEntry targetEntry

def writeRowSource (failure : FirstResidualOccurrence) :
    LedgerWriteRowSourceAt (source failure) (ExactTransitionAt failure) where
  IncidenceOccurrenceAt := ExactTransitionAt failure
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    exact .carried event.support_eq event.entry_eq
  compileExact := fun event => event

def terminalRowSource (failure : FirstResidualOccurrence) :
    LedgerTerminalRowSourceAt (source failure) :=
  LedgerTerminalRowSourceAt.empty _

def generatedRows (failure : FirstResidualOccurrence) :
    FiniteGeneratedLedgerWriteRowsAt (writeRowSource failure)
      (emitted failure PUnit.unit) (ledger failure) where
  size := 2
  sourceEntryAt := fun index =>
    (activePresentation failure).forward (rowCoordinate index)
  targetEntryAt := fun index =>
    (activePresentation failure).forward (rowCoordinate index)
  rowAt := fun _index =>
    (writeRowSource failure).generate ⟨rfl, HEq.rfl⟩

def generatedCoverage (failure : FirstResidualOccurrence) :
    LedgerCompleteFiniteCoverageAt (generatedRows failure) where
  destinationIndex := fun entry =>
    rowIndex ((activePresentation failure).backward entry)
  originIndex := fun entry =>
    rowIndex ((activePresentation failure).backward entry)
  destination_sound := fun entry => by
    change (activePresentation failure).forward
        (rowCoordinate
          (rowIndex ((activePresentation failure).backward entry))) = entry
    rw [rowCoordinate_rowIndex]
    exact (activePresentation failure).forward_backward entry
  origin_sound := fun entry => by
    change (activePresentation failure).forward
        (rowCoordinate
          (rowIndex ((activePresentation failure).backward entry))) = entry
    rw [rowCoordinate_rowIndex]
    exact (activePresentation failure).forward_backward entry

def generatedPatch (failure : FirstResidualOccurrence) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource failure)
      (emitted failure PUnit.unit) (ledger failure) :=
  .complete (generatedRows failure) (generatedCoverage failure)

theorem generatedPatch_destination_eq
    (failure : FirstResidualOccurrence) (entry : (ledger failure).Entry) :
    ((generatedPatch failure).toLedgerWriteEvolution.destination entry).1 =
      entry :=
  (generatedCoverage failure).destination_sound entry

theorem generatedPatch_origin_eq
    (failure : FirstResidualOccurrence) (entry : (ledger failure).Entry) :
    ((generatedPatch failure).toLedgerWriteEvolution.origin entry).1 = entry :=
  (generatedCoverage failure).origin_sound entry

def generatedEvolution (failure : FirstResidualOccurrence) :
    SourceNativeLedgerEvolutionAt (source failure)
      (emitted failure PUnit.unit) :=
  .nativeWrite PUnit.unit rfl (emitted failure PUnit.unit)
    (generatedPatch failure).toLedgerWriteEvolution

def ledgerCompiler (failure : FirstResidualOccurrence) :
    SourceNativeLedgerCompiler (source failure) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt failure
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun event => congrArg (DebtN failure).lineageAt event.support_eq
  writeRowSource := writeRowSource failure
  terminalRowSource := terminalRowSource failure
  compile := by
    intro current occurrence
    cases current
    rcases occurrence with ⟨support, event⟩
    cases event
    exact generatedEvolution failure
  compilePatch := by
    intro current occurrence
    cases current
    rcases occurrence with ⟨support, event⟩
    cases event
    exact ⟨generatedPatch failure, rfl⟩

def ledgerSource (failure : FirstResidualOccurrence) :
    SourceNativeLedgerSource (DebtN failure) (AuditV failure) where
  source := source failure
  ledgerCompiler := ledgerCompiler failure

def ledgerRoot (failure : FirstResidualOccurrence) :
    SourceNativeLedgerRootClosure (DebtN failure) (AuditV failure) where
  source := ledgerSource failure
  emitted := emitted failure
  compiler_commutes := by intro current; cases current; rfl

end

end ParticleWaveFockOccurrenceDebtU7AuditSource
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
