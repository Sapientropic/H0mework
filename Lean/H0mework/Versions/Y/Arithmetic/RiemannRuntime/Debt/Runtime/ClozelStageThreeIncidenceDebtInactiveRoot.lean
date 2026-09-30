import H0mework.Versions.Y.Arithmetic.RiemannRuntime.Debt.Runtime.ClozelStageThreeIncidenceDebtActiveRoot

/-!
# Inactive continuation root after incidence-debt payment

The projection debt is absent after its terminal handoff, while the canonical
arithmetic row continues at the exact next unit-history support.  This root is
the debt-inactive lift of the existing canonical unit update; it creates no
new debt, budget or terminal branch.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate.InactiveRoot

open CanonicalUnitArithmeticRoot
open DebtActivationWorld
open RootGeneratedProofRelevantRestructuring
open BranchNeutralDebtGate
open ActiveRoot

noncomputable section

variable {observation : GeneratedRiemannZeroObservation}
variable {nontrivial : ¬ ∃ n : Nat,
  observation.coordinate = -2 * (n + 1)}

local notation "Law" =>
  stageThreeIncidenceProjectionDebtLaw observation nontrivial
local notation "W" =>
  StageThreeIncidenceProjectionDebtNetwork observation nontrivial

def initialBaseCurrent : CanonicalUnitArithmeticRoot.Current :=
  CanonicalUnitArithmeticRoot.next
    (ActiveRoot.baseSupport
      (observation := observation) (nontrivial := nontrivial))

def supportAt (current : CanonicalUnitArithmeticRoot.Current) : (W).Support :=
  ⟨current, none⟩

abbrev vocabulary : Vocabulary where
  Current := CanonicalUnitArithmeticRoot.Current
  Anchor := (W).Anchor
  Incidence := (W).Incidence
  Lineage := (W).Lineage
  anchorAt := fun current => (W).anchorAt (supportAt current)
  incidenceAt := fun current => (W).incidenceAt (supportAt current)
  lineageAt := fun current => (W).lineageAt (supportAt current)
  NativeWriteAt := CanonicalUnitArithmeticRoot.NativeWriteAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := CanonicalUnitArithmeticRoot.NativeWriteAt.target
  relationTarget := fun event => nomatch event
  continuedTarget := fun event => nomatch event
  redirectTarget := fun event => nomatch event

local notation "V" => vocabulary
  (observation := observation) (nontrivial := nontrivial)

inductive RootEventAt : (current : (V).Current) → (W).Support → Type
  | step (current : (V).Current) : RootEventAt current (supportAt current)

def inactiveInventoryPresentation
    (current : CanonicalUnitArithmeticRoot.Current) :
    ConstructivePresentation PUnit
      (OpenResponsibilityAt W (supportAt current)) :=
  DebtActivationWorld.inactiveInventoryPresentation
    (law := Law) (rootLedgerInventoryPresentation current)

def eventAlgebra : SourceNativeEventAlgebra W V where
  EventAt := RootEventAt
  compile := by
    intro current support event
    cases event with
    | step => exact .nativeWrite (nativeWriteAt current)
  AffectedInventoryAt := fun {_current} {_support} _event => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event with
    | step => exact inactiveInventoryPresentation current
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

def source
    (_receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeSource W V where
  initial := initialBaseCurrent
    (observation := observation) (nontrivial := nontrivial)
  law := eventAlgebra
    (observation := observation) (nontrivial := nontrivial)

def emitted
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : (V).Current) :
    (source receipt).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt current,
    RootEventAt.step (observation := observation)
      (nontrivial := nontrivial) current⟩

def inactiveEntry (current : CanonicalUnitArithmeticRoot.Current) :
    OpenResponsibilityAt W (supportAt current) :=
  DebtActivationWorld.oldEntry (law := Law) (state? := none)
    (rootLedgerEntry current)

theorem inactiveEntry_unique
    (current : CanonicalUnitArithmeticRoot.Current)
    (entry : OpenResponsibilityAt W (supportAt current)) :
    entry = inactiveEntry current := by
  have recovered := (inactiveInventoryPresentation current).forward_backward entry
  exact recovered.symm

def transferReceipt (current : CanonicalUnitArithmeticRoot.Current) :
    (W).DispositionAt (supportAt current) .transfer :=
  .inl (.transfer (nativeWriteAt current))

def ledgerEvolution (current : CanonicalUnitArithmeticRoot.Current) :
    LedgerWriteEvolutionAt W ⟨supportAt current⟩
      ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩ where
  destination := fun entry => by
    cases inactiveEntry_unique current entry
    exact ⟨inactiveEntry (CanonicalUnitArithmeticRoot.next current),
      .transferred (transferReceipt current) rfl rfl (Nat.le_refl 0)⟩
  origin := fun entry => by
    cases inactiveEntry_unique (CanonicalUnitArithmeticRoot.next current) entry
    exact ⟨inactiveEntry current,
      .transferred (transferReceipt current) rfl rfl (Nat.le_refl 0)⟩

structure ExactTransitionAt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    {current : (V).Current}
    (occurrence : (source receipt).toRootSource.actual.OccurrenceAt current)
    {targetSupport : (W).Support}
    (sourceEntry : OpenResponsibilityAt W
      ((source receipt).toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt W targetSupport) : Type where
  evolution : LedgerEntryEvolutionAt W sourceEntry targetEntry
  lineage_eq : (W).lineageAt
      ((source receipt).toRootSource.account.supportOf occurrence) =
    (W).lineageAt targetSupport

def remainderEventAt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    {current : (V).Current}
    (_occurrence : (source receipt).toRootSource.actual.OccurrenceAt current)
    (targetSupport : (W).Support) : Type :=
  PLift (targetSupport = supportAt (CanonicalUnitArithmeticRoot.next current))

def remainderSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerTransportedRemainderSourceAt (source receipt)
      (ExactTransitionAt receipt) where
  OccurrenceAt := remainderEventAt receipt
  emit? := by
    intro current occurrence targetSupport
    classical
    by_cases target_eq :
        targetSupport = supportAt (CanonicalUnitArithmeticRoot.next current)
    · exact some (PLift.up target_eq)
    · exact none
  compileEvolution := by
    intro current occurrence targetSupport event
    rcases occurrence with ⟨support, rootEvent⟩
    cases rootEvent with
    | step =>
        rcases event with ⟨target_eq⟩
        cases target_eq
        exact ledgerEvolution current
  compileExact := by
    intro current occurrence targetSupport event
    rcases occurrence with ⟨support, rootEvent⟩
    cases rootEvent with
    | step =>
        rcases event with ⟨target_eq⟩
        cases target_eq
        exact
          { destination := fun entry =>
              { evolution := (ledgerEvolution current).destination entry |>.2
                lineage_eq := rfl }
            origin := fun entry =>
              { evolution := (ledgerEvolution current).origin entry |>.2
                lineage_eq := rfl } }

abbrev writeRowSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerWriteRowSourceAt (source receipt) (ExactTransitionAt receipt) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun event => nomatch event
  compileExact := fun event => nomatch event
  transportedRemainderSource := remainderSource receipt

def emptyRows
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    FiniteGeneratedLedgerWriteRowsAt (writeRowSource receipt)
      (emitted receipt current)
      ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩ where
  size := 0
  sourceEntryAt := Fin.elim0
  targetEntryAt := Fin.elim0
  rowAt := fun index => Fin.elim0 index

def emptyCoverage
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    LedgerTransportedRemainderCoverageAt (emptyRows receipt current) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

theorem remainderSource_emit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    (remainderSource receipt).emit? (emitted receipt current)
        (supportAt (CanonicalUnitArithmeticRoot.next current)) =
      some (PLift.up rfl) := by
  classical
  simp [remainderSource, emitted]
  congr 2

def generatedRemainder
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    GeneratedLedgerTransportedRemainderAt (writeRowSource receipt)
      (emitted receipt current)
      ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩ :=
  (writeRowSource receipt).generateTransportedRemainder
    (emitted receipt current)
    ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩
    (PLift.up rfl) (remainderSource_emit receipt current)

theorem generatedRemainder_evolution
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    (generatedRemainder receipt current).evolution = ledgerEvolution current := by
  rfl

def patch
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource receipt)
      (emitted receipt current)
      ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩ :=
  .transportedRemainder (emptyRows receipt current)
    (emptyCoverage receipt current) (generatedRemainder receipt current)

private theorem ledgerWriteEvolution_ext
    {sourceSupport targetSupport : (W).Support}
    (left right : LedgerWriteEvolutionAt W
      ⟨sourceSupport⟩ ⟨targetSupport⟩)
    (destination : ∀ entry, left.destination entry = right.destination entry)
    (origin : ∀ entry, left.origin entry = right.origin entry) :
    left = right := by
  cases left with
  | mk leftDestination leftOrigin =>
      cases right with
      | mk rightDestination rightOrigin =>
          congr
          · funext entry
            exact destination entry
          · funext entry
            exact origin entry

@[simp] theorem patch_evolution
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (current : CanonicalUnitArithmeticRoot.Current) :
    (patch receipt current).toLedgerWriteEvolution = ledgerEvolution current := by
  apply ledgerWriteEvolution_ext
  · intro entry
    change (generatedRemainder receipt current).evolution.destination entry = _
    rw [generatedRemainder_evolution]
  · intro entry
    change (generatedRemainder receipt current).evolution.origin entry = _
    rw [generatedRemainder_evolution]

def terminalRowSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerTerminalRowSourceAt (source receipt) :=
  LedgerTerminalRowSourceAt.empty (source receipt)

def ledgerCompiler
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLedgerCompiler (source receipt) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt receipt
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun exact => exact.lineage_eq
  writeRowSource := writeRowSource receipt
  terminalRowSource := terminalRowSource receipt
  compile := by
    intro current occurrence
    rcases occurrence with ⟨support, rootEvent⟩
    cases rootEvent with
    | step =>
        exact .nativeWrite (nativeWriteAt current) rfl
          (emitted receipt (CanonicalUnitArithmeticRoot.next current))
          (ledgerEvolution current)
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, rootEvent⟩
    cases rootEvent with
    | step => exact ⟨patch receipt current, patch_evolution receipt current⟩

def restructuringLaw
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLedgerRestructuringLaw (source receipt) :=
  RootGeneratedProofRelevantRestructuring.law W
    (supportAt (initialBaseCurrent
      (observation := observation) (nontrivial := nontrivial)))
    (source receipt)

def restructuringCertification
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    {current : (V).Current}
    (occurrence : (source receipt).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw receipt)
      ((ledgerCompiler receipt).compile occurrence) := by
  rcases occurrence with ⟨support, rootEvent⟩
  cases rootEvent with
  | step =>
      apply ExactLedgerRestructuringCertificationAt.ofInjective
      · intro left right _equality
        exact inactiveEntry_unique (CanonicalUnitArithmeticRoot.next current) left |>.trans
          ((inactiveEntry_unique (CanonicalUnitArithmeticRoot.next current) right).symm)
      · intro left right _equality
        exact inactiveEntry_unique current left |>.trans
          ((inactiveEntry_unique current right).symm)

def restructuringCompiler
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRestructuringLedgerCompiler (source receipt) where
  ledgerCompiler := ledgerCompiler receipt
  restructuringLaw := restructuringLaw receipt
  certifyRestructuring := restructuringCertification receipt

def restructuringSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeRestructuringLedgerSource W V where
  source := source receipt
  compiler := restructuringCompiler receipt

def projectionLaw
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeProjectionLaw (restructuringSource receipt).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {_current} _occurrence _active =>
    StageThreeIncidencePaymentReceiptAt observation nontrivial
  project := fun _ {_current} _occurrence _active => receipt

def eventInventoryAdmission
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeCompleteEventInventoryAdmission (restructuringSource receipt) :=
  .reflOfNoFaithfulTerminal (restructuringSource receipt)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

def authoritySource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
  SourceNativeAuthoritySource W V where
  restructuringSource := restructuringSource receipt
  eventInventoryAdmission := eventInventoryAdmission receipt
  lawSurface := .rootSemantic W
  projectionLaw := projectionLaw receipt

def authoritativeRoot
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
  SourceNativeAuthoritativeRootClosure W V where
  source := authoritySource receipt
  emitted := emitted receipt
  compiler_commutes := by
    intro current
    rfl

theorem root_initial_support
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (authoritativeRoot receipt).toRoot.supportAt
        (authoritativeRoot receipt).toRoot.source.initial =
      supportAt (initialBaseCurrent
        (observation := observation) (nontrivial := nontrivial)) :=
  rfl

end
end IntegralGraphJointAction.BranchNeutralDebtGate.InactiveRoot
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.InactiveRoot.root_initial_support
