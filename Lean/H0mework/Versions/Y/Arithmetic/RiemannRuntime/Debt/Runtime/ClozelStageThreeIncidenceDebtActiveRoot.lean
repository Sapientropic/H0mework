import H0mework.Foundation.Ledger.ProofRelevantRestructuring
import H0mework.Foundation.Authority.SourceProjectionInventory
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.Debt.Admission.ClozelStageThreeIncidenceDebtAdmission

/-!
# Active root for the stage-three incidence projection debt

One receipt-generated root has exactly two reachable phases.  Its first event
folds the generic debt step over the complete active ledger; its second event
is the source-generated phase terminal at the installed state.  This file
builds the authoritative root only.  The terminal handoff which preserves the
inherited canonical row is installed separately.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate.ActiveRoot

open CanonicalUnitArithmeticRoot
open DebtActivationLedger
open DebtActivationWorld
open RootGeneratedProofRelevantRestructuring
open BranchNeutralDebtGate

noncomputable section

variable {observation : GeneratedRiemannZeroObservation}
variable {nontrivial : ¬ ∃ n : Nat,
  observation.coordinate = -2 * (n + 1)}

local notation "Law" =>
  stageThreeIncidenceProjectionDebtLaw observation nontrivial
local notation "W" =>
  StageThreeIncidenceProjectionDebtNetwork observation nontrivial

def baseSupport : N.Support :=
  stageThreeIncidenceProjectionSupport observation nontrivial

inductive Phase
  | pending
  | installed
  deriving DecidableEq

def pendingSupport : (W).Support :=
  ⟨baseSupport (observation := observation) (nontrivial := nontrivial),
    some (StageThreeIncidenceProjectionDebtState.pending
      (observation := observation) (nontrivial := nontrivial))⟩

def installedSupport
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (W).Support :=
  ⟨baseSupport (observation := observation) (nontrivial := nontrivial),
    some (.installed receipt)⟩

def NativeWriteAt : Phase → Type
  | .pending => PUnit
  | .installed => PEmpty

def FaithfulTerminalAt : Phase → Type
  | .pending => PEmpty
  | .installed => PUnit

def nativeTarget : {phase : Phase} → NativeWriteAt phase → Phase
  | .pending, _ => .installed
  | .installed, impossible => nomatch impossible

abbrev vocabulary : Vocabulary where
  Current := Phase
  Anchor := (W).Anchor
  Incidence := (W).Incidence
  Lineage := (W).Lineage
  anchorAt := fun _ => (W).anchorAt
    (pendingSupport (observation := observation) (nontrivial := nontrivial))
  incidenceAt := fun _ => (W).incidenceAt
    (pendingSupport (observation := observation) (nontrivial := nontrivial))
  lineageAt := fun _ => (W).lineageAt
    (pendingSupport (observation := observation) (nontrivial := nontrivial))
  NativeWriteAt := NativeWriteAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := FaithfulTerminalAt
  nativeTarget := nativeTarget
  relationTarget := fun event => nomatch event
  continuedTarget := fun event => nomatch event
  redirectTarget := fun event => nomatch event

local notation "V" => vocabulary
  (observation := observation) (nontrivial := nontrivial)

inductive RootEventAt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (V).Current → (W).Support → Type
  | payment : RootEventAt receipt Phase.pending
      (pendingSupport (observation := observation) (nontrivial := nontrivial))
  | terminal : RootEventAt receipt Phase.installed
      (installedSupport receipt)

def activeDebtInventoryPresentation
    (state : (Law).DebtState) :
    ConstructivePresentation (Option PUnit)
      (OpenResponsibilityAt W
        ⟨baseSupport (observation := observation) (nontrivial := nontrivial),
          some state⟩) :=
  DebtActivationWorld.activeInventoryPresentation
    (N := N) (law := Law) state
    (rootLedgerInventoryPresentation
      (baseSupport (observation := observation) (nontrivial := nontrivial)))

def eventAlgebra
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeEventAlgebra W V where
  EventAt := RootEventAt receipt
  compile := by
    intro current support event
    cases event with
    | payment => exact .nativeWrite PUnit.unit
    | terminal => exact .faithfulTerminal PUnit.unit
  AffectedInventoryAt := fun {_current} {_support} _event => Option PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event with
    | payment =>
        exact (activeDebtInventoryPresentation
          (observation := observation) (nontrivial := nontrivial)
          (StageThreeIncidenceProjectionDebtState.pending
            (observation := observation) (nontrivial := nontrivial)))
    | terminal =>
        exact (activeDebtInventoryPresentation
          (observation := observation) (nontrivial := nontrivial)
          (.installed receipt))
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event <;> rfl
  incidence_commutes := by
    intro current support event
    cases event <;> rfl
  lineage_commutes := by
    intro current support event
    cases event <;> rfl

def source
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeSource W V where
  initial := Phase.pending
  law := eventAlgebra receipt

def emitted
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (phase : (V).Current) →
      (source receipt).toRootSource.actual.OccurrenceAt phase
  | Phase.pending =>
      ⟨pendingSupport (observation := observation) (nontrivial := nontrivial),
        .payment⟩
  | Phase.installed => ⟨installedSupport receipt, .terminal⟩

def paymentStep
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (Law).StepAt
      (StageThreeIncidenceProjectionDebtState.pending
        (observation := observation) (nontrivial := nontrivial))
      (.installed receipt) :=
  StageThreeIncidenceProjectionDebtStepAt.install receipt

def paymentEvolution
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerWriteEvolutionAt W
      ⟨pendingSupport (observation := observation) (nontrivial := nontrivial)⟩
      ⟨installedSupport receipt⟩ :=
  stepLedgerEvolution
    (baseSupport (observation := observation) (nontrivial := nontrivial))
    (paymentStep receipt)

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

def paymentRemainderEventAt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    {current : (V).Current}
    (_occurrence : (source receipt).toRootSource.actual.OccurrenceAt current)
    (targetSupport : (W).Support) : Type :=
  match current with
  | Phase.pending => PLift (targetSupport = installedSupport receipt)
  | Phase.installed => PEmpty

def paymentRemainderSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerTransportedRemainderSourceAt (source receipt)
      (ExactTransitionAt receipt) where
  OccurrenceAt := paymentRemainderEventAt receipt
  emit? := by
    intro current occurrence targetSupport
    rcases occurrence with ⟨support, sourceEvent⟩
    cases sourceEvent with
    | terminal => exact none
    | payment =>
        classical
        by_cases target_eq : targetSupport = installedSupport receipt
        · exact some (PLift.up target_eq)
        · exact none
  compileEvolution := by
    intro current occurrence targetSupport event
    rcases occurrence with ⟨support, sourceEvent⟩
    cases sourceEvent with
    | terminal => exact nomatch event
    | payment =>
        rcases event with ⟨target_eq⟩
        cases target_eq
        exact paymentEvolution receipt
  compileExact := by
    intro current occurrence targetSupport event
    rcases occurrence with ⟨support, sourceEvent⟩
    cases sourceEvent with
    | terminal => exact nomatch event
    | payment =>
        rcases event with ⟨target_eq⟩
        cases target_eq
        exact
          { destination := fun entry =>
              { evolution := (paymentEvolution receipt).destination entry |>.2
                lineage_eq := rfl }
            origin := fun entry =>
              { evolution := (paymentEvolution receipt).origin entry |>.2
                lineage_eq := rfl } }

abbrev writeRowSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerWriteRowSourceAt (source receipt) (ExactTransitionAt receipt) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun event => nomatch event
  compileExact := fun event => nomatch event
  transportedRemainderSource := paymentRemainderSource receipt

def emptyPaymentRows
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    FiniteGeneratedLedgerWriteRowsAt (writeRowSource receipt)
      (emitted receipt Phase.pending) ⟨installedSupport receipt⟩ where
  size := 0
  sourceEntryAt := Fin.elim0
  targetEntryAt := Fin.elim0
  rowAt := fun index => Fin.elim0 index

def emptyPaymentCoverage
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerTransportedRemainderCoverageAt (emptyPaymentRows receipt) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

theorem paymentRemainderSource_emit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (paymentRemainderSource receipt).emit?
        (emitted receipt Phase.pending) (installedSupport receipt) =
      some (PLift.up rfl) := by
  classical
  simp [paymentRemainderSource, emitted]
  congr 2

def generatedPaymentRemainder
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    GeneratedLedgerTransportedRemainderAt (writeRowSource receipt)
      (emitted receipt Phase.pending) ⟨installedSupport receipt⟩ :=
  (writeRowSource receipt).generateTransportedRemainder
    (emitted receipt Phase.pending) ⟨installedSupport receipt⟩
    (PLift.up rfl) (paymentRemainderSource_emit receipt)

theorem generatedPaymentRemainder_evolution
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (generatedPaymentRemainder receipt).evolution =
      paymentEvolution receipt := by
  rfl

def paymentPatch
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource receipt)
      (emitted receipt Phase.pending) ⟨installedSupport receipt⟩ :=
  .transportedRemainder (emptyPaymentRows receipt)
    (emptyPaymentCoverage receipt) (generatedPaymentRemainder receipt)

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

@[simp] theorem paymentPatch_evolution
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (paymentPatch receipt).toLedgerWriteEvolution =
      paymentEvolution receipt := by
  classical
  apply ledgerWriteEvolution_ext
  · intro entry
    change (generatedPaymentRemainder receipt).evolution.destination entry = _
    rw [generatedPaymentRemainder_evolution]
  · intro entry
    change (generatedPaymentRemainder receipt).evolution.origin entry = _
    rw [generatedPaymentRemainder_evolution]

def installedPhaseTerminal
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (Law).SupportTerminalAt (.installed receipt) := by
  change StageThreeIncidenceProjectionDebtSettlementAt (.installed receipt)
  exact .installed receipt

def terminalRowSource
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    LedgerTerminalRowSourceAt (source receipt) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun event => nomatch event
  supportSettlementSource :=
    { OccurrenceAt := fun {current} _occurrence =>
        match current with
        | .pending => PEmpty
        | .installed => PUnit
      emit? := by
        intro current occurrence
        cases current with
        | pending => exact none
        | installed => exact some PUnit.unit
      compile := by
        intro current occurrence event
        rcases occurrence with ⟨support, sourceEvent⟩
        cases sourceEvent with
        | payment => exact nomatch event
        | terminal =>
            exact debtSupportTerminalReceipt
              (baseSupport (observation := observation)
                (nontrivial := nontrivial))
              (installedPhaseTerminal receipt) }

def generatedInstalledSettlement
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    GeneratedLedgerSupportSettlementAt (terminalRowSource receipt)
      (emitted receipt Phase.installed) :=
  ((terminalRowSource receipt).generateSupportSettlement?
    (emitted receipt Phase.installed)).get (by rfl)

def terminalPatch
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceGeneratedLedgerTerminalPatchAt (terminalRowSource receipt)
      (emitted receipt Phase.installed) :=
  .supportSettlement (generatedInstalledSettlement receipt)

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
    rcases occurrence with ⟨support, event⟩
    cases event with
    | payment =>
        exact .nativeWrite PUnit.unit rfl (emitted receipt Phase.installed)
          (paymentEvolution receipt)
    | terminal =>
        exact .faithfulTerminal PUnit.unit rfl
          (terminalPatch receipt).toLedgerTerminalEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | payment => exact ⟨paymentPatch receipt, paymentPatch_evolution receipt⟩
    | terminal => exact ⟨terminalPatch receipt, rfl⟩

def restructuringLaw
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLedgerRestructuringLaw (source receipt) :=
  RootGeneratedProofRelevantRestructuring.law W
    (pendingSupport (observation := observation) (nontrivial := nontrivial))
    (source receipt)

def restructuringCertification
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    {current : (V).Current}
    (occurrence : (source receipt).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw receipt) ((ledgerCompiler receipt).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | terminal => exact PUnit.unit
  | payment =>
      apply ExactLedgerRestructuringCertificationAt.ofInjective
      · change Function.Injective (fun target =>
          ((stepLedgerEvolution
            (baseSupport (observation := observation)
              (nontrivial := nontrivial))
            (paymentStep receipt)).origin target).1)
        exact Function.LeftInverse.injective
          (g := fun sourceEntry =>
            ((stepLedgerEvolution
              (baseSupport (observation := observation)
                (nontrivial := nontrivial))
              (paymentStep receipt)).destination sourceEntry).1)
          (fun entry =>
          stepLedgerEvolution_destination_origin
            (baseSupport (observation := observation)
              (nontrivial := nontrivial))
            (paymentStep receipt) entry)
      · change Function.Injective (fun sourceEntry =>
          ((stepLedgerEvolution
            (baseSupport (observation := observation)
              (nontrivial := nontrivial))
            (paymentStep receipt)).destination sourceEntry).1)
        exact Function.LeftInverse.injective
          (g := fun target =>
            ((stepLedgerEvolution
              (baseSupport (observation := observation)
                (nontrivial := nontrivial))
              (paymentStep receipt)).origin target).1)
          (fun entry =>
          stepLedgerEvolution_origin_destination
            (baseSupport (observation := observation)
              (nontrivial := nontrivial))
            (paymentStep receipt) entry)

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
    SourceNativeCompleteEventInventoryAdmission
      (restructuringSource receipt) :=
  SourceNativeCompleteEventInventoryAdmission.refl
    (restructuringSource receipt) (by
      intro current occurrence terminal terminal_eq
      cases current with
      | pending => exact nomatch terminal
      | installed =>
          constructor
          rintro ⟨outgoingOccurrence, successor⟩
          rcases outgoingOccurrence with ⟨support, event⟩
          cases event
          exact nomatch successor)

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
    cases current with
    | pending => rfl
    | installed => exact True.intro

def pendingVisit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    RootVisit (authoritativeRoot receipt).toRoot :=
  (authoritativeRoot receipt).toRoot.initialVisit

def installedVisit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    RootVisit (authoritativeRoot receipt).toRoot :=
  (pendingVisit receipt).next rfl

theorem pending_generated_is_exact_first_payment
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (authoritativeRoot receipt).generatedLedgerAt Phase.pending =
      .nativeWrite PUnit.unit rfl (emitted receipt Phase.installed)
        (paymentEvolution receipt) :=
  rfl

theorem installed_generated_is_phase_terminal
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (authoritativeRoot receipt).generatedLedgerAt Phase.installed =
      .faithfulTerminal PUnit.unit rfl
        (terminalPatch receipt).toLedgerTerminalEvolution :=
  rfl

end
end IntegralGraphJointAction.BranchNeutralDebtGate.ActiveRoot
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.ActiveRoot.pending_generated_is_exact_first_payment
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.ActiveRoot.installed_generated_is_phase_terminal
