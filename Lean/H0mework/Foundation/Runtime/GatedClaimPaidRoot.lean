import H0mework.Foundation.Ledger.ProofRelevantRestructuring
import H0mework.Foundation.Authority.CausalEntry
import H0mework.Foundation.Runtime.GatedClaimTerminal

/-! A strict gated advance plus its exact whole-terminal target generates a
two-phase authoritative root.  Transported-remainder coverage compiles the
complete payment ledger; a bare advance or obstruction cannot enter. -/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace GatedClaimPaidRoot

open DebtActivationWorld GatedClaimPreProcess GatedClaimRootAuthority
open PendingClaimBirth RootGeneratedProofRelevantRestructuring

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}}
variable {facade : SourceNativePendingClaimRuntimeFacade N}
variable {runtime : LivingRuntimeState facade.base.process}
variable {activated : ExactActivatedRootOccurrenceAt runtime}
variable {face : facade.PendingFaceAt runtime}
variable {read : SourceInstalledPendingClaimFaceAt facade runtime face}
variable {birth : SourceExactPendingClaimBirthReceiptAt
  facade runtime activated read}

/-- The terminal is indexed by the advance's exact target current. -/
structure InputAt
    (birth : SourceExactPendingClaimBirthReceiptAt
      facade runtime activated read) : Type (u + 4) where
  advance : SourceNativeGatedClaimAdvanceAt
    (SourceNativeGatedClaimCurrentAt.initial birth)
  terminal : SourceNativeGatedClaimWholeTerminalAt advance.targetCurrent

variable (input : InputAt birth)

local notation "W" => ExtendedNetwork N birth.law

inductive Phase : Type u
  | pending
  | paid

def vocabulary : Vocabulary.{u} where
  Current := Phase
  Anchor := (W).Anchor
  Incidence := (W).Incidence
  Lineage := (W).Lineage
  anchorAt
    | .pending => (W).anchorAt birth.targetLedger.support
    | .paid => (W).anchorAt input.advance.targetCurrent.ledger.support
  incidenceAt
    | .pending => (W).incidenceAt birth.targetLedger.support
    | .paid => (W).incidenceAt input.advance.targetCurrent.ledger.support
  lineageAt
    | .pending => (W).lineageAt birth.targetLedger.support
    | .paid => (W).lineageAt input.advance.targetCurrent.ledger.support
  NativeWriteAt
    | .pending => PUnit
    | .paid => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt
    | .pending => PEmpty
    | .paid => PUnit
  nativeTarget := by
    intro phase write
    cases phase with
    | pending => exact .paid
    | paid => exact nomatch write
  relationTarget := fun event => nomatch event
  continuedTarget := fun event => nomatch event
  redirectTarget := fun event => nomatch event

local notation "V" => vocabulary input

inductive RootEventAt : (V).Current → (W).Support → Type u
  | payment : RootEventAt .pending birth.targetLedger.support
  | terminal : RootEventAt .paid input.advance.targetCurrent.ledger.support

abbrev BaseInventoryIndex : Type u :=
  runtime.current.root.toAuthoritativeRoot.toLedgerRoot.source.source.law
    |>.AffectedInventoryAt runtime.emittedOccurrence.2

def baseInventoryPresentation :
    ConstructivePresentation (BaseInventoryIndex (runtime := runtime))
      birth.sourceLedger.Entry :=
  runtime.current.root.toAuthoritativeRoot.toLedgerRoot.toInventoryRoot
    |>.affectedInventoryPresentation runtime.current.visit.current

def activeInventoryPresentation
    (debtState : birth.law.DebtState) :
    ConstructivePresentation
      (Option (BaseInventoryIndex (runtime := runtime)))
      (OpenResponsibilityAt W
        ⟨birth.sourceLedger.support, some debtState⟩) :=
  DebtActivationWorld.activeInventoryPresentation debtState
    (baseInventoryPresentation (birth := birth))

def eventAlgebra : SourceNativeEventAlgebra W V where
  EventAt := RootEventAt input
  compile := by
    intro phase support event
    cases event with
    | payment => exact .nativeWrite PUnit.unit
    | terminal => exact .faithfulTerminal PUnit.unit
  AffectedInventoryAt := fun _event =>
    Option (BaseInventoryIndex (runtime := runtime))
  affectedInventoryPresentation := by
    intro phase support event
    cases event with
    | payment => exact activeInventoryPresentation birth.initial
    | terminal => exact activeInventoryPresentation input.advance.targetState
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by intro phase support event; cases event <;> rfl
  incidence_commutes := by intro phase support event; cases event <;> rfl
  lineage_commutes := by intro phase support event; cases event <;> rfl

def source : SourceNativeSource W V where
  initial := .pending
  law := eventAlgebra input

def emitted : (phase : (V).Current) →
    (source input).toRootSource.actual.OccurrenceAt phase
  | .pending => ⟨birth.targetLedger.support, .payment⟩
  | .paid => ⟨input.advance.targetCurrent.ledger.support, .terminal⟩

structure ExactTransitionAt
    {phase : (V).Current}
    (occurrence : (source input).toRootSource.actual.OccurrenceAt phase)
    {targetSupport : (W).Support}
    (sourceEntry : OpenResponsibilityAt W
      ((source input).toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt W targetSupport) : Type u where
  evolution : LedgerEntryEvolutionAt W sourceEntry targetEntry

def paymentRemainderEventAt
    {phase : (V).Current}
    (_occurrence : (source input).toRootSource.actual.OccurrenceAt phase)
    (targetSupport : (W).Support) : Type u :=
  match phase with
  | .pending => ULift.{u, 0}
      (PLift (targetSupport = input.advance.targetCurrent.ledger.support))
  | .paid => PEmpty

def paymentRemainderSource :
    LedgerTransportedRemainderSourceAt (source input)
      (ExactTransitionAt input) where
  OccurrenceAt := paymentRemainderEventAt input
  emit? := by
    intro phase occurrence targetSupport
    cases phase with
    | paid => exact none
    | pending =>
        classical
        by_cases target_eq :
          targetSupport = input.advance.targetCurrent.ledger.support
        · exact some (ULift.up (PLift.up target_eq))
        · exact none
  compileEvolution := by
    intro phase occurrence targetSupport event
    rcases occurrence with ⟨sourceSupport, rootEvent⟩
    cases rootEvent with
    | terminal => exact nomatch event
    | payment =>
        rcases event with ⟨⟨target_eq⟩⟩
        cases target_eq
        exact input.advance.ledgerEvolution
  compileExact := by
    intro phase occurrence targetSupport event
    rcases occurrence with ⟨sourceSupport, rootEvent⟩
    cases rootEvent with
    | terminal => exact nomatch event
    | payment =>
        rcases event with ⟨⟨target_eq⟩⟩
        cases target_eq
        exact
          { destination := fun entry =>
              ⟨(input.advance.ledgerEvolution.destination entry).2⟩
            origin := fun entry =>
              ⟨(input.advance.ledgerEvolution.origin entry).2⟩ }

abbrev writeRowSource : LedgerWriteRowSourceAt (source input)
    (ExactTransitionAt input) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun event => nomatch event
  compileExact := fun event => nomatch event
  transportedRemainderSource := paymentRemainderSource input

def emptyPaymentRows : FiniteGeneratedLedgerWriteRowsAt
    (writeRowSource input) (emitted input .pending)
    input.advance.targetCurrent.ledger where
  size := 0
  sourceEntryAt := Fin.elim0
  targetEntryAt := Fin.elim0
  rowAt := fun index => Fin.elim0 index

def emptyPaymentCoverage :
    LedgerTransportedRemainderCoverageAt (emptyPaymentRows input) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

theorem paymentRemainderSource_emit :
    (paymentRemainderSource input).emit? (emitted input .pending)
      input.advance.targetCurrent.ledger.support =
        some (ULift.up (PLift.up rfl)) := by
  classical
  simp [paymentRemainderSource, emitted]
  congr 2

def generatedPaymentRemainder : GeneratedLedgerTransportedRemainderAt
    (writeRowSource input) (emitted input .pending)
    input.advance.targetCurrent.ledger :=
  (writeRowSource input).generateTransportedRemainder
    (emitted input .pending) input.advance.targetCurrent.ledger
    (ULift.up (PLift.up rfl)) (paymentRemainderSource_emit input)

def paymentPatch : FiniteGeneratedLedgerWritePatchAt (writeRowSource input)
    (emitted input .pending) input.advance.targetCurrent.ledger :=
  .transportedRemainder (emptyPaymentRows input)
    (emptyPaymentCoverage input) (generatedPaymentRemainder input)

private theorem ledgerWriteEvolution_ext
    {sourceLedger targetLedger : CompleteLiveLedgerAt W}
    (left right : LedgerWriteEvolutionAt W sourceLedger targetLedger)
    (destination : ∀ entry, left.destination entry = right.destination entry)
    (origin : ∀ entry, left.origin entry = right.origin entry) : left = right := by
  cases left
  cases right
  congr
  · funext entry; exact destination entry
  · funext entry; exact origin entry

@[simp] theorem paymentPatch_evolution :
    (paymentPatch input).toLedgerWriteEvolution =
      input.advance.ledgerEvolution := by
  classical
  apply ledgerWriteEvolution_ext
  · intro entry
    change (generatedPaymentRemainder input).evolution.destination entry = _
    rfl
  · intro entry
    change (generatedPaymentRemainder input).evolution.origin entry = _
    rfl

def terminalRowSource : LedgerTerminalRowSourceAt (source input) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun event => nomatch event
  supportSettlementSource :=
    { OccurrenceAt := fun {phase} _occurrence =>
        match phase with
        | .pending => PEmpty
        | .paid => PUnit
      emit? := by
        intro phase occurrence
        cases phase with
        | pending => exact none
        | paid => exact some PUnit.unit
      compile := by
        intro phase occurrence event
        rcases occurrence with ⟨support, rootEvent⟩
        cases rootEvent with
        | payment => exact nomatch event
        | terminal => exact input.terminal.worldReceipt }

def generatedTerminalSettlement : GeneratedLedgerSupportSettlementAt
    (terminalRowSource input) (emitted input .paid) :=
  ((terminalRowSource input).generateSupportSettlement?
    (emitted input .paid)).get (by rfl)

def terminalPatch : SourceGeneratedLedgerTerminalPatchAt
    (terminalRowSource input) (emitted input .paid) :=
  .supportSettlement (generatedTerminalSettlement input)

def ledgerCompiler : SourceNativeLedgerCompiler (source input) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt input
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun exact => exact.evolution.toDebtLineage.lineage_eq
  writeRowSource := writeRowSource input
  terminalRowSource := terminalRowSource input
  compile := by
    intro phase occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | payment =>
        exact .nativeWrite PUnit.unit rfl (emitted input .paid)
          input.advance.ledgerEvolution
    | terminal =>
        exact .faithfulTerminal PUnit.unit rfl input.terminal.ledgerEvolution
  compilePatch := by
    intro phase occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | payment => exact ⟨paymentPatch input, paymentPatch_evolution input⟩
    | terminal => exact ⟨terminalPatch input, rfl⟩

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source input) :=
  RootGeneratedProofRelevantRestructuring.law W birth.targetLedger.support
    (source input)

def restructuringCertification
    {phase : (V).Current}
    (occurrence : (source input).toRootSource.actual.OccurrenceAt phase) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw input)
      ((ledgerCompiler input).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event with
  | terminal => exact PUnit.unit
  | payment =>
      apply ExactLedgerRestructuringCertificationAt.ofInjective
      · exact Function.LeftInverse.injective
          (g := fun sourceEntry =>
            (input.advance.ledgerEvolution.destination sourceEntry).1)
          (fun entry => DebtActivationLedger.stepLedgerEvolution_destination_origin
            birth.sourceLedger.support input.advance.event entry)
      · exact Function.LeftInverse.injective
          (g := fun targetEntry =>
            (input.advance.ledgerEvolution.origin targetEntry).1)
          (fun entry => DebtActivationLedger.stepLedgerEvolution_origin_destination
            birth.sourceLedger.support input.advance.event entry)

def restructuringCompiler :
    SourceNativeRestructuringLedgerCompiler (source input) where
  ledgerCompiler := ledgerCompiler input
  restructuringLaw := restructuringLaw input
  certifyRestructuring := restructuringCertification input

def restructuringSource : SourceNativeRestructuringLedgerSource W V where
  source := source input
  compiler := restructuringCompiler input

def projectionLaw :
    SourceNativeProjectionLaw (restructuringSource input).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_phase} _occurrence => PUnit
  InactiveAt := fun _ {_phase} _occurrence => PEmpty
  classify := fun _ {_phase} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {_phase} _occurrence _active => PUnit
  project := fun _ {_phase} _occurrence _active => PUnit.unit

def eventInventoryAdmission :
    SourceNativeCompleteEventInventoryAdmission (restructuringSource input) :=
  SourceNativeCompleteEventInventoryAdmission.refl (restructuringSource input)
    (by
      intro phase occurrence terminalEvent terminal_eq
      cases phase with
      | pending => exact nomatch terminalEvent
      | paid =>
          constructor
          rintro ⟨outgoing, successor⟩
          rcases outgoing with ⟨support, event⟩
          cases event
          exact nomatch successor)

def authoritySource : SourceNativeAuthoritySource W V where
  restructuringSource := restructuringSource input
  eventInventoryAdmission := eventInventoryAdmission input
  lawSurface := .rootSemantic W
  projectionLaw := projectionLaw input

def authoritativeRoot : SourceNativeAuthoritativeRootClosure W V where
  source := authoritySource input
  emitted := emitted input
  compiler_commutes := by intro phase; cases phase <;> trivial

def pendingVisit : RootVisit (authoritativeRoot input).toRoot :=
  (authoritativeRoot input).toRoot.initialVisit

def paidVisit : RootVisit (authoritativeRoot input).toRoot :=
  (pendingVisit input).next rfl

def pendingTemporalVisit : SourceNativeTemporalVisitAt
    (authoritativeRoot input).toLedgerRoot :=
  .finite (pendingVisit input)

/-- The initial patch selects the freshly born debt row. -/
def pendingDebtGeneratedRow :
    ((authoritativeRoot input).toLedgerRoot.generatedAtTemporalVisit
      (pendingTemporalVisit input)).GeneratedEntryRowAt birth.debtEntry :=
  (((authoritativeRoot input).toLedgerRoot.generatedAtTemporalVisit
    (pendingTemporalVisit input)).canonicalGeneratedEntryRow?
      birth.debtEntry).get (by rfl)

/-- Exact initial causal-entry authority for the born terminal claim. -/
def pendingDebtCausalAuthority :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      (authoritativeRoot input) (pendingTemporalVisit input)
      birth.debtEntry :=
  SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (authoritativeRoot input) birth.debtEntry
      (pendingDebtGeneratedRow input)

/-- The paid row is the same compiler payment's canonical destination. -/
theorem paidTargetEntry_eq :
    (authoritativeRoot input).toLedgerRoot.canonicalTargetEntryAtNext
      (current := Phase.pending) (next := Phase.paid) rfl
        birth.debtEntry = input.advance.targetCurrent.entry :=
  rfl

/-- Causal authority crosses only the exact strict root write. -/
def paidDebtCausalAuthority :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      (authoritativeRoot input)
      ((pendingTemporalVisit input).next rfl)
      ((authoritativeRoot input).toLedgerRoot.canonicalTargetEntryAtNext
        (current := Phase.pending) (next := Phase.paid) rfl
          birth.debtEntry) :=
  (pendingDebtCausalAuthority input).next rfl

/-- The target occurrence discharges the exact paid debt row. -/
def paidDebtTerminal : LedgerEntryTerminalAt W
    input.advance.targetCurrent.entry :=
  input.terminal.ledgerEvolution.discharge
    input.advance.targetCurrent.entry

theorem pending_generated_is_exact_payment :
    (authoritativeRoot input).generatedLedgerAt .pending =
      .nativeWrite PUnit.unit rfl (emitted input .paid)
        input.advance.ledgerEvolution :=
  rfl

theorem paid_generated_is_exact_terminal :
    (authoritativeRoot input).generatedLedgerAt .paid =
      .faithfulTerminal PUnit.unit rfl input.terminal.ledgerEvolution :=
  rfl

theorem paid_debt_disposition_is_terminal :
    ((authoritativeRoot input).generatedLedgerAt .paid).entryDisposition
      input.advance.targetCurrent.entry =
        .terminal (paidDebtTerminal input) :=
  rfl

end

end GatedClaimPaidRoot
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
