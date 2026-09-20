import H0mework.Foundation.Responsibility.DebtLedgerReadback
import H0mework.Foundation.Responsibility.DebtInstallation

/-!
# Positive root for a direct debt-activation source

A source-generated strict step is installed as the sole live-to-paid native
write of the same activation world.  A source-generated support terminal then
closes the paid whole ledger.  The write patch is an empty exceptional family
over one generated transported remainder whose evolution is exactly the
canonical `stepLedgerEvolution`.

This kernel creates neither a pending/gated root nor an obstruction successor.
The direct-U8 path owns the source-generated obstruction branch.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedDebtActivationDirectPositive

open DebtActivationLedger
open DebtActivationWorld
open RootGeneratedDebtActivationDirect

noncomputable section

universe u

/-- Exact positive image already selected by one direct activation source. -/
structure GeneratedPositiveAt
    {N : WorldRelationNetwork.{u}} {LowerV : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N LowerV}
    {lowerCurrent : LowerV.Current}
    (activation : OccurrenceIndexedSourceAt lower lowerCurrent) : Type u where
  private mk ::
  target : activation.law.DebtState
  step : activation.law.StepAt activation.state target
  generated_eq : activation.generatedDisposition = .step step
  terminal : activation.law.SupportTerminalAt target

def GeneratedPositiveAt.ofGenerated
    {N : WorldRelationNetwork.{u}} {LowerV : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N LowerV}
    {lowerCurrent : LowerV.Current}
    {activation : OccurrenceIndexedSourceAt lower lowerCurrent}
    {target : activation.law.DebtState}
    (step : activation.law.StepAt activation.state target)
    (generated_eq : activation.generatedDisposition = .step step)
    (terminal : activation.law.SupportTerminalAt target) :
    GeneratedPositiveAt activation :=
  ⟨target, step, generated_eq, terminal⟩

variable {N : WorldRelationNetwork.{u}} {LowerV : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure N LowerV}
variable {lowerCurrent : LowerV.Current}
variable {activation : OccurrenceIndexedSourceAt lower lowerCurrent}
variable (positive : GeneratedPositiveAt activation)

abbrev World := activation.World

inductive Current : Type u
  | live
  | paid

abbrev supportAt : Current.{u} → activation.World.Support
  | .live => activation.liveLedger.support
  | .paid => (activeLedger activation.lowerSupport positive.target).support

def vocabulary : Vocabulary.{u} where
  Current := Current.{u}
  Anchor := activation.World.Anchor
  Incidence := activation.World.Incidence
  Lineage := activation.World.Lineage
  anchorAt := fun current => activation.World.anchorAt (supportAt positive current)
  incidenceAt := fun current =>
    activation.World.incidenceAt (supportAt positive current)
  lineageAt := fun current =>
    activation.World.lineageAt (supportAt positive current)
  NativeWriteAt
    | .live => ULift.{u, 0}
        (PLift (activation.generatedDisposition = .step positive.step))
    | .paid => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt
    | .live => PEmpty
    | .paid => activation.law.SupportTerminalAt positive.target
  nativeTarget := by
    intro current write
    cases current with
    | live => exact .paid
    | paid => exact nomatch write
  relationTarget := fun event => nomatch event
  continuedTarget := fun event => nomatch event
  redirectTarget := fun event => nomatch event

abbrev V := vocabulary positive

def paymentWrite : (V positive).NativeWriteAt .live :=
  ULift.up (PLift.up positive.generated_eq)

inductive EventAt : (V positive).Current → activation.World.Support → Type u
  | payment : EventAt .live (supportAt positive .live)
  | terminal : EventAt .paid (supportAt positive .paid)

abbrev BaseInventoryIndex : Type u :=
  lower.source.source.law.AffectedInventoryAt activation.lowerOccurrence.2

def baseInventory : ConstructivePresentation
    (BaseInventoryIndex (activation := activation))
    (OpenResponsibilityAt N activation.lowerSupport) :=
  lower.source.source.law.affectedInventoryPresentation
    activation.lowerOccurrence.2

def eventAlgebra : SourceNativeEventAlgebra activation.World (V positive) where
  EventAt := EventAt positive
  compile := by
    intro current support event
    cases event with
    | payment => exact .nativeWrite (paymentWrite positive)
    | terminal => exact .faithfulTerminal positive.terminal
  AffectedInventoryAt := fun _ =>
    Option (BaseInventoryIndex (activation := activation))
  affectedInventoryPresentation := by
    intro current support event
    cases event with
    | payment =>
        exact activeInventoryPresentation activation.state
          (baseInventory (activation := activation))
    | terminal =>
        exact activeInventoryPresentation positive.target
          (baseInventory (activation := activation))
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

def rootSource : SourceNativeSource activation.World (V positive) where
  initial := .live
  law := eventAlgebra positive

def paymentOccurrence :
    (rootSource positive).toRootSource.actual.OccurrenceAt .live :=
  ⟨supportAt positive .live, .payment⟩

def terminalOccurrence :
    (rootSource positive).toRootSource.actual.OccurrenceAt .paid :=
  ⟨supportAt positive .paid, .terminal⟩

structure ExactTransitionAt
    {current : (V positive).Current}
    (occurrence : (rootSource positive).toRootSource.actual.OccurrenceAt current)
    {targetSupport : activation.World.Support}
    (sourceEntry : OpenResponsibilityAt activation.World occurrence.1)
    (targetEntry : OpenResponsibilityAt activation.World targetSupport) : Type u where
  evolution : LedgerEntryEvolutionAt activation.World sourceEntry targetEntry

def paymentEvolution : LedgerWriteEvolutionAt activation.World
    ⟨supportAt positive .live⟩ ⟨supportAt positive .paid⟩ :=
  stepLedgerEvolution activation.lowerSupport positive.step

def paymentRemainderEventAt
    {current : (V positive).Current}
    (_occurrence : (rootSource positive).toRootSource.actual.OccurrenceAt current)
    (targetSupport : activation.World.Support) : Type u :=
  match current with
  | .live => ULift.{u, 0}
      (PLift (targetSupport = supportAt positive .paid))
  | .paid => PEmpty

def paymentRemainderSource : LedgerTransportedRemainderSourceAt
    (rootSource positive) (ExactTransitionAt positive) where
  OccurrenceAt := paymentRemainderEventAt positive
  emit? := by
    intro current occurrence targetSupport
    cases current with
    | paid => exact none
    | live =>
        classical
        by_cases target_eq : targetSupport = supportAt positive .paid
        · exact some (ULift.up (PLift.up target_eq))
        · exact none
  compileEvolution := by
    intro current occurrence targetSupport event
    rcases occurrence with ⟨sourceSupport, rootEvent⟩
    cases rootEvent with
    | terminal => exact nomatch event
    | payment =>
        rcases event with ⟨⟨target_eq⟩⟩
        cases target_eq
        exact paymentEvolution positive
  compileExact := by
    intro current occurrence targetSupport event
    rcases occurrence with ⟨sourceSupport, rootEvent⟩
    cases rootEvent with
    | terminal => exact nomatch event
    | payment =>
        rcases event with ⟨⟨target_eq⟩⟩
        cases target_eq
        exact {
          destination := fun entry =>
            ⟨((paymentEvolution positive).destination entry).2⟩
          origin := fun entry =>
            ⟨((paymentEvolution positive).origin entry).2⟩ }

abbrev writeRowSource : LedgerWriteRowSourceAt (rootSource positive)
    (ExactTransitionAt positive) where
  IncidenceOccurrenceAt := fun _ _ _ _ => PEmpty
  compileEvolution := fun event => nomatch event
  compileExact := fun event => nomatch event
  transportedRemainderSource := paymentRemainderSource positive

def emptyPaymentRows : FiniteGeneratedLedgerWriteRowsAt
    (writeRowSource positive) (paymentOccurrence positive)
    ⟨supportAt positive .paid⟩ where
  size := 0
  sourceEntryAt := Fin.elim0
  targetEntryAt := Fin.elim0
  rowAt := fun index => Fin.elim0 index

def emptyPaymentCoverage :
    LedgerTransportedRemainderCoverageAt (emptyPaymentRows positive) where
  destinationIndex := fun _ => none
  originIndex := fun _ => none

theorem paymentRemainderSource_emit :
    (paymentRemainderSource positive).emit? (paymentOccurrence positive)
      (supportAt positive .paid) = some (ULift.up (PLift.up rfl)) := by
  classical
  simp [paymentRemainderSource, paymentOccurrence]
  congr 2

def generatedPaymentRemainder : GeneratedLedgerTransportedRemainderAt
    (writeRowSource positive) (paymentOccurrence positive)
    ⟨supportAt positive .paid⟩ :=
  (writeRowSource positive).generateTransportedRemainder
    (paymentOccurrence positive) ⟨supportAt positive .paid⟩
    (ULift.up (PLift.up rfl)) (paymentRemainderSource_emit positive)

def paymentPatch : FiniteGeneratedLedgerWritePatchAt (writeRowSource positive)
    (paymentOccurrence positive) ⟨supportAt positive .paid⟩ :=
  .transportedRemainder (emptyPaymentRows positive)
    (emptyPaymentCoverage positive) (generatedPaymentRemainder positive)

private theorem ledgerWriteEvolution_ext
    {sourceLedger targetLedger : CompleteLiveLedgerAt activation.World}
    (left right : LedgerWriteEvolutionAt activation.World sourceLedger targetLedger)
    (destination : ∀ entry, left.destination entry = right.destination entry)
    (origin : ∀ entry, left.origin entry = right.origin entry) : left = right := by
  cases left
  cases right
  congr
  · funext entry; exact destination entry
  · funext entry; exact origin entry

@[simp] theorem paymentPatch_evolution :
    (paymentPatch positive).toLedgerWriteEvolution = paymentEvolution positive := by
  classical
  apply ledgerWriteEvolution_ext
  · intro entry
    change (generatedPaymentRemainder positive).evolution.destination entry = _
    rfl
  · intro entry
    change (generatedPaymentRemainder positive).evolution.origin entry = _
    rfl

/-- The live root event inhabits the previous direct installation mouth with
the exact source-generated step. -/
def directStepInstallation : NativeStepInstallationAt activation positive.step
    (rootSource positive) .live EventAt.payment where
  write := paymentWrite positive
  structural_eq := rfl
  targetEvent := EventAt.terminal

def generatedDirectStepInstallation :
    GeneratedSourceNativeLedgerInstallationAt activation
      (rootSource positive) .live EventAt.payment :=
  RootGeneratedDebtActivationDirect.generatedStepInstallation
    positive.generated_eq (directStepInstallation positive)

inductive SupportSettlementEventAt :
    {current : (V positive).Current} →
    (rootSource positive).toRootSource.actual.OccurrenceAt current → Type u
  | generated : SupportSettlementEventAt (terminalOccurrence positive)

def terminalRowSource : LedgerTerminalRowSourceAt (rootSource positive) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun event => nomatch event
  supportSettlementSource := {
    OccurrenceAt := SupportSettlementEventAt positive
    emit? := by
      intro current occurrence
      rcases occurrence with ⟨support, event⟩
      cases event with
      | payment => exact none
      | terminal => exact some .generated
    compile := by
      intro current occurrence event
      cases event with
      | generated =>
          exact debtSupportTerminalReceipt activation.lowerSupport
            positive.terminal }

def generatedTerminalSettlement : GeneratedLedgerSupportSettlementAt
    (terminalRowSource positive) (terminalOccurrence positive) :=
  ((terminalRowSource positive).generateSupportSettlement?
    (terminalOccurrence positive)).get (by rfl)

def terminalPatch : SourceGeneratedLedgerTerminalPatchAt
    (terminalRowSource positive) (terminalOccurrence positive) :=
  .supportSettlement (generatedTerminalSettlement positive)

@[simp] theorem terminalPatch_evolution :
    (terminalPatch positive).toLedgerTerminalEvolution =
      supportTerminalLedgerEvolution activation.lowerSupport positive.terminal :=
  rfl

def generatedLedger : {current : (V positive).Current} →
    (occurrence :
      (rootSource positive).toRootSource.actual.OccurrenceAt current) →
    SourceNativeLedgerEvolutionAt (rootSource positive) occurrence := by
  intro current occurrence
  rcases occurrence with ⟨support, event⟩
  cases event with
  | payment =>
      exact .nativeWrite (paymentWrite positive) rfl
        (show (rootSource positive).toRootSource.actual.OccurrenceAt
            ((V positive).nativeTarget (paymentWrite positive)) from
          terminalOccurrence positive)
        (paymentPatch positive).toLedgerWriteEvolution
  | terminal =>
      exact .faithfulTerminal positive.terminal rfl
        (terminalPatch positive).toLedgerTerminalEvolution

@[simp] theorem generatedLedger_payment :
    generatedLedger positive (paymentOccurrence positive) =
      .nativeWrite (paymentWrite positive) rfl
        (show (rootSource positive).toRootSource.actual.OccurrenceAt
            ((V positive).nativeTarget (paymentWrite positive)) from
          terminalOccurrence positive)
        (paymentPatch positive).toLedgerWriteEvolution := by
  rfl

def ledgerCompiler : SourceNativeLedgerCompiler (rootSource positive) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt positive
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun exact => exact.evolution.toDebtLineage.lineage_eq
  writeRowSource := writeRowSource positive
  terminalRowSource := terminalRowSource positive
  compile := generatedLedger positive
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event with
    | payment => exact ⟨paymentPatch positive, rfl⟩
    | terminal => exact ⟨terminalPatch positive, rfl⟩

/-- The root's live compiler image is exactly the explicit direct step
installation.  `generatedDirectStepInstallation` separately proves that this
same installation is selected by the source-generated disposition. -/
theorem liveCompiler_eq_directStepInstallation :
    (ledgerCompiler positive).compile (paymentOccurrence positive) =
      NativeStepInstallationAt.generated (directStepInstallation positive) := by
  rw [show (ledgerCompiler positive).compile (paymentOccurrence positive) =
      generatedLedger positive (paymentOccurrence positive) from rfl]
  rw [generatedLedger_payment, paymentPatch_evolution]
  rfl

/-- One theorem retains both source selection of the direct mouth and exact
identity of the root compiler image with that selected step installation. -/
theorem liveCompiler_factors_generatedDirectMouth :
    Nonempty (GeneratedSourceNativeLedgerInstallationAt activation
      (rootSource positive) .live EventAt.payment) ∧
      (ledgerCompiler positive).compile (paymentOccurrence positive) =
        NativeStepInstallationAt.generated (directStepInstallation positive) :=
  ⟨⟨generatedDirectStepInstallation positive⟩,
    liveCompiler_eq_directStepInstallation positive⟩

def ledgerSource : SourceNativeLedgerSource activation.World (V positive) where
  source := rootSource positive
  ledgerCompiler := ledgerCompiler positive

def ledgerRoot : SourceNativeLedgerRootClosure activation.World (V positive) where
  source := ledgerSource positive
  emitted
    | .live => paymentOccurrence positive
    | .paid => terminalOccurrence positive
  compiler_commutes := by
    intro current
    cases current with
    | live => rfl
    | paid => trivial

end


end RootGeneratedDebtActivationDirectPositive
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
