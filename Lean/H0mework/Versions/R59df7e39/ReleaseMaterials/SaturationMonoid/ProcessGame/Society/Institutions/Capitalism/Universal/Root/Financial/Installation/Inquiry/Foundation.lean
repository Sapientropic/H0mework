import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Restructuring
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def canonicalEntry : {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (state : (world input (ProgrammeSource.N input) run).Support) →
    OpenResponsibilityAt (world input (ProgrammeSource.N input) run) state
  | _, .nil, state => ProgrammeLiving.inquiryEntrySupport input state
  | _, .step prior (.admit _), state => oldEntry (state? := state.2) (canonicalEntry prior state.1)
  | _, .step prior (.cross _ _ _ _), state => canonicalEntry prior state
  | _, .step _ (.reopen _ _ _ impossible), _ => impossible.elim

def canonicalDisposition : {current : ResponsibilityState (vocabulary input)} →
    (run : (process input).Run (.empty (vocabulary input)) current) →
    (state : (world input (ProgrammeSource.N input) run).Support) →
    (kind : WorldDispositionKind) → (world input (ProgrammeSource.N input) run).DispositionAt state kind
  | _, .nil, _, .supportSettlement => ()
  | _, .nil, state, .transfer =>
      ProgrammeWorld.transferReceipt (ProgrammeSource.observation? input) state
  | _, .nil, _, .lawSurfaceExtension => ()
  | _, .step prior (.admit _), state, .supportSettlement => canonicalDisposition prior state.1 .supportSettlement
  | _, .step prior (.admit _), state, .transfer => .inl (canonicalDisposition prior state.1 .transfer)
  | _, .step prior (.admit _), state, .lawSurfaceExtension => .inl (canonicalDisposition prior state.1 .lawSurfaceExtension)
  | _, .step prior (.cross _ _ _ _), state, kind => canonicalDisposition prior state kind
  | _, .step _ (.reopen _ _ _ impossible), _, _ => impossible.elim

namespace AccountSource

variable (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

def inquiryEntryAt {current : Current input start}
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (N input start) occurrence.1 :=
  canonicalEntry input start.account.generated occurrence.1

def inquiryU7 : U7ProducerCalculus (N input start) where
  DemandAt := fun _ => PUnit
  generateDemand := fun _ => PUnit.unit

def inquiryU7Source : U7ActualSuccessorSource (N input start) (inquiryU7 input start) where
  EventAt := SourceGeneratedU7DemandAt (inquiryU7 input start)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := id
  demandEntryAt := fun {support} {_} {_} _ => canonicalEntry input start.account.generated support

def inquiryCalculus : U7ObstructionEvolutionCalculus (N input start) (inquiryU7 input start) where
  source := inquiryU7Source input start
  compile := fun {support} {obstruction} {_} _ => {
    disposition := .redirected (successor := obstruction)
      ⟨canonicalDisposition input start.account.generated support _, rfl⟩
    demandEntryDisposition :=
      ⟨.transferred (canonicalDisposition input start.account.generated support _) rfl rfl (Nat.le_refl _), rfl⟩ }

def inquiryAudit {current : Current input start}
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) :
    SourceNativeInquiryFrontAuditAt (inquiryU7 input start) (inquiryCalculus input start)
      (TheoryState.rootSemantic (N input start)) occurrence.1 := .answered

end AccountSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
