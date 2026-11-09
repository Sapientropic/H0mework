import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Visit

set_option autoImplicit false

open private sameSupportLedger sameSupportLedger_heq sameSupportLedger_rows from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Root.Financial.Installation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

namespace Frame

variable {law : DebtActivationLaw} {base next : WorldRelationNetwork}
  {origin target : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldShape : Shape law origin.frame.N base} {phase : law.DebtState} {wait : law.TransportAt phase phase}
  (current : Resident oldShape phase wait)
  {newShape : Shape law target.frame.N next} {future : law.DebtState}
  (frame : Frame target newShape future) (waiting : law.TransportAt future future)

def inherit := QueryHistory.freeze current.root.toAuthoritativeRoot.source.projectionLaw
  (current.root.emitted current.visit.current) (Compiler.ledgerSource (frame.flow waiting))

end Frame

namespace Sequential

variable {law : DebtActivationLaw} {joint : WorldRelationNetwork}
  {origin target : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldShape : Shape law origin.frame.N joint} {phase : law.DebtState} {wait : law.TransportAt phase phase}
  (current : Resident oldShape phase wait)
  {newShape : Shape law target.frame.N joint} {future : law.DebtState}
  (frame : Frame target newShape future) (waiting : law.TransportAt future future)
  (same : frame.initialSupport = current.support)

local notation "root" => frame.rooted waiting (Frame.inherit current frame waiting)

def translatedEntry : OpenResponsibilityAt joint frame.initialSupport :=
  (sameSupportLedger same).forward current.entry

theorem translatedEntry_heq : HEq (translatedEntry current frame same) current.entry := by
  change HEq ((sameSupportLedger same).forward current.entry) current.entry
  generalize frame.initialSupport = value at same ⊢
  cases same
  rfl

private def occurrence : ConstructivePresentation
    (current.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.visit.current)
    ((root).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (frame.initial waiting).current) where
  forward := fun _ => (root).emitted (frame.initial waiting).current
  backward := fun _ => current.root.emitted current.visit.current
  backward_forward := fun actual => (current.unique actual).symm
  forward_backward := fun actual => (Compiler.occurrence_eq_emitted (frame.flow waiting) actual).symm

set_option maxHeartbeats 700000 in
def action (balance : ℚ) (event : ExactTemporalCausalRootEventAt
    current.root.toAuthoritativeRoot.toLedgerRoot current.visit) :
    SourceNativeSequentialActualActionTargetAt current.root current.visit event current.entry current.authority := by
  rw [event.eq_generated]
  let ledger := sameSupportLedger same
  exact {
    TargetN := joint
    translation := Ingress.identityTranslation joint
    TargetV := Compiler.V (frame.flow waiting)
    targetRoot := root
    targetTheory := TheoryState.rootSemantic joint
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrence current frame waiting
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq same
    initialOpenLedger := ledger
    initialOpenLedger_heq := sameSupportLedger_heq same
    initialLedger_responsibility_commutes := fun row => ((sameSupportLedger_rows same).1 row).symm
    initialLedger_claim_commutes := fun row => ((sameSupportLedger_rows same).2.1 row).symm
    initialLedger_budget_conservative := fun row => ((sameSupportLedger_rows same).2.2.1 row).le
    initialLedgerNoFresh := fun row => ⟨⟨ledger.backward row, ⟨(sameSupportLedger_rows same).2.2.2 row⟩⟩⟩
    translatedSourceEntryRow := Compiler.generatedRow (frame.flow waiting) (frame.initial waiting)
      (translatedEntry current frame same)
    firstSuccessor := frame.first waiting
    canonical_targetNextVisit_eq := Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (root) (frame.initial waiting) (frame.first waiting)
    Answer := ℚ
    answer := balance
    Receipt := fun amount => ULift.{3,0} (PLift (amount = balance))
    receipt := ⟨⟨rfl⟩⟩ }

def program (balance : ℚ) :
    SourceNativeSequentialActualActionProgramAt current.root current.visit current.entry current.authority where
  targetAt := action current frame waiting same balance

def generated (balance : ℚ) := (program current frame waiting same balance).generate
  (current.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.visit)

theorem generated_enters_the_actual_frame (balance : ℚ)
    (repair : (frame.initialWrite.val.destination (translatedEntry current frame same)).1 =
      newShape.repair (sourceSupport target) future) :
    (⟨joint, (generated current frame waiting same balance).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) =
        (frame.resident waiting (Frame.inherit current frame waiting)
          (translatedEntry current frame same) repair).erase :=
  congrArg (fun visit => (⟨joint, visit⟩ : AnyAuthoritativeRootCurrent))
    (generated current frame waiting same balance).target.targetAnswerAndNext_next_eq

end Sequential

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
