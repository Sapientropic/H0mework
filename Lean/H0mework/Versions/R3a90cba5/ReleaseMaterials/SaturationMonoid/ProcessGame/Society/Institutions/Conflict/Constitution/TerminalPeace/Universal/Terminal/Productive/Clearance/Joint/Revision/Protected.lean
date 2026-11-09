import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Inventory
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation (Key)
open Reparation.Actual (Occurrence ReceiptAnswers Script)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (answers : ReceiptAnswers seed)
  (front : Script Party Good Port Technology Instrument)
  (key : Key Party Good) (purpose : Port) (quantity : ℚ)

local notation "Reserve" => reserveAt loss front
local notation "After" => (front ++ installment purpose key quantity)

abbrev ProtectedIssue :=
  InstallmentIssue loss answers Reserve front purpose key quantity ⊕ NeedShortage loss After

def InspectablePayment : Prop :=
  CanInstallment loss answers Reserve front purpose key quantity ∧ ProtectsNeeds loss After

theorem ProtectedIssue.refutes (issue : ProtectedIssue loss answers front key purpose quantity) :
    ¬ InspectablePayment loss answers front key purpose quantity :=
  match issue with
  | .inl refused => fun pays => refused.refutes pays.1
  | .inr short => fun pays => short.refutes loss After pays.2

def inspectProtectedInstallment (ready : ReadyEntry loss front) :
    ProtectedIssue loss answers front key purpose quantity ⊕
      PLift (InspectablePayment loss answers front key purpose quantity) :=
  match inspectInstallment loss answers Reserve front purpose key quantity ready (reserveAt_nonnegative _ _ _ _) with
  | .inl refused => .inl (.inl refused)
  | .inr signed =>
    match inspectNeeds loss After with
    | .inl short => .inl (.inr short)
    | .inr keepsNeeds => .inr ⟨signed.down, keepsNeeds.down⟩

def writeProtectedRefusal (issue : ProtectedIssue loss answers front key purpose quantity) :=
  Installation.Core.publish (Occurrence.reached answers loss front) issue true

theorem the_protected_refusal_writes_the_unchanged_original_ledger
    (issue : ProtectedIssue loss answers front key purpose quantity) :
    let original := Occurrence.reached answers loss front
    let next := writeProtectedRefusal loss answers front key purpose quantity issue
    next.read = issue ∧ next.state.stack = original.stack ∧
      (⟨original.world, (Installation.Core.action original issue true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = next.state.resident.erase :=
  ⟨rfl, rfl, Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _⟩

inductive ProtectedInstallmentOutcome
  | written (paid : PaidInstallment loss answers Reserve front purpose key quantity)
      (keepsNeeds : ProtectsNeeds loss After)
  | refused (issue : ProtectedIssue loss answers front key purpose quantity)
      (visit : Installation.Core.Landed seed community (endAt seed (Occurrence.history loss ++ front))
        (ProtectedIssue loss answers front key purpose quantity))
      (same : visit = writeProtectedRefusal loss answers front key purpose quantity issue)

/-- Inspect the exact intermediate and resulting material states before
the native settlement writer can consume either signature. -/
def compileProtectedInstallment (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front) :
    ProtectedInstallmentOutcome loss answers front key purpose quantity :=
  match inspectProtectedInstallment loss answers front key purpose quantity ready with
  | .inl refused => .refused refused (writeProtectedRefusal loss answers front key purpose quantity refused) rfl
  | .inr payable =>
    .written (writeInstallment loss answers Reserve front purpose key quantity safe ready
      (reserveAt_nonnegative _ _ _ _) payable.down.1) payable.down.2

theorem compileProtectedInstallment_pays_iff (safe : Occurrence.Eligible answers loss front)
    (ready : ReadyEntry loss front) :
    (∃ paid keepsNeeds, compileProtectedInstallment loss answers front key purpose quantity safe ready =
      .written paid keepsNeeds) ↔ InspectablePayment loss answers front key purpose quantity := by
  unfold compileProtectedInstallment
  cases inspected : inspectProtectedInstallment loss answers front key purpose quantity ready with
  | inl issue =>
    constructor
    · rintro ⟨_, _, impossible⟩
      cases impossible
    · exact fun payable => (issue.refutes loss answers front key purpose quantity payable).elim
  | inr ready => exact ⟨fun _ => ready.down, fun _ => ⟨_, _, rfl⟩⟩

theorem a_failed_payment_writes_its_refusal_at_the_retained_cut
    (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front)
    (failed : ¬ InspectablePayment loss answers front key purpose quantity) :
    ∃ issue, compileProtectedInstallment loss answers front key purpose quantity safe ready =
      .refused issue (writeProtectedRefusal loss answers front key purpose quantity issue) rfl := by
  unfold compileProtectedInstallment
  split
  · exact ⟨_, rfl⟩
  · rename_i payable _
    exact (failed payable.down).elim

def compileProtectedPayment (safe : Occurrence.Eligible answers loss front) (ready : ReadyEntry loss front) :
    ProtectedInstallmentOutcome loss answers front key purpose (maximumInstallment loss answers front key) :=
  compileProtectedInstallment loss answers front key purpose _ safe ready

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
