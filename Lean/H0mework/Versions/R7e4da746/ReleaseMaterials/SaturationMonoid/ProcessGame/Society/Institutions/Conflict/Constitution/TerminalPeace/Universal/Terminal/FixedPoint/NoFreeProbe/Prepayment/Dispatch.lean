import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Gate
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Assessment
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {View : Type*}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum
local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "Offer" => ProductionOffer Party Good Port Technology Instrument
local notation "Slot" => Due Party Good Port Technology Instrument

inductive Reply
  | ordinary (result : NoFreeProbe.PublicReply)
  | prepaid (result : Verdict)
  deriving DecidableEq

structure Observation where
  opensAt : ℚ
  landsAt : ℚ
  reply : Reply
  deriving DecidableEq

private def revisionOnly (answers : RevisionAnswers Party Good Port Technology Instrument) :
    Replies Party Good Port Technology Instrument :=
  ⟨fun _ _ _ _ => false, answers⟩

variable (tariff : Tariff Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

def ordinary (revision : Option Offer) : NoFreeProbe.Step tariff (revisionOnly replies.revision) current :=
  NoFreeProbe.advance tariff (revisionOnly replies.revision) current ⟨revision, []⟩

theorem ordinary_has_no_charge (revision : Option Offer) :
    (ordinary tariff replies current revision).paidWire = none := by
  cases revision with
  | none => rfl
  | some offer =>
    simp only [ordinary, NoFreeProbe.advance, revisionOnly]
    cases inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer <;> rfl

private theorem ordinary_is_renewal (revision : Option Offer)
    (noRevision : (ordinary tariff replies current revision).reply ≠ .revised) :
    ordinary tariff replies current revision = .renewed := by
  have unpaid := ordinary_has_no_charge tariff replies current revision
  cases actual : ordinary tariff replies current revision with
  | renewed => rfl
  | revised offer kit approved => exact (noRevision (actual ▸ rfl)).elim
  | reviewed wire signed paid => rw [actual] at unpaid; contradiction

variable (see : Current (seed := seed) (cut := cut) (community := community) origin people quantum → View)
  (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)

/-- A revision already admitted on the original source owns the slot.
Otherwise the queue can select only a whole-fibre payment order. -/
def selectInAgenda (reply : NoFreeProbe.PublicReply) (visible : View) (now : ℚ) (packets : List Packet) :
    Option { wire : Packet // CanPrepay see tariff home orders visible now wire } :=
  if reply = .revised then none else selectOrder see tariff home orders visible now packets

def selected (due : Slot) :
    Option { wire : Packet //
      CanPrepay see tariff home orders (see current) current.physical.raw.clock wire } :=
  selectInAgenda tariff see home orders (ordinary tariff replies current due.revision).reply
    (see current) current.physical.raw.clock due.packets

inductive Step where
  | ordinary (due : NoFreeProbe.Step tariff (revisionOnly replies.revision) current)
      (unpaid : due.paidWire = none)
  | prepaid (wire : Packet) (consented : CanPrepay see tariff home orders (see current) current.physical.raw.clock wire)
      (paid : PaidReview current (bill tariff wire))

namespace Step

variable {tariff replies current see home orders} (step : Step tariff replies current see home orders)

def round : Round current :=
  match step with
  | .ordinary due _ => due.round
  | .prepaid _ _ paid => paid.round

def next : State :=
  match step with
  | .ordinary due _ => due.next
  | .prepaid _ _ paid => assessmentNext replies paid

def reply : Reply :=
  match step with
  | .ordinary due _ => .ordinary due.reply
  | .prepaid _ _ paid => .prepaid (assessment replies paid).read

def observe : Observation :=
  ⟨current.physical.raw.clock, step.next.physical.raw.clock, step.reply⟩

def paidWire : Option Packet :=
  match step with
  | .ordinary _ _ => none
  | .prepaid wire _ _ => some wire

theorem rows : step.next.ledger.stack.balances = current.ledger.stack.balances := by
  cases step with
  | ordinary due _ => exact due.rows
  | prepaid _ _ paid => exact assessment_rows replies paid

theorem clock : current.physical.raw.clock + quantum ≤ step.next.physical.raw.clock := by
  cases step with
  | ordinary due _ => exact due.clock
  | prepaid _ _ paid => exact assessment_clock replies paid

theorem physical : step.round.next.physical = step.next.physical := by
  cases step with
  | ordinary due unpaid =>
    cases due with
    | renewed | revised => rfl
    | reviewed _ _ _ => contradiction
  | prepaid _ _ _ => rfl

theorem keepsPublicTerms : KeepsPublicTerms current.programme step.next.programme := by
  cases step with
  | ordinary due _ => exact due.keepsPublicTerms
  | prepaid _ _ paid =>
    change KeepsPublicTerms current.programme paid.round.next.programme
    rw [paid.programme]
    exact .refl _

end Step

def writeSelected (due : Slot)
    (order : Option { wire : Packet // CanPrepay see tariff home orders (see current) current.physical.raw.clock wire }) :
    Step tariff replies current see home orders :=
  match order with
  | none => .ordinary (ordinary tariff replies current due.revision) (ordinary_has_no_charge tariff replies current due.revision)
  | some ⟨wire, consent⟩ =>
    .prepaid wire consent
      ((consent.budget current rfl rfl).write (tariff.positive wire.attempted))

def advance (due : Slot) : Step tariff replies current see home orders :=
  writeSelected tariff replies current see home orders due (selected tariff replies current see home orders due)

theorem charged_wire_is_the_selected_order (due : Slot) :
    (advance tariff replies current see home orders due).paidWire =
      (selected tariff replies current see home orders due).map Subtype.val := by
  cases found : selected tariff replies current see home orders due with
  | none => simp only [advance, found, writeSelected, Step.paidWire, Option.map_none]
  | some order =>
    obtain ⟨wire, consent⟩ := order
    simp only [advance, found, writeSelected, Step.paidWire, Option.map_some]

theorem unpaid_order_is_the_exact_ordinary_write (due : Slot)
    (unpaid : (advance tariff replies current see home orders due).paidWire = none) :
    advance tariff replies current see home orders due =
      .ordinary (ordinary tariff replies current due.revision) (ordinary_has_no_charge tariff replies current due.revision) := by
  rw [charged_wire_is_the_selected_order] at unpaid
  have noSelection := Option.map_eq_none_iff.mp unpaid
  simp only [advance, noSelection, writeSelected]

theorem a_selected_order_has_its_own_prepaid_receipt (due : Slot) {wire : Packet}
    (actual : (advance tariff replies current see home orders due).paidWire = some wire) :
    ∃ (consented : CanPrepay see tariff home orders (see current) current.physical.raw.clock wire)
      (paid : PaidReview current (bill tariff wire)),
      advance tariff replies current see home orders due = .prepaid wire consented paid := by
  generalize same : advance tariff replies current see home orders due = step at actual ⊢
  cases step with
  | ordinary _ _ => contradiction
  | prepaid submitted consented paid =>
    have identity : submitted = wire := Option.some.inj actual
    subst wire
    exact ⟨consented, paid, rfl⟩

theorem assessment_uses_the_exact_ordinary_clock (due : Slot) :
    (advance tariff replies current see home orders due).observe.landsAt =
      (ordinary tariff replies current due.revision).observation.landsAt := by
  unfold advance
  cases found : selected tariff replies current see home orders due with
  | none => rfl
  | some order =>
    obtain ⟨wire, consent⟩ := order
    have noRevision : (ordinary tariff replies current due.revision).reply ≠ .revised := by
      intro revised
      simp [selected, selectInAgenda, revised] at found
    have quietClock : (ordinary tariff replies current due.revision).observation.landsAt = current.move.next.clock := by
      rw [ordinary_is_renewal tariff replies current due.revision noRevision]
      exact congrArg RawCurrent.clock
        (productiveRound_reads_selected_production current .renew .renewed current.programme current.recipe).2.1
    exact (assessment_exact_clock replies ((consent.budget current rfl rfl).write
      (tariff.positive wire.attempted))).trans quietClock.symm

theorem an_approved_revision_keeps_the_exact_due_write (due : Slot)
    (revision : (ordinary tariff replies current due.revision).reply = .revised) :
    advance tariff replies current see home orders due =
      .ordinary (ordinary tariff replies current due.revision) (ordinary_has_no_charge tariff replies current due.revision) := by
  simp only [advance, selected, selectInAgenda, if_pos revision, writeSelected]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
