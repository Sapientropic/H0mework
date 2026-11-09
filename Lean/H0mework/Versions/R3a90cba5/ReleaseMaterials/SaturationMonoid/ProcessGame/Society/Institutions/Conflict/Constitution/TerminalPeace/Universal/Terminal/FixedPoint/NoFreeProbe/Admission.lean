import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Tariff
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open private positive_expense_is_listed from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

/-- Tender and identity fields are untrusted. Admission checks them
against the original current and its personal answer lane. -/
structure Wire (Party Good Port Technology Instrument : Type) where
  home : AnyAuthoritativeRootCurrent.{0}
  clock : ℚ
  sender : Party
  payer : Party
  attempted : RawEvent Party Good Port Technology Instrument
  tender : Bundle Good

local notation "Packet" => Wire Party Good Port Technology Instrument

variable (tariff : Tariff Party Good Port Technology Instrument)

def bill (wire : Packet) : ReviewBid Party Good Port Technology Instrument :=
  ⟨wire.payer, wire.attempted, tariff.port, tariff.parts wire.attempted⟩

/-- This first screen uses only the public tariff and the packet. It
does not ask the current for a signature, stock, or a protected verdict. -/
def fundingScreen (wire : Packet) : Bool :=
  decide (wire.sender = wire.payer) &&
    ((bill tariff wire).expenses.map Prod.fst).all fun good =>
      decide (amount Good (bill tariff wire).expenses good ≤ amount Good wire.tender good)

variable (replies : Replies Party Good Port Technology Instrument)
  (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))

/-- This check has no attack assessment. It binds a full tender and the
payer's own answer to the bill for this literal word at this original cut. -/
structure Admitted (wire : Packet) : Prop where
  home : wire.home = current.ledger.resident.erase
  fresh : wire.clock = current.physical.raw.clock
  sender : wire.sender = wire.payer
  standing : wire.sender ∈ people
  ownAnswer : replies.review current.ledger.resident.erase current.physical.raw (bill tariff wire) wire.sender = true
  full : ∀ good, amount Good (bill tariff wire).expenses good ≤ amount Good wire.tender good
  legal : ReviewLegal current (bill tariff wire)
  fits : ReviewFits current.recipe (bill tariff wire).fee
  surplus : ∃ person good, (bill tariff wire).fee person good < current.recipe.gain person good

theorem Admitted.passes_public_screen {wire : Packet}
    (paid : Admitted tariff replies current wire) : fundingScreen tariff wire = true := by
  simp only [fundingScreen, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨paid.sender, fun good _ => paid.full good⟩

def checked (wire : Packet) : Option {packet : Packet // Admitted tariff replies current packet} := by
  classical
  exact if fundingScreen tariff wire then
    if paid : Admitted tariff replies current wire then some ⟨wire, paid⟩ else none
  else none

theorem checked_eq_none_iff (wire : Packet) :
    checked tariff replies current wire = none ↔ ¬ Admitted tariff replies current wire := by
  classical
  by_cases paid : Admitted tariff replies current wire
  · simp [checked, paid, paid.passes_public_screen]
  · simp [checked, paid]

/-- The position of a rejected packet in the untrusted input is never
an original dispatch address. Only the selected sealed candidate escapes. -/
def select (wires : List Packet) : Option {packet : Packet // Admitted tariff replies current packet} :=
  wires.findSome? (checked tariff replies current)

def ZeroTender (wire : Packet) : Prop := ∀ good, amount Good wire.tender good = 0

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem zero_tender_stops_before_the_current_is_read (wire : Packet) (zero : ZeroTender wire) :
    fundingScreen tariff wire = false := by
  apply Bool.eq_false_iff.mpr
  intro passed
  obtain ⟨good, positive⟩ := tariff.positive wire.attempted
  have listed := positive_expense_is_listed (bill tariff wire) good positive
  simp only [fundingScreen, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at passed
  have full := passed.2 good listed
  rw [zero good] at full
  exact (not_lt_of_ge full) positive

theorem zero_tender_cannot_be_admitted (wire : Packet) (zero : ZeroTender wire) :
    ¬ Admitted tariff replies current wire := by
  intro paid
  obtain ⟨good, positive⟩ := tariff.positive wire.attempted
  have full := paid.full good
  rw [zero good] at full
  exact (not_lt_of_ge full) positive

theorem an_admitted_wire_uses_its_payers_own_answer {wire : Packet}
    (paid : Admitted tariff replies current wire) :
    replies.review current.ledger.resident.erase current.physical.raw (bill tariff wire) wire.payer = true := by
  simpa only [paid.sender] using paid.ownAnswer

theorem mismatched_sender_is_rejected (wire : Packet) (proxy : wire.sender ≠ wire.payer) :
    checked tariff replies current wire = none :=
  (checked_eq_none_iff tariff replies current wire).mpr fun paid => proxy paid.sender

theorem an_absent_personal_reply_is_rejected (wire : Packet)
    (absent : replies.review current.ledger.resident.erase current.physical.raw (bill tariff wire) wire.payer = false) :
    checked tariff replies current wire = none := by
  apply (checked_eq_none_iff tariff replies current wire).mpr
  intro paid
  have answer := an_admitted_wire_uses_its_payers_own_answer tariff replies current paid
  rw [absent] at answer
  contradiction

theorem an_earlier_stamp_is_rejected (wire : Packet) (earlier : wire.clock < current.physical.raw.clock) :
    checked tariff replies current wire = none :=
  (checked_eq_none_iff tariff replies current wire).mpr fun paid => (ne_of_lt earlier) paid.fresh

theorem a_different_root_is_rejected (wire : Packet) (other : wire.home ≠ current.ledger.resident.erase) :
    checked tariff replies current wire = none :=
  (checked_eq_none_iff tariff replies current wire).mpr fun paid => other paid.home

theorem a_tender_fragment_is_rejected (wire : Packet) (good : Good)
    (short : amount Good wire.tender good < amount Good (bill tariff wire).expenses good) :
    checked tariff replies current wire = none :=
  (checked_eq_none_iff tariff replies current wire).mpr fun paid => (not_le_of_gt short) (paid.full good)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
