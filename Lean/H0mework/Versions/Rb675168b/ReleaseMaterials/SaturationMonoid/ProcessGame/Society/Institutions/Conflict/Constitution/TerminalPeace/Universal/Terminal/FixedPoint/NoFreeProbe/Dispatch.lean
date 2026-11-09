import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Admission
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.PaidWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "Packet" => Wire Party Good Port Technology Instrument
local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum

/-- A public presentation receives this response off the due queue.
Its occurrence in a sender's history does not create a root visit. -/
inductive PresentationReply
  | presented
  deriving DecidableEq

def present (_wire : Packet) : PresentationReply := .presented

structure Due (Party Good Port Technology Instrument : Type) where
  revision : Option (ProductionOffer Party Good Port Technology Instrument)
  packets : List (Wire Party Good Port Technology Instrument)

inductive PublicReply
  | renewed
  | revised
  | reviewed (demandsAggression : Bool)
  deriving DecidableEq

structure Observation where
  opensAt : ℚ
  landsAt : ℚ
  reply : PublicReply
  deriving DecidableEq

variable (tariff : Tariff Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

/-- A paid branch carries the actual material write, followed by the
answer write. The remaining branches perform ordinary due production. -/
inductive Step where
  | renewed
  | revised (offer : ProductionOffer Party Good Port Technology Instrument)
      (kit : RevisionKit current.programme origin people cut.raw quantum offer)
      (approved : RevisionApproval replies.revision current.ledger.resident.erase current.physical.raw people offer)
  | reviewed (wire : Packet) (signed : Admitted tariff replies current wire)
      (paid : PaidReview current (bill tariff wire))

namespace Step

variable {tariff replies current} (step : Step tariff replies current)

def round : Round current :=
  match step with
  | .renewed => productiveRound current .renew .renewed current.programme current.recipe
  | .revised offer kit _ =>
    productiveRound current (.revise offer) .revised (reviseProgramme current.programme offer) kit.recipe
  | .reviewed _ _ paid => paid.round

def next : State :=
  match step with
  | .reviewed _ _ paid => paid.next
  | _ => step.round.next

def reply : PublicReply :=
  match step with
  | .renewed => .renewed
  | .revised _ _ _ => .revised
  | .reviewed _ _ paid => .reviewed paid.answer

def observation : Observation :=
  ⟨current.physical.raw.clock, step.next.physical.raw.clock, step.reply⟩

def paidWire : Option Packet :=
  match step with
  | .reviewed wire _ _ => some wire
  | _ => none

theorem rows : step.next.ledger.stack.balances = current.ledger.stack.balances := by
  cases step with
  | renewed | revised => exact (round _).rows
  | reviewed _ _ paid => exact paid.rows

theorem clock : current.physical.raw.clock + quantum ≤ step.next.physical.raw.clock := by
  cases step with
  | renewed | revised => exact (round _).clock
  | reviewed _ _ paid => exact paid.clock

theorem keepsPublicTerms : KeepsPublicTerms current.programme step.next.programme := by
  cases step with
  | renewed => exact .refl _
  | revised offer _ _ => exact reviseProgramme_keeps_public_terms _ offer
  | reviewed _ _ paid => exact paid.keepsPublicTerms

theorem paidWire_has_its_actual_receipt {wire : Packet} (issued : step.paidWire = some wire) :
    ∃ (signed : Admitted tariff replies current wire) (paid : PaidReview current (bill tariff wire)),
      step = .reviewed wire signed paid := by
  cases step with
  | renewed | revised => contradiction
  | reviewed candidate signed paid =>
    have same : candidate = wire := Option.some.inj issued
    subst wire
    exact ⟨signed, paid, rfl⟩

end Step

private def paidOrRenew (packets : List Packet) : Step tariff replies current :=
  match select tariff replies current packets with
  | none => .renewed
  | some ⟨wire, signed⟩ =>
    .reviewed wire signed (writePaidReview current (bill tariff wire) signed.legal signed.fits
      signed.surplus (tariff.positive wire.attempted))

/-- Signed production revisions keep their original slot. Attack traffic
can enter a due visit only through its own, fully funded source bill. -/
def advance (due : Due Party Good Port Technology Instrument) : Step tariff replies current :=
  match due.revision with
  | none => paidOrRenew tariff replies current due.packets
  | some offer =>
    match inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer with
    | .checked kit approved => .revised offer kit approved
    | _ => paidOrRenew tariff replies current due.packets

theorem advance_depends_only_on_the_selected_admitted_wire
    (first second : Due Party Good Port Technology Instrument)
    (revision : first.revision = second.revision)
    (paid : select tariff replies current first.packets = select tariff replies current second.packets) :
    advance tariff replies current first = advance tariff replies current second := by
  have same : paidOrRenew tariff replies current first.packets = paidOrRenew tariff replies current second.packets := by
    unfold paidOrRenew
    rw [paid]
  unfold advance
  rw [revision, same]

private theorem paidOrRenew_without_payment (packets : List Packet)
    (unpaid : (paidOrRenew tariff replies current packets).paidWire = none) :
    paidOrRenew tariff replies current packets = .renewed := by
  cases selected : select tariff replies current packets with
  | none => simp only [paidOrRenew, selected]
  | some hit =>
    obtain ⟨wire, signed⟩ := hit
    simp only [paidOrRenew, selected, Step.paidWire, Option.some_ne_none] at unpaid

theorem no_payment_preserves_the_exact_due_write
    (due : Due Party Good Port Technology Instrument)
    (unpaid : (advance tariff replies current due).paidWire = none) :
    advance tariff replies current due = advance tariff replies current {due with packets := []} := by
  have empty : paidOrRenew tariff replies current [] = .renewed := rfl
  cases revision : due.revision with
  | none =>
    simpa only [advance, revision, empty] using paidOrRenew_without_payment tariff replies current due.packets
      (by simpa only [advance, revision] using unpaid)
  | some offer =>
    cases outcome : inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer with
    | checked kit approved => simp only [advance, revision, outcome]
    | refused _ _ _ | unproductive _ _ =>
      simpa only [advance, revision, outcome, empty] using paidOrRenew_without_payment tariff replies current due.packets
        (by simpa only [advance, revision, outcome] using unpaid)

theorem any_effect_of_the_attack_lane_has_a_prior_full_payment
    (due : Due Party Good Port Technology Instrument)
    (different : advance tariff replies current due ≠ advance tariff replies current {due with packets := []}) :
    ∃ (wire : Packet) (signed : Admitted tariff replies current wire) (paid : PaidReview current (bill tariff wire)),
      advance tariff replies current due = .reviewed wire signed paid := by
  cases evidence : (advance tariff replies current due).paidWire with
  | none => exact (different (no_payment_preserves_the_exact_due_write tariff replies current due evidence)).elim
  | some wire =>
    obtain ⟨signed, paid, exact⟩ := (advance tariff replies current due).paidWire_has_its_actual_receipt evidence
    exact ⟨wire, signed, paid, exact⟩

theorem the_original_revision_keeps_its_due_slot
    (offer : ProductionOffer Party Good Port Technology Instrument)
    (kit : RevisionKit current.programme origin people cut.raw quantum offer)
    (approved : RevisionApproval replies.revision current.ledger.resident.erase current.physical.raw people offer)
    (selected : inspectRevision current.programme origin people cut.raw quantum replies.revision
      current.ledger.resident.erase current.physical.raw offer = .checked kit approved)
    (packets : List Packet) :
    advance tariff replies current ⟨some offer, packets⟩ = .revised offer kit approved := by
  simp only [advance, selected]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
