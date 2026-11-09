import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Cost
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Productivity
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Production

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Input" => ProgrammeSource.Input Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Native" => Runtime.Native Party Good Port Technology Instrument

structure ReviewBid (Party Good Port Technology Instrument : Type) where
  payer : Party
  attempted : RawEvent Party Good Port Technology Instrument
  port : Port
  parts : ChargeParts Good

abbrev ReviewBid.expenses (bid : ReviewBid Party Good Port Technology Instrument) : Bundle Good :=
  bid.parts.bundle

inductive Proposal (Party Good Port Technology Instrument : Type)
  | renew
  | review (bid : ReviewBid Party Good Port Technology Instrument)
  | revise (offer : ProductionOffer Party Good Port Technology Instrument)

inductive Disposition
  | renewed
  | presentation
  | reviewed
  | revised
  | revisionRefused
  deriving DecidableEq

variable {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

/-- Physical state is read from the installed visit. The native ledger
anchor remains the original cut at which the old debts were cleared. -/
structure Current (origin : Raw) (people : List Party) (quantum : ℚ) where
  ledger : StateAt seed community cut
  physical : Native
  programme : Input
  recipe : Recipe programme origin people cut.raw quantum
  reserved : InReserve cut.raw physical.raw

variable (current : Current (seed := seed) (cut := cut) (community := community) origin people quantum)

abbrev Current.move := current.recipe.moveAt current.physical.raw current.reserved

structure Readout (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  submitted : Proposal Party Good Port Technology Instrument
  disposition : Disposition
  programme : ProgrammeSource.Input Party Good Port Technology Instrument
  before : Runtime.Native Party Good Port Technology Instrument
  commands : RawEvent Party Good Port Technology Instrument

def Readout.effect (read : Readout Party Good Port Technology Instrument) :=
  Physical.Public.compile read.programme read.before (.execute read.commands)

structure Round where
  visit : Installation.Core.Landed seed community cut (Readout Party Good Port Technology Instrument)
  next : Current (seed := seed) (cut := cut) (community := community) origin people quantum
  before : visit.read.before = current.physical
  realWrite : visit.read.effect.isAccepted = true
  physicalNext : visit.read.effect.next = next.physical
  programmeNext : visit.read.programme = next.programme
  wholeNext : (⟨current.ledger.world,
    (Installation.Core.action current.ledger visit.read true).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = next.ledger.resident.erase
  rows : next.ledger.stack.balances = current.ledger.stack.balances
  noDamage : ∀ item ∈ visit.read.effect.execution.items, ∀ key,
    Reparation.loss visit.read.programme.law community item key = 0
  ownDebit : ∀ item ∈ visit.read.effect.execution.items, ∀ lot ∈
    visit.read.programme.law.actualDebit item.before item.request, lot.1.1 = item.request.signer
  needs : OriginalNeedFloor visit.read.programme origin current.physical.raw people visit.read.commands ∧
    OriginalNeedFloor visit.read.programme current.physical.raw current.physical.raw people visit.read.commands
  exit : ∀ person ∈ people, ∃ word, Supply.Registered visit.read.programme current.physical.raw word ∧
    Supply.Period visit.read.programme origin current.physical.raw [person] word
  clock : current.physical.raw.clock + quantum ≤ next.physical.raw.clock
  growth : ∃ person good, current.physical.raw.stock person good < next.physical.raw.stock person good

local notation "Command" => Proposal Party Good Port Technology Instrument

private def publishRound (submitted : Command) (disposition : Disposition)
    (programme : Input) (recipe : Recipe programme origin people cut.raw quantum) (commands : Word)
    (accepted : (Physical.Public.compile programme current.physical (.execute commands)).isAccepted = true)
    (reserve : InReserve cut.raw (Physical.Public.compile programme current.physical (.execute commands)).next.raw)
    (safe : ∀ item ∈ (Physical.Public.compile programme current.physical (.execute commands)).execution.items,
      ∀ key, Reparation.loss programme.law community item key = 0)
    (own : ∀ item ∈ (Physical.Public.compile programme current.physical (.execute commands)).execution.items,
      ∀ lot ∈ programme.law.actualDebit item.before item.request, lot.1.1 = item.request.signer)
    (needs : OriginalNeedFloor programme origin current.physical.raw people commands ∧
      OriginalNeedFloor programme current.physical.raw current.physical.raw people commands)
    (exits : ∀ person ∈ people, ∃ word, Supply.Registered programme current.physical.raw word ∧
      Supply.Period programme origin current.physical.raw [person] word)
    (clock : current.physical.raw.clock + quantum ≤
      (Physical.Public.compile programme current.physical (.execute commands)).next.raw.clock)
    (growth : ∃ person good, current.physical.raw.stock person good <
      (Physical.Public.compile programme current.physical (.execute commands)).next.raw.stock person good) :
    Round current := by
  let read : Readout Party Good Port Technology Instrument := ⟨submitted, disposition, programme, current.physical, commands⟩
  let write := Installation.Core.publish current.ledger read true
  have exactRead : write.read = read := Installation.Core.publish_reads_the_exact_payload _ _ _
  refine ⟨write, ⟨write.state, read.effect.next, programme, recipe, reserve⟩,
    ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, clock, growth⟩
  · rw [exactRead]
  · rw [exactRead]
    exact accepted
  · rw [exactRead]
  · rw [exactRead]
  · rw [exactRead]
    exact Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _
  · intro item listed key
    rw [exactRead] at listed
    exact safe item listed key
  · intro item listed lot debit
    rw [exactRead] at listed debit
    exact own item listed lot debit
  · simpa only [exactRead] using needs
  · simpa only [exactRead] using exits

/-- The selected recipe pays this very round. An approved replacement
uses its own trial as this write, before the replacement enters the next cut. -/
def productiveRound (submitted : Command) (disposition : Disposition)
    (programme : Input) (recipe : Recipe programme origin people cut.raw quantum) :
    Round current := by
  let move := recipe.moveAt current.physical.raw current.reserved
  have actual := move.paid.native_write current.physical
  refine publishRound current submitted disposition programme recipe move.word actual.1 ?_ ?_ ?_
    ⟨move.paid.originalFloor, move.paid.currentFloor⟩ move.personal ?_ ?_
  · rw [actual.2.2]
    exact recipe.next_reserved current.physical.raw current.reserved
  · rw [actual.2.1]
    intro item listed key
    exact (move.paid.own item listed).opens_no_coercive_loss community key
  · rw [actual.2.1]
    intro item listed lot debited
    exact (move.paid.own item listed).actual_debit_is_own lot debited
  · rw [actual.2.2]
    exact recipe.next_clock current.physical.raw current.reserved
  · rw [actual.2.2]
    obtain ⟨person, good, positive⟩ := recipe.positiveGain
    refine ⟨person, good, ?_⟩
    change current.physical.raw.stock person good < move.next.stock person good
    rw [recipe.next_material current.physical.raw current.reserved person good]
    exact lt_add_of_pos_right _ positive

def ReviewBid.fee (bid : ReviewBid Party Good Port Technology Instrument) (person : Party) (good : Good) : ℚ :=
  if person = bid.payer then amount Good bid.expenses good else 0

variable (bid : ReviewBid Party Good Port Technology Instrument)

def ReviewLegal : Prop :=
  current.programme.law.Valid
    (reviewItem current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses).before
    (reviewRequest bid.payer bid.port bid.expenses)

theorem review_is_the_exact_physical_charge (legal : ReviewLegal current bid) :
    afterCharge current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses =
      chargeReview current.move.next bid.fee :=
  afterCharge_is_posted_deduction legal

def paidReviewRound (legal : ReviewLegal current bid) (fits : ReviewFits current.recipe bid.fee)
    (surplus : ∃ person good, bid.fee person good < current.recipe.gain person good) : Round current := by
  have actual := charged_native_write current.physical current.move.paid legal
  have exactRaw := review_is_the_exact_physical_charge current bid legal
  refine publishRound current (.review bid) .reviewed current.programme current.recipe
    (chargedWord current.move.word bid.payer bid.port bid.expenses) actual.1 ?_ ?_ ?_
    (charged_needs_are_exact current.move.paid) current.move.personal ?_ ?_
  · rw [actual.2.2]
    change InReserve cut.raw (afterCharge _ _ _ _ _ _)
    rw [exactRaw]
    exact current.recipe.review_reserved current.physical.raw current.reserved bid.fee fits
  · rw [actual.2.1]
    exact charged_items_have_no_damage community current.move.paid legal
  · rw [actual.2.1, ← RawLaw.rawItems, charged_items]
    intro item listed lot debited
    rcases List.mem_append.mp listed with productive | charged
    · exact (current.move.paid.own item productive).actual_debit_is_own lot debited
    · rcases List.mem_singleton.mp charged with rfl
      rw [(charged_actual_debit legal).1] at debited
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp debited
      rfl
  · rw [actual.2.2]
    change _ ≤ (afterCharge _ _ _ _ _ _).clock
    rw [exactRaw]
    exact current.recipe.next_clock current.physical.raw current.reserved
  · rw [actual.2.2]
    change ∃ p g, _ < (afterCharge _ _ _ _ _ _).stock p g
    rw [exactRaw]
    exact (current.recipe.review_progress current.physical.raw current.reserved bid.fee).mpr surplus

theorem productiveRound_reads_selected_production (submitted : Command) (disposition : Disposition)
    (programme : Input) (recipe : Recipe programme origin people cut.raw quantum) :
    let round := productiveRound current submitted disposition programme recipe
    round.visit.read.disposition = disposition ∧
    round.next.physical.raw = (recipe.moveAt current.physical.raw current.reserved).next ∧
    round.next.programme = programme ∧
    round.visit.read.commands = (recipe.moveAt current.physical.raw current.reserved).word := by
  let move := recipe.moveAt current.physical.raw current.reserved
  have paid := move.paid.native_write current.physical
  exact ⟨rfl, congrArg (fun next : Native => next.raw) paid.2.2, rfl, rfl⟩

theorem paidReviewRound_reads_the_payers_whole_cost
    (legal : ReviewLegal current bid) (fits : ReviewFits current.recipe bid.fee)
    (surplus : ∃ person good, bid.fee person good < current.recipe.gain person good) :
    let round := paidReviewRound current bid legal fits surplus
    let after := round.next.physical.raw
    let peaceful := current.move.next
    round.visit.read.disposition = .reviewed ∧ round.next.programme = current.programme ∧
    after.claims = peaceful.claims ∧ after.technology = peaceful.technology ∧
    after.clock = peaceful.clock ∧ after.round = peaceful.round ∧
    ∀ person good, after.stock person good - peaceful.stock person good = -(bid.fee person good) := by
  have paid := charged_native_write current.physical current.move.paid legal
  have actual : (paidReviewRound current bid legal fits surplus).next.physical.raw =
      afterCharge current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses :=
    congrArg (fun next : Native => next.raw) paid.2.2
  dsimp only
  rw [actual, review_is_the_exact_physical_charge current bid legal]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun person good => ?_⟩
  change current.move.next.stock person good + -(bid.fee person good) - current.move.next.stock person good =
    -(bid.fee person good)
  ring

theorem paidReviewRound_charges_the_actual_last_item
    (legal : ReviewLegal current bid) (fits : ReviewFits current.recipe bid.fee)
    (surplus : ∃ person good, bid.fee person good < current.recipe.gain person good) :
    let round := paidReviewRound current bid legal fits surplus
    round.visit.read.effect.execution.items[current.move.word.length]? =
      some (reviewItem current.programme current.physical.raw current.move.word bid.payer bid.port bid.expenses) := by
  have written := charged_native_write current.physical current.move.paid legal
  have width : (current.programme.law.rawItems current.physical.raw current.move.word).length = current.move.word.length :=
    current.programme.law.inventory_length current.physical.raw 0 current.move.word
  change (Physical.Public.compile current.programme current.physical
    (.execute (chargedWord current.move.word bid.payer bid.port bid.expenses))).execution.items[
      current.move.word.length]? = _
  rw [written.2.1, ← RawLaw.rawItems, charged_items, List.getElem?_append_right width.le,
    width, Nat.sub_self]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
