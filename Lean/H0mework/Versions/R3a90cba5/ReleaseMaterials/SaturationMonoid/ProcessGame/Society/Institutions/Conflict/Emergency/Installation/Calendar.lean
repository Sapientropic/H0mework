import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.ClockCell

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
open PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument

/-- A clock cell is closed at its first possible expiry and open at
the first physical instant at which it would change a submission. -/
structure Band where
  lower : ℚ
  upper : Option ℚ

namespace Band

def interval (band : Band) : Interval := ⟨some band.lower, band.upper⟩

abbrev Holds (band : Band) (deadline : ℚ) : Prop := band.interval.Holds deadline

instance (band : Band) (deadline : ℚ) : Decidable (band.Holds deadline) :=
  match upper : band.upper with
  | none => decidable_of_iff (band.lower ≤ deadline) ⟨
      fun lower => ⟨fun _ same => (Option.some.inj same) ▸ lower,
        fun _ impossible => by rw [show band.interval.upper = none from upper] at impossible; cases impossible⟩,
      fun fit => fit.1 _ rfl⟩
  | some stop => decidable_of_iff (band.lower ≤ deadline ∧ deadline < stop) ⟨
      fun ⟨lower, before⟩ => ⟨fun _ same => (Option.some.inj same) ▸ lower,
        fun _ named => (Option.some.inj (upper.symm.trans named)) ▸ before⟩,
      fun fit => ⟨fit.1 _ rfl, fit.2 _ upper⟩⟩

def below (band : Band) (clock : ℚ) : Band :=
  ⟨band.lower, (band.interval.insert (.below clock)).upper⟩

def atLeast (band : Band) (clock : ℚ) : Band :=
  ⟨max band.lower clock, band.upper⟩

theorem below_iff (band : Band) (clock deadline : ℚ) :
    (band.below clock).Holds deadline ↔ band.Holds deadline ∧ deadline < clock :=
  Interval.insert_holds_iff band.interval (.below clock) deadline

theorem at_least_iff (band : Band) (clock deadline : ℚ) :
    (band.atLeast clock).Holds deadline ↔ band.Holds deadline ∧ clock ≤ deadline :=
  by
    change (band.atLeast clock).interval.Holds deadline ↔ band.interval.Holds deadline ∧ clock ≤ deadline
    simpa only [Band.atLeast, Band.interval, Interval.insert, Option.elim, max_comm, Guard.Holds] using
      (Interval.insert_holds_iff band.interval (.atLeast clock) deadline)

theorem lower_le {band : Band} {deadline : ℚ} (fit : band.Holds deadline) :
    band.lower ≤ deadline := fit.1 _ rfl

theorem lower_fits {band : Band} {deadline : ℚ} (fit : band.Holds deadline) :
    band.Holds band.lower :=
  ⟨fun _ same => (Option.some.inj same).symm.le,
    fun upper found => (lower_le fit).trans_lt (fit.2 upper found)⟩

end Band

/-- The item and its posted amounts are the outputs of the original
interpreter at that literal position. -/
structure Posting (Party Good Port Technology Instrument : Type) where
  item : ExecutionItem Party Good Port (State Party Technology) Instrument
  accepted : Bool
  debit : Bundle (Party × Good)
  credit : Bundle (Party × Good)

structure Period (Party Good Port Technology Instrument : Type) where
  before : RawCurrent Party Good (State Party Technology) Instrument
  after : RawCurrent Party Good (State Party Technology) Instrument
  word : RawEvent Party Good Port (State Party Technology) Instrument
  postings : List (Posting Party Good Port Technology Instrument)

local notation "Day" => Period Party Good Port Technology Instrument

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port))

def period (deadline : ℚ) (current : Raw) (word : Word) : Day :=
  let active := law base (withCutoff scope deadline)
  ⟨current, active.next current word, word,
    (active.rawItems current word).map fun item =>
      ⟨item, decide (active.Valid item.before item.request),
        active.actualDebit item.before item.request, active.actualCredit item.before item.request⟩⟩

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem every_item_reads_period_clock
    (active : RawLaw Party Good Port (State Party Technology) Instrument)
    (current : Raw) (index : Nat) (word : Word) (item : Item)
    (listed : item ∈ (active.execute current index word).items) :
    item.before.clock = current.clock := by
  induction word generalizing current index with
  | nil => cases listed
  | cons head rest ih =>
    simp only [RawLaw.execute, List.mem_cons] at listed
    rcases listed with rfl | tail
    · rfl
    · have next : (active.step current head).clock = current.clock := by
        unfold RawLaw.step
        split <;> rfl
      exact (ih _ _ tail).trans next

theorem period_same_cell (current : Raw) (word : Word) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    period base scope a current word = period base scope b current word := by
  let left := law base (withCutoff scope a)
  let right := law base (withCutoff scope b)
  have items : left.rawItems current word = right.rawItems current word :=
    congrArg ExecutionResult.items (execute_same_cell base scope current 0 word same)
  have equalMap :
      (left.rawItems current word).map (fun item =>
        (⟨item, decide (left.Valid item.before item.request), left.actualDebit item.before item.request,
          left.actualCredit item.before item.request⟩ : Posting Party Good Port Technology Instrument)) =
      (right.rawItems current word).map (fun item =>
        ⟨item, decide (right.Valid item.before item.request), right.actualDebit item.before item.request,
          right.actualCredit item.before item.request⟩) := by
    rw [← items]
    apply List.map_congr_left
    intro item listed
    have clock := every_item_reads_period_clock left current 0 word item listed
    have side : item.before.clock ≤ a ↔ item.before.clock ≤ b := clock.symm ▸ same
    have agrees : left.Valid item.before item.request ↔ right.Valid item.before item.request :=
      valid_iff_same_cell base scope item.before item.request side
    have admitted : decide (left.Valid item.before item.request) = decide (right.Valid item.before item.request) := by
      by_cases good : left.Valid item.before item.request
      · simp [good, agrees.mp good]
      · have denied : ¬ right.Valid item.before item.request := fun h => good (agrees.mpr h)
        simp [good, denied]
    rw [admitted, actual_debit_same_cell base scope item.before item.request side,
      actual_credit_same_cell base scope item.before item.request side]
  exact congrArg₂ (fun next postings => (⟨current, next, word, postings⟩ : Day))
    (next_same_cell base scope current word same) equalMap

def replay (deadline : ℚ) (current : Raw) : List Word → List Day × Raw
  | [] => ([], current)
  | word :: rest =>
    let today := period base scope deadline current word
    let later := replay deadline today.after rest
    (today :: later.1, later.2)

structure Cell (Party Good Port Technology Instrument : Type) where
  band : Band
  history : List (Period Party Good Port Technology Instrument)
  target : RawCurrent Party Good (State Party Technology) Instrument

local notation "Slice" => Cell Party Good Port Technology Instrument

private def prepend (today : Day) (cell : Slice) : Slice :=
  {cell with history := today :: cell.history}

/-- Search the two exact branches at each native physical clock.
Inconsistent branches are dropped at their least point. The search has
no supplied time grid or bound on the number of epochs. -/
def cells (band : Band) (current : Raw) : List Word → List Slice
  | [] => if band.Holds band.lower then [⟨band, [], current⟩] else []
  | word :: rest =>
    if band.Holds band.lower then
      let early := band.below current.clock
      let late := band.atLeast current.clock
      let stopped := period base scope early.lower current word
      let active := period base scope late.lower current word
      (cells early stopped.after rest).map (prepend stopped) ++
        (cells late active.after rest).map (prepend active)
    else []

theorem cell_replays_at_every_deadline (band : Band) (current : Raw) (words : List Word)
    (cell : Slice) (listed : cell ∈ cells base scope band current words) :
    cell.band.Holds cell.band.lower ∧
      ∀ deadline, cell.band.Holds deadline →
        band.Holds deadline ∧ replay base scope deadline current words = (cell.history, cell.target) := by
  induction words generalizing band current cell with
  | nil =>
    by_cases possible : band.Holds band.lower
    · simp only [cells, if_pos possible, List.mem_singleton] at listed
      subst cell
      exact ⟨possible, fun _ fits => ⟨fits, rfl⟩⟩
    · simp [cells, possible] at listed
  | cons word rest ih =>
    by_cases possible : band.Holds band.lower
    · simp only [cells, if_pos possible, List.mem_append, List.mem_map] at listed
      rcases listed with ⟨prior, included, rfl⟩ | ⟨prior, included, rfl⟩
      · let early := band.below current.clock
        let stopped := period base scope early.lower current word
        have later := ih early stopped.after prior included
        refine ⟨later.1, fun deadline fits => ?_⟩
        obtain ⟨side, replayed⟩ := later.2 deadline fits
        have earliestSide := (Band.below_iff band current.clock early.lower).mp (Band.lower_fits side)
        have exactSide := (Band.below_iff band current.clock deadline).mp side
        have same : current.clock ≤ deadline ↔ current.clock ≤ early.lower := by
          simp [not_le.mpr exactSide.2, not_le.mpr earliestSide.2]
        have day := period_same_cell base scope current word same
        refine ⟨exactSide.1, ?_⟩
        rw [replay, day]
        change (stopped :: (replay base scope deadline stopped.after rest).1,
          (replay base scope deadline stopped.after rest).2) = (stopped :: prior.history, prior.target)
        rw [replayed]
      · let late := band.atLeast current.clock
        let active := period base scope late.lower current word
        have later := ih late active.after prior included
        refine ⟨later.1, fun deadline fits => ?_⟩
        obtain ⟨side, replayed⟩ := later.2 deadline fits
        have exactSide := (Band.at_least_iff band current.clock deadline).mp side
        have same : current.clock ≤ deadline ↔ current.clock ≤ late.lower := by
          exact iff_of_true exactSide.2 (le_max_right _ _)
        have day := period_same_cell base scope current word same
        refine ⟨exactSide.1, ?_⟩
        rw [replay, day]
        change (active :: (replay base scope deadline active.after rest).1,
          (replay base scope deadline active.after rest).2) = (active :: prior.history, prior.target)
        rw [replayed]
    · simp [cells, possible] at listed

theorem cells_cover_all_deadlines (band : Band) (current : Raw) (words : List Word)
    (deadline : ℚ) (fits : band.Holds deadline) :
    ∃ cell ∈ cells base scope band current words, cell.band.Holds deadline := by
  induction words generalizing band current with
  | nil =>
    exact ⟨⟨band, [], current⟩, by simp [cells, Band.lower_fits fits], fits⟩
  | cons word rest ih =>
    have low := Band.lower_fits fits
    rw [cells, if_pos low]
    by_cases expires : deadline < current.clock
    · let early := band.below current.clock
      let stopped := period base scope early.lower current word
      obtain ⟨cell, included, exactFit⟩ := ih early stopped.after
        ((Band.below_iff band current.clock deadline).mpr ⟨fits, expires⟩)
      exact ⟨prepend stopped cell, List.mem_append_left _ (List.mem_map_of_mem included), exactFit⟩
    · let late := band.atLeast current.clock
      let active := period base scope late.lower current word
      obtain ⟨cell, included, exactFit⟩ := ih late active.after
        ((Band.at_least_iff band current.clock deadline).mpr ⟨fits, le_of_not_gt expires⟩)
      exact ⟨prepend active cell, List.mem_append_right _ (List.mem_map_of_mem included), exactFit⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
