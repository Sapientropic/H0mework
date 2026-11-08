import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Reader.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Abolition.Root Abolition.Root.Registered
open Intervals

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- The read clock values carry a proof that they are the original
opening and committing clocks. Only these rational values are used by
the executable interval calculation. -/
structure ClockReading (source : C) (meter : Meter.{u} source) (script : Script) where
  observation : Observation source meter script
  span : Span
  originalClock : span = observation.span

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} source}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

local notation "Reading" => ClockReading source meter script

def checkedSpans (reported : List Reading) (person : Party) (includes : Phase → Bool) : List Span :=
  (reported.filter fun read => decide (read.observation.person = person) &&
    includes read.observation.phase).map ClockReading.span

theorem checkedSpans_eq_original (reported : List Reading) (person : Party) (includes : Phase → Bool) :
    checkedSpans reported person includes =
      spansFor (reported.map ClockReading.observation) person includes := by
  induction reported with
  | nil => rfl
  | cons read later ih =>
    have clock := read.originalClock
    by_cases present : (decide (read.observation.person = person) && includes read.observation.phase) = true
    · simp only [checkedSpans, spansFor, List.map_cons, List.filter_cons, present, if_true]
      change read.span :: checkedSpans later person includes =
        read.observation.span :: spansFor (later.map ClockReading.observation) person includes
      rw [clock, ih]
    · simp only [checkedSpans, spansFor, List.map_cons, List.filter_cons, present]
      exact ih

/-- A missing original reading has its own output branch. The numeric
branch executes only after the source stream has been covered. -/
def readHours (stream : SourceStream source meter script) (reported : List Reading)
    (person : Party) (includes : Phase → Bool) :
    Sum (Missing stream (reported.map ClockReading.observation)) ℚ :=
  match read stream (reported.map ClockReading.observation) with
  | .missing issue => .inl issue
  | .complete _ => .inr (length (checkedSpans reported person includes))

theorem a_successful_read_has_the_exact_original_person_hours
    (stream : SourceStream source meter script) (reported : List Reading)
    (person : Party) (includes : Phase → Bool) (value : ℚ)
    (observed : readHours stream reported person includes = .inr value) :
    value = hours (roster source meter script) person includes := by
  unfold readHours at observed
  cases checked : read stream (reported.map ClockReading.observation) with
  | missing issue => rw [checked] at observed; cases observed
  | complete covered =>
    rw [checked] at observed
    have computed : length (checkedSpans reported person includes) = value := Sum.inr.inj observed
    rw [checkedSpans_eq_original] at computed
    exact computed.symm.trans (complete_reports_give_exactly_the_original_person_hours _ covered _ _)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
