import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive.Frontier
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Metering

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive

open Abolition.Root Abolition.Root.Registered

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} origin}
  {exposure : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

private def exposureOnly (phase : Phase) : Bool := decide (phase = .exposure)

/-- The numerical branch runs over verified original clocks. An unread
meter stamp remains a typed failure of the original observation stream. -/
def readLongest (reading : Cohort.Reading origin meter exposure) (person : Party) :
    Sum (Missing reading.source (reading.reports.map ClockReading.observation)) ℚ :=
  match PersonTime.read reading.source (reading.reports.map ClockReading.observation) with
  | .missing issue => .inl issue
  | .complete _ => .inr (longest (checkedSpans reading.reports person exposureOnly))

theorem a_successful_run_read_has_the_original_consecutive_length
    (reading : Cohort.Reading origin meter exposure) (person : Party) (value : ℚ)
    (observed : readLongest reading person = .inr value) :
    value = originalLongest origin meter exposure person := by
  unfold readLongest at observed
  cases read : PersonTime.read reading.source (reading.reports.map ClockReading.observation) with
  | missing issue => rw [read] at observed; cases observed
  | complete covered =>
    rw [read] at observed
    have exactWidth : longest (checkedSpans reading.reports person exposureOnly) = value := Sum.inr.inj observed
    exact exactWidth.symm.trans (same_occupied_times_have_the_same_longest_run
      (Cohort.complete_reading_has_original_cover reading covered person exposureOnly))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Consecutive
