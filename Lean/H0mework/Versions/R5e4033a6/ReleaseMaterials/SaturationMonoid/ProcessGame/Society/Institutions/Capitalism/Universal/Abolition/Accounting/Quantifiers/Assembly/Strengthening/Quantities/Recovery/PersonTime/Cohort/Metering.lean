import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Profile
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Reader.Compute

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort

open Abolition.Root Abolition.Root.Registered
open Intervals

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

structure Reading (origin : C) (meter : Meter.{u} origin) (word : Script) where
  source : SourceStream origin meter word
  reports : List (ClockReading origin meter word)

variable {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} origin}
  {exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

private def exposureOnly (phase : Phase) : Bool := decide (phase = .exposure)

private def recoveryDuty : Phase → Bool
  | .ordinary => false
  | .exposure | .recovery => true

theorem complete_reading_has_original_cover {word : Script}
    (reading : Reading origin meter word)
    (complete : CoversSource (reading.reports.map ClockReading.observation))
    (person : Party) (includes : Phase → Bool) :
    cover (checkedSpans reading.reports person includes) =
      cover (spansFor (roster origin meter word) person includes) := by
  ext time
  rw [checkedSpans_eq_original, cover_for_iff_original_person_occupation,
    roster_covers_exactly_the_source_occupations]
  constructor
  · rintro ⟨observation, _, owner, phase, occupied⟩
    exact ⟨observation, owner, phase, occupied⟩
  · rintro ⟨observation, owner, phase, occupied⟩
    obtain ⟨read, present, same⟩ := complete observation
    have kind : read.phase = observation.phase := congrArg Stamp.phase same
    exact ⟨read, present, (congrArg Stamp.person same).trans owner,
      kind.symm ▸ phase, (Observation.same_span_of_same_stamp same).symm ▸ occupied⟩

private def originalSpans (start : Reading origin meter exposure) (person : Party) : List Span :=
  checkedSpans start.reports person exposureOnly

private def counted (start : Reading origin meter exposure)
    (whole : Reading origin meter (exposure ++ repair)) (person : Party) : ℚ :=
  length (originalSpans start person ++ checkedSpans whole.reports person recoveryDuty)

private theorem counted_eq_original (start : Reading origin meter exposure)
    (whole : Reading origin meter (exposure ++ repair))
    (startComplete : CoversSource (start.reports.map ClockReading.observation))
    (wholeComplete : CoversSource (whole.reports.map ClockReading.observation))
    (person : Party) :
    counted (repair := repair) start whole person = hoursThroughRepair origin meter exposure repair person := by
  unfold counted originalSpans hoursThroughRepair phaseSpans
  apply length_eq_of_same_cover
  rw [cover_append, cover_append, complete_reading_has_original_cover start startComplete,
    complete_reading_has_original_cover whole wholeComplete]
  rfl

private def quantities (start : Reading origin meter exposure)
    (whole : Reading origin meter (exposure ++ repair)) : Address origin meter exposure → ℚ
  | .hours person => counted (repair := repair) start whole person
  | .ratio person _ => counted (repair := repair) start whole person / length (originalSpans start person)

private theorem quantities_eq_original (start : Reading origin meter exposure)
    (whole : Reading origin meter (exposure ++ repair))
    (startComplete : CoversSource (start.reports.map ClockReading.observation))
    (wholeComplete : CoversSource (whole.reports.map ClockReading.observation))
    (address : Address origin meter exposure) :
    quantities (repair := repair) start whole address = amount origin meter exposure repair address := by
  cases address with
  | hours person => exact counted_eq_original start whole startComplete wholeComplete person
  | ratio person positive =>
    have sameExposure : length (originalSpans start person) = originalExposure origin meter exposure person :=
      length_eq_of_same_cover (complete_reading_has_original_cover start startComplete person exposureOnly)
    change counted (repair := repair) start whole person / length (originalSpans start person) = _
    rw [counted_eq_original start whole startComplete wholeComplete, sameExposure]
    rfl

inductive ReadDecision (start : Reading origin meter exposure)
    (whole : Reading origin meter (exposure ++ repair))
  | ready (values : Address origin meter exposure → ℚ)
      (exactValues : ∀ address, values address = amount origin meter exposure repair address)
  | missingExposure (issue : Missing start.source (start.reports.map ClockReading.observation))
  | missingContinuation (issue : Missing whole.source (whole.reports.map ClockReading.observation))

/-- Validate the actual prefix and continuation once. One verified
clock profile then answers every person's hours and ratio queries. -/
def readTogether (start : Reading origin meter exposure) (whole : Reading origin meter (exposure ++ repair)) :
    ReadDecision (repair := repair) start whole :=
  match PersonTime.read start.source (start.reports.map ClockReading.observation) with
  | .missing issue => .missingExposure issue
  | .complete startComplete =>
    match PersonTime.read whole.source (whole.reports.map ClockReading.observation) with
    | .missing issue => .missingContinuation issue
    | .complete wholeComplete => .ready (quantities (repair := repair) start whole)
        (quantities_eq_original start whole startComplete wholeComplete)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort
