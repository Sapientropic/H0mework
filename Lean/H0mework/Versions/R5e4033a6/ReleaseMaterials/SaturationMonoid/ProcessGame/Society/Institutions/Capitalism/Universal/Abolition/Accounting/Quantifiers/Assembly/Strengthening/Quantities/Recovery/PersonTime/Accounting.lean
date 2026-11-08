import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Observation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.WorkHours

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Source.Program Abolition.Root Abolition.Root.Registered
open Intervals

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} source}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

def phaseSpans (observed : List (Observation source meter script)) (person : Party) (phase : Phase) :
    List Span :=
  spansFor observed person (fun kind => decide (kind = phase))

def phaseHours (observed : List (Observation source meter script)) (person : Party) (phase : Phase) :
    ℚ :=
  length (phaseSpans observed person phase)

def exposureAndRecovery (observed : List (Observation source meter script)) (person : Party) : ℚ :=
  length (phaseSpans observed person .exposure ++ phaseSpans observed person .recovery)

def overlappingHours (observed : List (Observation source meter script)) (person : Party) : ℚ :=
  length (overlaps (phaseSpans observed person .exposure) (phaseSpans observed person .recovery))

theorem original_persons_work_and_recovery_conserve_the_exact_overlap
    (observed : List (Observation source meter script)) (person : Party) :
    exposureAndRecovery observed person + overlappingHours observed person =
      phaseHours observed person .exposure + phaseHours observed person .recovery :=
  length_union_add_overlap _ _

def conversion (observed : List (Observation source meter script)) (person : Party) : Option ℚ :=
  let exposure := phaseHours observed person .exposure
  if 0 < exposure then some (exposureAndRecovery observed person / exposure) else none

theorem a_positive_exposure_counts_only_nonoverlapping_extra_recovery
    (observed : List (Observation source meter script)) (person : Party)
    (positive : 0 < phaseHours observed person .exposure) :
    conversion observed person = some
      (1 + (phaseHours observed person .recovery - overlappingHours observed person) /
        phaseHours observed person .exposure) := by
  let exposure := phaseHours observed person .exposure
  let recovery := phaseHours observed person .recovery
  let shared := overlappingHours observed person
  have balance : exposureAndRecovery observed person + shared = exposure + recovery :=
    original_persons_work_and_recovery_conserve_the_exact_overlap observed person
  have numerator : exposureAndRecovery observed person = exposure + (recovery - shared) := by
    linarith only [balance]
  unfold conversion
  rw [if_pos positive, numerator, add_div, div_self positive.ne']

theorem zero_actual_exposure_has_no_conversion
    (observed : List (Observation source meter script)) (person : Party)
    (zero : phaseHours observed person .exposure = 0) :
    conversion observed person = none := by
  simp [conversion, zero]

theorem duplicated_observations_do_not_multiply_person_hours
    (observed : List (Observation source meter script)) (person : Party) (phase : Phase) :
    phaseHours (observed ++ observed) person phase = phaseHours observed person phase := by
  unfold phaseHours phaseSpans spansFor
  rw [List.filter_append, List.map_append, duplicate_occupations_leave_the_same_length]

structure RecoveredAt (source : C) (meter : Meter.{u} source) (exposure repair : Script)
    (observed : List (Observation source meter (exposure ++ repair))) (person : Party) : Prop where
  measured : 0 < phaseHours observed person .exposure
  settled : Settled (Execution.endAt source exposure) repair
  restored : Restored source exposure repair
  whole : Recorded source (exposure ++ repair)

inductive Disposition (source : C) (meter : Meter.{u} source) (exposure repair : Script)
    (observed : List (Observation source meter (exposure ++ repair))) (person : Party)
  | paid (recovered : RecoveredAt source meter exposure repair observed person)
  | noExposure (missing : phaseHours observed person .exposure = 0)
      (original : Recorded source (exposure ++ repair))
  | accounting (issue : Obstruction (Execution.endAt source exposure) repair)
      (original : Recorded source (exposure ++ repair))
  | residual (loss : Loss source exposure repair)
      (original : Recorded source (exposure ++ repair))

/-- The measured person and the physical repair enter one original
disposition. Failed recovery retains the original material address. -/
def resolve (source : C) (meter : Meter.{u} source) (exposure repair : Script)
    (observed : List (Observation source meter (exposure ++ repair))) (person : Party) :
    Disposition source meter exposure repair observed person :=
  let whole := record source (exposure ++ repair)
  if positive : 0 < phaseHours observed person .exposure then
    match decideAt (Execution.endAt source exposure) repair with
    | .blocked issue => .accounting issue whole
    | .feasible paid =>
      match found : Recovery.inspect source exposure repair with
      | some loss => .residual loss whole
      | none => .paid ⟨positive, settle _ _ paid,
          (cleared_exactly_when_no_original_actor_loses_stock source exposure repair).mp found, whole⟩
  else .noExposure (le_antisymm (le_of_not_gt positive) (length_nonnegative _)) whole

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
