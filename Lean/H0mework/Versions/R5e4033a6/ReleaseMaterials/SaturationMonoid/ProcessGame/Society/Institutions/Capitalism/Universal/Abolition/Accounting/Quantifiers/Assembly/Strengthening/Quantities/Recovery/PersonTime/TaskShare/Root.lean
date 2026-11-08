import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Marginal
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Metering

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open Abolition.Root Abolition.Root.Registered Intervals
open SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} origin}
  {word exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

local notation "TaskAt" => Ordinal origin word

private def reportsFor (reading : Cohort.Reading origin meter word) (person : Party) (includes : Phase → Bool) :=
  reading.reports.filter fun entry =>
    decide (entry.observation.person = person) && includes entry.observation.phase

/-- Task charges keep the performer ordinal of the observed original
operation, even when several operations occupy the same person's clock. -/
def ofReading (reading : Cohort.Reading origin meter word) (person : Party) (includes : Phase → Bool) :
    Log TaskAt :=
  (reportsFor reading person includes).map fun read => (read.observation.performs, read.span)

theorem the_task_clock_is_the_original_personal_union
    (reading : Cohort.Reading origin meter word)
    (complete : CoversSource (reading.reports.map ClockReading.observation))
    (person : Party) (includes : Phase → Bool) :
    length (allSpans (ofReading reading person includes)) = hours (roster origin meter word) person includes := by
  have same : allSpans (ofReading reading person includes) = checkedSpans reading.reports person includes := by
    simp [allSpans, ofReading, reportsFor, checkedSpans, List.map_map, Function.comp_def]
  rw [same]
  exact length_eq_of_same_cover (Cohort.complete_reading_has_original_cover reading complete person includes)

theorem every_positive_task_charge_is_for_a_measured_original_action
    (reading : Cohort.Reading origin meter word) (person : Party) (includes : Phase → Bool)
    (allocation : TaskAt → Cell (ofReading reading person includes) → ℚ)
    (paid : Allocates (ofReading reading person includes) allocation)
    (task : TaskAt) (cell : Cell (ofReading reading person includes)) (charged : 0 < allocation task cell) :
    ownAction origin word task person ∧
      ∃ read ∈ reading.reports, read.observation.performs = task ∧ read.observation.person = person ∧
        includes read.observation.phase = true ∧ read.span.Contains cell.val := by
  have compatible : allows (ofReading reading person includes) task cell = true := by
    cases edge : allows (ofReading reading person includes) task cell
    · exact (charged.ne' ((paid.1.1 task cell).2 edge)).elim
    · rfl
  obtain ⟨span, listed, occupied⟩ := (present_iff _ _).mp compatible
  obtain ⟨entry, selected, rfl⟩ := List.mem_map.mp listed
  obtain ⟨inLog, taskKey⟩ := List.mem_filter.mp selected
  obtain ⟨read, measured, rfl⟩ := List.mem_map.mp inLog
  obtain ⟨original, actorPhase⟩ := List.mem_filter.mp measured
  simp only [decide_eq_true_eq] at taskKey
  simp only [Bool.and_eq_true, decide_eq_true_eq] at actorPhase
  have originalAction := read.observation.operation
  rw [taskKey, actorPhase.1] at originalAction
  exact ⟨originalAction, read, original, taskKey, actorPhase.1, actorPhase.2, occupied⟩

structure RecoveryCharges (reading : Cohort.Reading origin meter (exposure ++ repair))
    (person : Party) (includes : Phase → Bool) (charges : Ordinal origin (exposure ++ repair) → ℚ) where
  allocation : Ordinal origin (exposure ++ repair) → Cell (ofReading reading person includes) → ℚ
  exactCells : Allocates (ofReading reading person includes) allocation
  exactTasks : ∀ task, Network.rowTotal allocation task = charges task
  recovery : PaidRecovery origin exposure repair

/-- A simultaneous charge profile at an already restored occurrence is
funded precisely by the actual person's clock and the original task
cuts. The accepted allocation carries the same whole root successor. -/
theorem original_recovery_charges_are_exactly_its_measured_task_cuts
    (reading : Cohort.Reading origin meter (exposure ++ repair))
    (complete : CoversSource (reading.reports.map ClockReading.observation))
    (person : Party) (includes : Phase → Bool) (charges : Ordinal origin (exposure ++ repair) → ℚ)
    (recovery : PaidRecovery origin exposure repair) :
    let log := ofReading reading person includes
    Nonempty (RecoveryCharges reading person includes charges) ↔
      (∀ task, 0 ≤ charges task ∧ charges task ≤ full log task) ∧
      (∑ task, charges task) = hours (roster origin meter (exposure ++ repair)) person includes ∧
      ∀ group : Finset (Ordinal origin (exposure ++ repair)), (∑ task ∈ group, charges task) ≤
        (network log).supplyOf ((network log).neighbours group) := by
  have exactClock := the_task_clock_is_the_original_personal_union reading complete person includes
  dsimp only
  rw [← exactClock, ← fully_distributed_hours_iff_original_task_group_cuts]
  constructor
  · rintro ⟨settled⟩
    exact ⟨settled.allocation, settled.exactCells, settled.exactTasks⟩
  · rintro ⟨allocation, paid, rows⟩
    exact ⟨⟨allocation, paid, rows, recovery⟩⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
