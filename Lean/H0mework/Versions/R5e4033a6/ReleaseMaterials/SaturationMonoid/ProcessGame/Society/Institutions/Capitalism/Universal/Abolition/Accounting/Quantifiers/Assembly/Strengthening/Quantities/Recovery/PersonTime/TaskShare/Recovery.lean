import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Prefix
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare.Root

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
  {exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

private def originalExposureOnly (phase : Phase) : Bool := decide (phase = .exposure)

private def burden : Phase → Bool
  | .ordinary => false
  | .exposure | .recovery => true

def recoveryLog (start : Cohort.Reading origin meter exposure)
    (full : Cohort.Reading origin meter (exposure ++ repair)) (person : Party) :
    Log (Ordinal origin (exposure ++ repair)) :=
  (ofReading start person originalExposureOnly).map (fun entry => (prefixTask (repair := repair) entry.1, entry.2)) ++
    ofReading full person burden

private theorem allSpans_ofReading {word : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
    (reading : Cohort.Reading origin meter word) (person : Party) (includes : Phase → Bool) :
    allSpans (ofReading reading person includes) = checkedSpans reading.reports person includes := by
  unfold allSpans ofReading checkedSpans
  simp only [List.map_map, Function.comp_def]
  rfl

private theorem log_entry_has_original_actor {word : List (Option (Compile.RawInput Party Good Port Technology Instrument))}
    (reading : Cohort.Reading origin meter word) (person : Party) (includes : Phase → Bool)
    (entry : Ordinal origin word × Span) (listed : entry ∈ ofReading reading person includes) :
    ownAction origin word entry.1 person := by
  obtain ⟨read, selected, rfl⟩ := List.mem_map.mp listed
  have actor := (List.mem_filter.mp selected).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at actor
  simpa only [actor.1] using read.observation.operation

theorem every_recovery_log_task_keeps_its_original_performer
    (start : Cohort.Reading origin meter exposure)
    (full : Cohort.Reading origin meter (exposure ++ repair)) (person : Party)
    (entry : Ordinal origin (exposure ++ repair) × Span)
    (listed : entry ∈ recoveryLog (repair := repair) start full person) :
    ownAction origin (exposure ++ repair) entry.1 person := by
  rcases List.mem_append.mp listed with earlier | continued
  · obtain ⟨old, original, rfl⟩ := List.mem_map.mp earlier
    exact (prefixTask_keeps_the_same_original_performer (repair := repair) old.1 person).mpr
      (log_entry_has_original_actor start person originalExposureOnly old original)
  · exact log_entry_has_original_actor full person burden entry continued

theorem recovery_log_has_the_original_paid_personal_clock
    (start : Cohort.Reading origin meter exposure)
    (full : Cohort.Reading origin meter (exposure ++ repair))
    (startComplete : CoversSource (start.reports.map ClockReading.observation))
    (fullComplete : CoversSource (full.reports.map ClockReading.observation)) (person : Party) :
    length (allSpans (recoveryLog (repair := repair) start full person)) =
      hoursThroughRepair origin meter exposure repair person := by
  have both : allSpans (recoveryLog (repair := repair) start full person) =
      checkedSpans start.reports person originalExposureOnly ++ checkedSpans full.reports person burden := by
    change allSpans ((ofReading start person originalExposureOnly).map
      (fun entry => (prefixTask (repair := repair) entry.1, entry.2)) ++ ofReading full person burden) = _
    have earlier : allSpans ((ofReading start person originalExposureOnly).map
        (fun entry => (prefixTask (repair := repair) entry.1, entry.2))) =
        allSpans (ofReading start person originalExposureOnly) := by
      simp only [allSpans, List.map_map, Function.comp_def]
    unfold allSpans at earlier ⊢
    rw [List.map_append, earlier]
    change allSpans (ofReading start person originalExposureOnly) ++ allSpans (ofReading full person burden) = _
    rw [allSpans_ofReading, allSpans_ofReading]
  unfold hoursThroughRepair phaseSpans
  rw [both]
  apply length_eq_of_same_cover
  rw [cover_append, cover_append, Cohort.complete_reading_has_original_cover start startComplete,
    Cohort.complete_reading_has_original_cover full fullComplete]
  rfl

theorem recovery_charge_profiles_use_one_original_clock_and_whole_successor
    (start : Cohort.Reading origin meter exposure)
    (full : Cohort.Reading origin meter (exposure ++ repair))
    (startComplete : CoversSource (start.reports.map ClockReading.observation))
    (fullComplete : CoversSource (full.reports.map ClockReading.observation))
    (person : Party) (charges : Ordinal origin (exposure ++ repair) → ℚ)
    (recovery : PaidRecovery origin exposure repair) :
    let log := recoveryLog (repair := repair) start full person
    (∃ allocation, Allocates log allocation ∧ (∀ task, Network.rowTotal allocation task = charges task) ∧
      PaidRecovery origin exposure repair) ↔
    (∀ task, 0 ≤ charges task ∧ charges task ≤ TaskShare.full log task) ∧
      (∑ task, charges task) = hoursThroughRepair origin meter exposure repair person ∧
      ∀ group : Finset (Ordinal origin (exposure ++ repair)),
        (∑ task ∈ group, charges task) ≤ (network log).supplyOf ((network log).neighbours group) := by
  dsimp only
  rw [← recovery_log_has_the_original_paid_personal_clock start full startComplete fullComplete,
    ← fully_distributed_hours_iff_original_task_group_cuts]
  constructor
  · rintro ⟨allocation, allocated, charges, _⟩
    exact ⟨allocation, allocated, charges⟩
  · rintro ⟨allocation, allocated, charges⟩
    exact ⟨allocation, allocated, charges, recovery⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
