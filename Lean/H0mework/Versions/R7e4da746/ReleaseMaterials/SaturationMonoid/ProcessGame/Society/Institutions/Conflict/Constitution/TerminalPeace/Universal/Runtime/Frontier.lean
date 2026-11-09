import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Exit
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (prior : StateAt seed community cut)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (menus : Menus Party Good Port Technology Instrument)

local notation "Clock" => clockAt prior input origin roster menus
local notation "Event" => eventAt prior input origin roster menus
local notation "Paid" => Succeeds prior input origin roster menus
local notation "Failed" => Refused prior input origin roster menus
local notation "Ready" => ReadyAt prior input origin roster menus
local notation "Fault" => FaultAt prior input origin roster menus

def durationAt (n : Nat) : ℚ :=
  match (Event n).selected with
  | .paid _ _ _ => input.law.duration (Event n).before.raw
  | .blocked _ => 0

theorem next_clock_is_the_selected_source_duration (n : Nat) :
    Clock (n + 1) = Clock n + durationAt prior input origin roster menus n := by
  change ((Event n).after).raw.clock = (Event n).before.raw.clock + _
  unfold durationAt
  cases choice : (Event n).selected with
  | paid position paid earlier =>
    have after := (paid.native_write (Event n).before).2.2
    unfold Attempt.after
    simp only [choice]
    rw [after]
    change (input.law.next (Event n).before.raw (Event n).offers[position]).clock = _
    exact paid.exact_clock
  | blocked failure =>
    unfold Attempt.after
    rw [choice, add_zero]

def totalDuration : Nat → ℚ
  | 0 => 0
  | n + 1 => totalDuration n + durationAt prior input origin roster menus n

theorem clock_is_the_exact_sum_of_actual_durations (n : Nat) :
    Clock n = cut.raw.clock + totalDuration prior input origin roster menus n := by
  induction n with
  | zero =>
    change cut.raw.clock = cut.raw.clock + 0
    exact (add_zero _).symm
  | succ n previous =>
    rw [next_clock_is_the_selected_source_duration, previous, totalDuration, add_assoc]

def ClockCofinal : Prop := ∀ start bound, ∃ visit ≥ start, bound < Clock visit

theorem clock_cofinal_iff_paid_duration_is_unbounded :
    ClockCofinal prior input origin roster menus ↔
      ∀ bound, ∃ n, bound < totalDuration prior input origin roster menus n := by
  constructor
  · intro cofinal bound
    obtain ⟨n, _, passed⟩ := cofinal 0 (cut.raw.clock + bound)
    rw [clock_is_the_exact_sum_of_actual_durations] at passed
    exact ⟨n, lt_of_add_lt_add_left passed⟩
  · intro unbounded start bound
    obtain ⟨n, passed⟩ := unbounded (bound - cut.raw.clock)
    refine ⟨max start n, Nat.le_max_left _ _, ?_⟩
    have advanced : bound < Clock n := by
      rw [clock_is_the_exact_sum_of_actual_durations]
      linarith only [passed]
    exact advanced.trans_le (clock_mono prior input origin roster menus (Nat.le_max_right _ _))

/-- The classifier reads a realized run. The runtime still selects each
word from that cut's current inventory and its finite submitted menu. -/
inductive Outcome where
  | firstRefusal (visit : Nat) (failure : Fault visit) (earlier : ∀ n < visit, Ready n)
  | bounded (ready : ∀ n, Ready n) (bound : ℚ) (notBeyond : ∀ n, Clock n ≤ bound)
  | live (ready : ∀ n, Ready n) (time : ClockCofinal prior input origin roster menus)

def classify : Outcome prior input origin roster menus := by
  classical
  by_cases bad : ∃ n, Fault n
  · refine .firstRefusal (Nat.find bad) (Nat.find_spec bad) ?_
    intro n earlier
    exact (ready_or_exact_fault prior input origin roster menus n).resolve_right (Nat.find_min bad earlier)
  · have paid (n : Nat) : Ready n :=
      (ready_or_exact_fault prior input origin roster menus n).resolve_right (fun refused => bad ⟨n, refused⟩)
    by_cases later : ∀ bound, ∃ n, bound < Clock n
    · refine .live paid fun start bound => ?_
      obtain ⟨n, beyond⟩ := later bound
      exact ⟨max start n, Nat.le_max_left _ _,
        beyond.trans_le (clock_mono prior input origin roster menus (Nat.le_max_right _ _))⟩
    · have bound : ∃ bound : ℚ, ∀ n, Clock n ≤ bound := by
        by_contra noBound
        apply later
        intro bound
        by_contra h
        exact noBound ⟨bound, fun n => le_of_not_gt fun passes => h ⟨n, passes⟩⟩
      exact .bounded paid (Classical.choose bound) (Classical.choose_spec bound)

theorem a_living_terminal_is_generated_exactly_on_a_paid_cofinal_source :
    (∃ ready time, classify prior input origin roster menus = .live ready time) ↔
      (∀ n, Ready n) ∧ ClockCofinal prior input origin roster menus := by
  constructor
  · rintro ⟨ready, time, _⟩
    exact ⟨ready, time⟩
  · rintro ⟨ready, time⟩
    cases classify prior input origin roster menus with
    | firstRefusal visit failed _ =>
      exact ((ready_refutes_a_fault prior input origin roster menus visit (ready visit)) failed).elim
    | bounded _ limit stays =>
      obtain ⟨n, _, above⟩ := time 0 limit
      exact ((not_lt_of_ge (stays n)) above).elim
    | live ready time => exact ⟨ready, time, rfl⟩

theorem every_actual_first_refusal_names_every_missing_offer (visit : Nat) (failed : Failed visit) :
    (∀ word ∈ (Event visit).offers, ¬ Supply.Period input origin (Event visit).before.raw roster word) ∧
      (Event (visit + 1)).before = (Event visit).before ∧ (Event visit).items = [] :=
  ⟨((Event visit).fails_iff).mp failed,
    refused_visit_preserves_the_current_and_has_no_items prior input origin roster menus visit failed⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
