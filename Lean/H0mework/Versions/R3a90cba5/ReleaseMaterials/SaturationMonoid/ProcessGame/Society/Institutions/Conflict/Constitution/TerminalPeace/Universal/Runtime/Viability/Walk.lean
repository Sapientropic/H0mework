import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Distance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)

/-- Only the current viable cut and its current finite clock target are
carried. At the next cut the shortest remaining length is recomputed. -/
structure Cursor where
  raw : RawCurrent Party Good Technology Instrument
  live : Live input origin roster raw
  goal : ℚ
  unreached : raw.clock ≤ goal

namespace Cursor

variable {input origin roster}

def start (raw : RawCurrent Party Good Technology Instrument) (live : Live input origin roster raw) :
    Cursor input origin roster :=
  ⟨raw, live, raw.clock + 1, le_add_of_nonneg_right zero_le_one⟩

variable (prior : Cursor input origin roster)

abbrev distance : Nat := prior.live.distance prior.goal

def choice : Step prior.live prior.goal := prior.live.chooseStep prior.goal prior.unreached

theorem same_raw_and_goal_choose_the_same_word (other : Cursor input origin roster)
    (sameRaw : prior.raw = other.raw) (sameGoal : prior.goal = other.goal) :
    prior.choice.move.word = other.choice.move.word := by
  have same : prior = other := by
    cases prior
    cases other
    cases sameRaw
    cases sameGoal
    rfl
  exact congrArg (fun cursor => cursor.choice.move.word) same

theorem the_selected_word_cannot_end_in_a_dead_cut (other : Move input origin roster prior.raw)
    (dead : ¬ Live input origin roster other.next) :
    prior.choice.move.word ≠ other.word := by
  intro same
  have sameNext : prior.choice.move.next = other.next := congrArg (input.law.next prior.raw) same
  exact dead (sameNext ▸ prior.choice.retains)

def step : Cursor input origin roster :=
  if passed : prior.goal < prior.choice.move.next.clock then
    start prior.choice.move.next prior.choice.retains
  else ⟨prior.choice.move.next, prior.choice.retains, prior.goal, le_of_not_gt passed⟩

theorem step_raw : prior.step.raw = prior.choice.move.next := by
  unfold step
  split <;> rfl

theorem step_clock : prior.raw.clock < prior.step.raw.clock := by
  rw [step_raw]
  exact prior.choice.move.clock_advances

theorem step_keeps_goal (unpassed : ¬ prior.goal < prior.step.raw.clock) :
    prior.step.goal = prior.goal := by
  rw [step_raw] at unpassed
  simp only [step, dif_neg unpassed]

theorem step_restarts_goal (passed : prior.goal < prior.step.raw.clock) :
    prior.step.goal = prior.step.raw.clock + 1 := by
  rw [step_raw] at passed
  simp only [step, dif_pos passed, start]

theorem step_spends_one (unpassed : ¬ prior.goal < prior.step.raw.clock) :
    prior.step.distance + 1 = prior.distance := by
  rw [step_raw] at unpassed
  simp only [step, dif_neg unpassed, distance]
  exact prior.choice.spendsOne

def run : Nat → Cursor input origin roster
  | 0 => prior
  | n + 1 => (run n).step

theorem run_add (n m : Nat) : prior.run (n + m) = (prior.run n).run m := by
  induction m with
  | zero => rfl
  | succ m earlier =>
    change (prior.run (n + m)).step = ((prior.run n).run m).step
    rw [earlier]

theorem run_clock_mono : Monotone (fun n => (prior.run n).raw.clock) :=
  monotone_nat_of_le_succ (fun n => (prior.run n).step_clock.le)

def runPath : (n : Nat) → Path input origin roster prior.raw n (prior.run n).raw
  | 0 => .nil _
  | n + 1 => by
    change Path input origin roster prior.raw (n + 1) ((prior.run n).step).raw
    rw [step_raw]
    exact (runPath n).snoc (prior.run n).choice.move

private theorem passes_its_goal_within_distance :
    ∃ n ≤ prior.distance, prior.goal < (prior.run n).raw.clock := by
  generalize currentDistance : prior.distance = length
  induction length generalizing prior with
  | zero =>
    have spent : prior.choice.retains.distance prior.goal + 1 = prior.distance := prior.choice.spendsOne
    omega
  | succ length earlier =>
    by_cases crossed : prior.goal < prior.step.raw.clock
    · exact ⟨1, Nat.succ_le_succ (Nat.zero_le _), crossed⟩
    · have spent := prior.step_spends_one crossed
      have remaining : prior.step.distance = length := by omega
      obtain ⟨n, inside, beyond⟩ := earlier prior.step remaining
      refine ⟨1 + n, by omega, ?_⟩
      rw [prior.run_add, ← prior.step_keeps_goal crossed]
      exact beyond

theorem passes_its_goal_at_the_exact_minimum :
    prior.goal < (prior.run prior.distance).raw.clock ∧
      ∀ n < prior.distance, (prior.run n).raw.clock ≤ prior.goal := by
  have minLength (n : Nat) (passed : prior.goal < (prior.run n).raw.clock) : prior.distance ≤ n :=
    prior.live.distance_le ⟨(prior.run n).raw, ⟨prior.runPath n⟩, (prior.run n).live, passed⟩
  obtain ⟨n, inside, beyond⟩ := prior.passes_its_goal_within_distance
  have exactLength := le_antisymm inside (minLength n beyond)
  refine ⟨exactLength ▸ beyond, ?_⟩
  intro earlier before
  exact le_of_not_gt (fun crossed => (not_le_of_gt before) (minLength earlier crossed))

private theorem keeps_the_original_goal_until_passed (n : Nat) (within : (prior.run n).raw.clock ≤ prior.goal) :
    (prior.run n).goal = prior.goal := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    let last := prior.run n
    have same := earlier (last.step_clock.le.trans within)
    have stays : ¬ last.goal < last.step.raw.clock := by
      change ¬ (prior.run n).goal < (prior.run (n + 1)).raw.clock
      rw [same]
      exact not_lt_of_ge within
    exact (last.step_keeps_goal stays).trans same

theorem resets_the_target_at_the_first_crossing :
    (prior.run prior.distance).goal = (prior.run prior.distance).raw.clock + 1 := by
  have crossed := prior.passes_its_goal_at_the_exact_minimum
  cases length : prior.distance with
  | zero =>
    rw [length] at crossed
    exact ((not_lt_of_ge prior.unreached) crossed.1).elim
  | succ n =>
    have before : n < prior.distance := length.symm ▸ Nat.lt_succ_self n
    have last := prior.keeps_the_original_goal_until_passed n (crossed.2 n before)
    apply (prior.run n).step_restarts_goal
    rw [last]
    rw [length] at crossed
    exact crossed.1

end Cursor

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability
