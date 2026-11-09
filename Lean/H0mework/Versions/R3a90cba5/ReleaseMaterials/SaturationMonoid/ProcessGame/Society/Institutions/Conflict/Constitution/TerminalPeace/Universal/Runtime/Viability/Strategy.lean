import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Walk
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument} {roster : List Party}

namespace Cursor

variable (prior : Cursor input origin roster)

private theorem eventually_gains_one_clock_unit :
    ∃ n, prior.raw.clock + 1 ≤ (prior.run n).raw.clock := by
  let first := prior.run prior.distance
  have target : first.goal = first.raw.clock + 1 := prior.resets_the_target_at_the_first_crossing
  have later := first.passes_its_goal_at_the_exact_minimum.1
  rw [target] at later
  have original : prior.raw.clock ≤ first.raw.clock := prior.run_clock_mono (Nat.zero_le _)
  refine ⟨prior.distance + first.distance, ?_⟩
  rw [prior.run_add]
  exact (add_le_add_left original 1).trans later.le

private theorem reaches_every_whole_clock_increment (increment : Nat) :
    ∃ n, prior.raw.clock + increment ≤ (prior.run n).raw.clock := by
  induction increment with
  | zero => exact ⟨0, by simp [run]⟩
  | succ increment earlier =>
    obtain ⟨n, advanced⟩ := earlier
    obtain ⟨extra, later⟩ := (prior.run n).eventually_gains_one_clock_unit
    refine ⟨n + extra, ?_⟩
    rw [prior.run_add, Nat.cast_succ, ← add_assoc]
    exact (add_le_add_left advanced 1).trans later

theorem clock_is_cofinal_after_every_cut (cut : Nat) (bound : ℚ) :
    ∃ n ≥ cut, bound < (prior.run n).raw.clock := by
  obtain ⟨increment, above⟩ := exists_nat_gt (bound - prior.raw.clock)
  obtain ⟨n, paid⟩ := prior.reaches_every_whole_clock_increment increment
  have beyond : bound < (prior.run n).raw.clock := by linarith only [above, paid]
  exact ⟨max cut n, Nat.le_max_left _ _, beyond.trans_le (prior.run_clock_mono (Nat.le_max_right _ _))⟩

end Cursor

theorem live_is_the_greatest_postfixed_region :
    Postfixed input origin roster (Live input origin roster) ∧
    ∀ region, Postfixed input origin roster region →
      ∀ raw, region raw → Live input origin roster raw :=
  ⟨fun _ live bound => live.reaches bound, fun region postfixed _ inside => ⟨region, postfixed, inside⟩⟩

variable {raw : RawCurrent Party Good Technology Instrument}

/-- Extract a trajectory mathematically from the largest live region.
Every emitted word still belongs to the original registered alphabet. -/
def strategy (live : Live input origin roster raw) : Trajectory input origin roster raw :=
  let start := Cursor.start raw live
  { state := fun n => (start.run n).raw
    initial := rfl
    move := fun n => (start.run n).choice.move
    next_eq := fun n => (start.run n).step_raw
    cofinal := start.clock_is_cofinal_after_every_cut }

theorem live_iff_cofinal_trajectory :
    Live input origin roster raw ↔ Nonempty (Trajectory input origin roster raw) :=
  ⟨fun live => ⟨strategy live⟩, fun ⟨actual⟩ => actual.initial_is_live⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability
