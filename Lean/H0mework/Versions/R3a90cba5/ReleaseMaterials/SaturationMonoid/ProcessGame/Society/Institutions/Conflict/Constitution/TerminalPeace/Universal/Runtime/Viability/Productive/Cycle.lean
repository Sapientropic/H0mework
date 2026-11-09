import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Productive.Retiming
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Region
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw finish : RawCurrent Party Good Technology Instrument} {roster : List Party} {length : Nat}

namespace Path

private def append :
    {raw pivot finish : Raw} → {n m : Nat} →
    Path input origin roster raw n pivot → Path input origin roster pivot m finish →
      Path input origin roster raw (n + m) finish
  | _, _, _, _, _, .nil _, back => by simpa only [Nat.zero_add] using back
  | _, _, _, _, _, .cons first rest, back => by
    simpa only [Nat.add_right_comm _ 1] using Path.cons first (append rest back)

theorem round_exact (path : Path input origin roster raw length finish) :
    finish.round = raw.round + length := by
  induction path with
  | nil => rfl
  | cons _ _ later => exact later.trans (Nat.add_right_comm _ 1 _)

theorem clock_advances_of_positive (path : Path input origin roster raw length finish)
    (positive : 0 < length) : raw.clock < finish.clock := by
  cases path with
  | nil => exact (Nat.lt_irrefl _ positive).elim
  | cons first rest => exact first.clock_advances.trans_le rest.clock_never_decreases

/-- Repeat the given material cycle on the same source. Each copy is
interpreted at its own actual cuts and preserves the original individual
exit witnesses, even if resources decrease during the cycle. -/
def repeatCycle (path : Path input origin roster raw length finish)
    (timing : input.law.TimeIndependent) (stable : path.RetimeStable)
    (closed : finish = raw.retime finish.clock finish.round) (clock : ℚ) (round : Nat) :
    (n : Nat) → Path input origin roster (shifted raw clock round) (n * length)
      (shifted raw (clock + (n : ℚ) * (finish.clock - raw.clock)) (round + n * length))
  | 0 => by
    simpa only [Nat.zero_mul, Nat.cast_zero, zero_mul, add_zero, Nat.add_zero] using
      Path.nil (input := input) (origin := origin) (roster := roster) (shifted raw clock round)
  | n + 1 => by
    let elapsed := finish.clock - raw.clock
    let front := repeatCycle path timing stable closed clock round n
    let back := path.retime timing (clock + (n : ℚ) * elapsed) (round + n * length) stable
    have arrives :
        shifted finish (clock + (n : ℚ) * elapsed) (round + n * length) =
          shifted raw (clock + ((n + 1 : Nat) : ℚ) * elapsed) (round + (n + 1) * length) := by
      apply RawCurrent.ext
      · change finish.stock = raw.stock
        have same := congrArg (fun state : Raw => state.stock) closed
        exact same
      · change finish.claims = raw.claims
        have same := congrArg (fun state : Raw => state.claims) closed
        exact same
      · change finish.technology = raw.technology
        have same := congrArg (fun state : Raw => state.technology) closed
        exact same
      · change finish.clock + (clock + (n : ℚ) * elapsed) =
          raw.clock + (clock + ((n + 1 : Nat) : ℚ) * elapsed)
        simp only [Nat.cast_succ, elapsed]
        ring
      · change finish.round + (round + n * length) = raw.round + (round + (n + 1) * length)
        rw [path.round_exact, Nat.succ_mul]
        omega
    have composed :
        Path input origin roster (shifted raw clock round) (n * length + length)
          (shifted raw (clock + ((n + 1 : Nat) : ℚ) * elapsed) (round + (n + 1) * length)) :=
      arrives ▸ append front back
    simpa only [Nat.succ_mul] using composed

/-- One nonempty finite paid cycle produces membership in the greatest
cofinal live region. A duration bound or future schedule is derived
from that cycle. -/
theorem cycle_is_live_at_shift (path : Path input origin roster raw length finish)
    (timing : input.law.TimeIndependent) (stable : path.RetimeStable)
    (positive : 0 < length) (closed : finish = raw.retime finish.clock finish.round)
    (delay : ℚ) (rounds : Nat) :
    Live input origin roster (shifted raw delay rounds) := by
  let region : Raw → Prop := fun current => ∃ clock round, current = shifted raw clock round
  have advancing := sub_pos.mpr (path.clock_advances_of_positive positive)
  refine ⟨region, ?_, ⟨delay, rounds, rfl⟩⟩
  rintro current ⟨clock, round, rfl⟩ bound
  obtain ⟨n, more⟩ := exists_nat_gt ((bound - (raw.clock + clock)) / (finish.clock - raw.clock))
  have enough := (div_lt_iff₀ advancing).mp more
  refine ⟨n * length, _, ⟨path.repeatCycle timing stable closed clock round n⟩, ⟨_, _, rfl⟩, ?_⟩
  change bound < raw.clock + (clock + (n : ℚ) * (finish.clock - raw.clock))
  linarith only [enough]

theorem cycle_is_live (path : Path input origin roster raw length finish)
    (timing : input.law.TimeIndependent) (stable : path.RetimeStable)
    (positive : 0 < length) (closed : finish = raw.retime finish.clock finish.round) :
    Live input origin roster raw := by
  have same : shifted raw 0 0 = raw := by
    simp only [shifted, add_zero]
    cases raw
    rfl
  exact same ▸ path.cycle_is_live_at_shift timing stable positive closed 0 0

theorem cycle_restarts (path : Path input origin roster raw length finish)
    (timing : input.law.TimeIndependent) (stable : path.RetimeStable)
    (positive : 0 < length) (closed : finish = raw.retime finish.clock finish.round) :
    Live input origin roster finish := by
  have same : shifted raw (finish.clock - raw.clock) length = finish := by
    unfold shifted
    rw [← path.round_exact, show raw.clock + (finish.clock - raw.clock) = finish.clock by ring]
    exact closed.symm
  exact same ▸ path.cycle_is_live_at_shift timing stable positive closed (finish.clock - raw.clock) length

theorem cycle_is_live_of_source (path : Path input origin roster raw length finish)
    (timing : input.law.TimeIndependent) (stable : ∀ current, RetimeStableAt input current)
    (positive : 0 < length) (closed : finish = raw.retime finish.clock finish.round) :
    Live input origin roster raw :=
  path.cycle_is_live timing (path.retimeStable_of_source stable) positive closed

end Path

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability
