import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument

/-- Each group comes from the actual inputs between two chances to act.
An empty group records that an opportunity occurred without a native tick. -/
abbrev History (Observation : Type u) := List (List Observation)

local notation "Strategy" => History Observation → Word

def observations (read : C → Observation) : W → Word → List Observation
  | _, [] => []
  | window, input :: rest =>
    let target := window.write input
    read target.current :: observations read target rest

structure Position (Party Good Port Technology Instrument : Type) (Observation : Type u)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] where
  window : Window Party Good Port Technology Instrument
  seen : History Observation

local notation "PositionAt" => Position Party Good Port Technology Instrument Observation

def Position.start (origin : C) (read : C → Observation) : PositionAt :=
  ⟨Window.at origin, [[read origin]]⟩

def Position.extend (position : PositionAt) (read : C → Observation) (move reply : Word) : PositionAt :=
  ⟨position.window.run (move ++ reply),
    position.seen ++ [observations read position.window (move ++ reply)]⟩

theorem same_observation_chooses_the_same_submission (strategy : Strategy)
    (first second : PositionAt) (same : first.seen = second.seen) :
    strategy first.seen = strategy second.seen := congrArg strategy same

structure Prefix (Party Good Port Technology Instrument : Type) (Observation : Type u)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] where
  script : Script Party Good Port Technology Instrument
  position : Position Party Good Port Technology Instrument Observation

local notation "PrefixAt" => Prefix Party Good Port Technology Instrument Observation

/-- The rival ranges over all native scripts. Rejected requests and the
priority of pending work are interpreted by the installed epoch compiler. -/
def play (origin : C) (read : C → Observation) (strategy : Strategy) (rival : Nat → Word) : Nat → PrefixAt
  | 0 => ⟨[], Position.start origin read⟩
  | round + 1 =>
      let earlier := play origin read strategy rival round
      let move := strategy earlier.position.seen
      let reply := rival round
      ⟨earlier.script ++ (move ++ reply), earlier.position.extend read move reply⟩

theorem play_is_the_original_execution (origin : C) (read : C → Observation) (strategy : Strategy)
    (rival : Nat → Word) (round : Nat) :
    (play origin read strategy rival round).position.window.current =
      Quantities.Execution.endAt origin (play origin read strategy rival round).script := by
  induction round with
  | zero => rfl
  | succ round ih =>
    simp only [play, Position.extend, Window.run_current, Quantities.Execution.endAt_append, ih]

theorem play_keeps_the_original_whole_ledger (origin : C) (read : C → Observation) (strategy : Strategy)
    (rival : Nat → Word) (round : Nat) :
    Quantities.Recorded origin (play origin read strategy rival round).script ∧
      Evolving.Epoch.Current.ClosedAt (play origin read strategy rival round).position.window.current := by
  refine ⟨Quantities.record _ _, ?_⟩
  rw [play_is_the_original_execution]
  exact (Quantities.record _ _).next

theorem play_ignores_future_submissions (origin : C) (read : C → Observation) (strategy : Strategy)
    (left right : Nat → Word) (round : Nat) (past : ∀ tick < round, left tick = right tick) :
    play origin read strategy left round = play origin read strategy right round := by
  induction round with
  | zero => rfl
  | succ round ih =>
    have same := ih (fun tick earlier => past tick (Nat.lt_succ_of_lt earlier))
    simp only [play, same, past round (Nat.lt_succ_self round)]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
