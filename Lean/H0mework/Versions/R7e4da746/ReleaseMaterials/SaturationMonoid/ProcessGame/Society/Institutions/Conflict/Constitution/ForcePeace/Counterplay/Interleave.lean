import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Window
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Script Window)
open Quantities.Execution (endAt query)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument

inductive Turn where
  | civil
  | opponent
  | retained
  deriving DecidableEq

abbrev Turn.isCivil : Turn → Bool
  | .civil => true
  | _ => false

/-- Observations read only the current already reached by the original fold.
The arbitration chooses whose proposal is passed to the native dispatcher. -/
structure Game (Party Good Port Technology Instrument Community : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
    (CivilView : Type u) (OpponentView : Type v) where
  seed : Root.Cut Party Good Port Technology Instrument
  past : Script Party Good Port Technology Instrument
  community : Party → Community
  command : List Party
  observeCivil : Root.Cut Party Good Port Technology Instrument → CivilView
  observeOpponent : Root.Cut Party Good Port Technology Instrument → OpponentView

local notation "CivilPolicy" => List CivilView → Input
local notation "OpponentPolicy" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

structure Position (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
    (CivilView : Type u) (OpponentView : Type v) where
  script : Script Party Good Port Technology Instrument
  window : Window Party Good Port Technology Instrument
  civilSeen : List CivilView
  opponentSeen : List OpponentView

local notation "P" => Position Party Good Port Technology Instrument CivilView OpponentView

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)

abbrev opening := (Window.at game.seed).run game.past

def start : P :=
  ⟨[], game.opening, [game.observeCivil game.opening.current], [game.observeOpponent game.opening.current]⟩

def proposal (position : P) (civil : CivilPolicy) (opponent : OpponentPolicy) : Turn → Input
  | .civil => civil position.civilSeen
  | .opponent => opponent position.opponentSeen
  | .retained => none

def extend (position : P) (input : Input) : P :=
  let next := position.window.write input
  ⟨position.script ++ [input], next, position.civilSeen ++ [game.observeCivil next.current],
    position.opponentSeen ++ [game.observeOpponent next.current]⟩

def play (civil : CivilPolicy) (opponent : OpponentPolicy) (arbitrate : Arbitration) : Nat → P
  | 0 => game.start
  | tick + 1 =>
      let prior := play civil opponent arbitrate tick
      game.extend prior (proposal prior civil opponent (arbitrate tick prior.window.current))

variable (civil : List CivilView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

abbrev turnAt (tick : Nat) : Turn := arbitrate tick (game.play civil opponent arbitrate tick).window.current
abbrev inputAt (tick : Nat) : Input :=
  proposal (game.play civil opponent arbitrate tick) civil opponent (game.turnAt civil opponent arbitrate tick)
abbrev scriptAt (tick : Nat) : Word := (game.play civil opponent arbitrate tick).script
abbrev currentAt (tick : Nat) : C := (game.play civil opponent arbitrate tick).window.current

theorem play_succ_script (tick : Nat) :
    game.scriptAt civil opponent arbitrate (tick + 1) =
      game.scriptAt civil opponent arbitrate tick ++ [game.inputAt civil opponent arbitrate tick] := rfl

theorem play_is_the_original_current (tick : Nat) :
    game.currentAt civil opponent arbitrate tick = endAt game.seed (game.past ++ game.scriptAt civil opponent arbitrate tick) := by
  induction tick with
  | zero =>
    change ((Window.at game.seed).run game.past).current = endAt game.seed (game.past ++ [])
    rw [List.append_nil, Window.run_current]
    rfl
  | succ tick earlier =>
    change ((game.play civil opponent arbitrate tick).window.write
      (game.inputAt civil opponent arbitrate tick)).current = _
    rw [Window.write_current, Window.nextCut]
    change Quantities.Execution.next (game.currentAt civil opponent arbitrate tick)
      (game.inputAt civil opponent arbitrate tick) = _
    rw [earlier, play_succ_script, ← List.append_assoc]
    exact (Quantities.Execution.endAt_append game.seed
      (game.past ++ game.scriptAt civil opponent arbitrate tick)
      [game.inputAt civil opponent arbitrate tick]).symm

theorem equal_civil_observations_choose_the_same_input (civil : CivilPolicy) (opponent : OpponentPolicy) (first second : P)
    (equal : first.civilSeen = second.civilSeen) :
    proposal first civil opponent .civil = proposal second civil opponent .civil := congrArg civil equal

theorem equal_opponent_observations_choose_the_same_input (civil : CivilPolicy) (opponent : OpponentPolicy) (first second : P)
    (equal : first.opponentSeen = second.opponentSeen) :
    proposal first civil opponent .opponent = proposal second civil opponent .opponent := congrArg opponent equal

abbrev originalDispatch (tick : Nat) :=
  Reparation.Transport.inspect (query (game.currentAt civil opponent arbitrate tick)
    (game.inputAt civil opponent arbitrate tick))

theorem a_busy_original_visit_does_not_spend_the_chosen_proposal (tick : Nat)
    (busy : Reparation.Transport.NativeWork (game.currentAt civil opponent arbitrate tick)) :
    Quantities.Execution.inventory (game.currentAt civil opponent arbitrate tick)
      [game.inputAt civil opponent arbitrate tick] = [] := by
  apply Reparation.Transport.native_step_has_no_material_items
  generalize game.inputAt civil opponent arbitrate tick = input
  cases input <;> exact busy

theorem every_interleaving_prefix_is_recorded (tick : Nat) :
    Quantities.Recorded game.seed (game.past ++ game.scriptAt civil opponent arbitrate tick) :=
  Quantities.record _ _

variable [DecidableEq Community]

abbrev ledger (tick : Nat) := Reparation.Actual.run game.seed game.community
  (game.past ++ game.scriptAt civil opponent arbitrate tick)

theorem every_arbitrated_tick_writes_the_original_joint_successor (tick : Nat) :
    HEq (game.ledger civil opponent arbitrate (tick + 1))
      (Reparation.Actual.advance (game.ledger civil opponent arbitrate tick) (game.inputAt civil opponent arbitrate tick)) := by
  unfold ledger
  rw [play_succ_script, ← List.append_assoc, Reparation.Actual.run_snoc]

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
