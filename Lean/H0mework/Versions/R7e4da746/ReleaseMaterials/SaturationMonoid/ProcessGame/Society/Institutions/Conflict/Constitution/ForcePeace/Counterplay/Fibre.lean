import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (ExitAtCut Script StepGood)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Pos" => Position Party Good Port Technology Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView
local notation "Word" => Script Party Good Port Technology Instrument

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)

omit [DecidableEq Community] in
theorem opponent_history_length (plan : Plan) (opponent : List OpponentView → Input)
    (arbitrate : Nat → C → Turn) (tick : Nat) :
    (game.play plan.submit opponent arbitrate tick).opponentSeen.length = tick + 1 := by
  induction tick with
  | zero => rfl
  | succ tick earlier =>
    change ((game.play plan.submit opponent arbitrate tick).opponentSeen ++ [_]).length = tick + 1 + 1
    rw [List.length_append, earlier]
    rfl

def AllowsBefore (allowed : Pos → Turn → Input → Prop)
    (plan : Plan) (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn) (limit : Nat) : Prop :=
  ∀ tick < limit, allowed (game.play plan.submit opponent arbitrate tick)
    (game.turnAt plan.submit opponent arbitrate tick) (game.inputAt plan.submit opponent arbitrate tick)

/-- An allowed finite prefix carries an independent exit. Each allowed
following visit must also meet the original standing and service checks. -/
def PreservesAllowedPrefixes (allowed : Pos → Turn → Input → Prop) (plan : Plan) : Prop :=
  ∀ (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn) (tick : Nat),
    game.AllowsBefore allowed plan opponent arbitrate tick →
      game.exitGoodAt plan opponent arbitrate tick ∧
      (allowed (game.play plan.submit opponent arbitrate tick)
        (game.turnAt plan.submit opponent arbitrate tick) (game.inputAt plan.submit opponent arbitrate tick) →
        game.stepGoodAt plan opponent arbitrate tick)

/-- The response is chosen at the common observation. The original
successor of every locally allowed dispatch remains in the family. -/
def FibreCloses (civilChoice : List CivilView → Input → Prop) (allowed : Pos → Turn → Input → Prop)
    (family : Pos → Prop) : Prop :=
  ∀ seen : List CivilView, ∃ answer : Input × Word, civilChoice seen answer.1 ∧
    ∀ position, family position → position.civilSeen = seen →
      ExitAtCut game.seed game.command game.community position.window.current answer.2 ∧
        ∀ (lane : Turn) (rival : Input),
          let input := proposal position (fun _ => answer.1) (fun _ => rival) lane
          allowed position lane input →
          StepGood game.seed game.command game.community lane.isCivil position.window input ∧
            family (game.extend position input)

def compileFibre (civilChoice : List CivilView → Input → Prop) (allowed : Pos → Turn → Input → Prop)
    (family : Pos → Prop) (closed : game.FibreCloses civilChoice allowed family) : Plan :=
  ⟨fun seen => (Classical.choose (closed seen)).1, fun seen => (Classical.choose (closed seen)).2⟩

theorem compileFibre_uses_the_original_civil_choice
    (civilChoice : List CivilView → Input → Prop) (allowed : Pos → Turn → Input → Prop)
    (family : Pos → Prop) (closed : game.FibreCloses civilChoice allowed family) (seen : List CivilView) :
    civilChoice seen ((game.compileFibre civilChoice allowed family closed).submit seen) :=
  (Classical.choose_spec (closed seen)).1

theorem compileFibre_preserves_each_allowed_original_prefix
    (civilChoice : List CivilView → Input → Prop) (allowed : Pos → Turn → Input → Prop)
    (family : Pos → Prop) (initial : family game.start) (closed : game.FibreCloses civilChoice allowed family) :
    game.PreservesAllowedPrefixes allowed (game.compileFibre civilChoice allowed family closed) := by
  let plan := game.compileFibre civilChoice allowed family closed
  intro opponent arbitrate tick admitted
  have here (position : Pos) (inside : family position) :
      ExitAtCut game.seed game.command game.community position.window.current (plan.exit position.civilSeen) ∧
        ∀ (lane : Turn) (rival : Input),
          let input := proposal position (fun _ => plan.submit position.civilSeen) (fun _ => rival) lane
          allowed position lane input →
            StepGood game.seed game.command game.community lane.isCivil position.window input ∧
              family (game.extend position input) := by
    exact (Classical.choose_spec (closed position.civilSeen)).2 position inside rfl
  have advance (n : Nat) (inside : family (game.play plan.submit opponent arbitrate n))
      (permitted : allowed (game.play plan.submit opponent arbitrate n) (game.turnAt plan.submit opponent arbitrate n)
        (game.inputAt plan.submit opponent arbitrate n)) :
      game.stepGoodAt plan opponent arbitrate n ∧ family (game.play plan.submit opponent arbitrate (n + 1)) := by
    let prior := game.play plan.submit opponent arbitrate n
    let lane := game.turnAt plan.submit opponent arbitrate n
    have same : proposal prior (fun _ => plan.submit prior.civilSeen) (fun _ => opponent prior.opponentSeen) lane =
        game.inputAt plan.submit opponent arbitrate n := by
      change _ = proposal prior plan.submit opponent lane
      cases lane <;> rfl
    have allowedHere : allowed prior lane
        (proposal prior (fun _ => plan.submit prior.civilSeen) (fun _ => opponent prior.opponentSeen) lane) := by
      rw [same]
      exact permitted
    change StepGood game.seed game.command game.community lane.isCivil prior.window (game.inputAt plan.submit opponent arbitrate n) ∧
      family (game.extend prior (game.inputAt plan.submit opponent arbitrate n))
    rw [← same]
    exact (here prior inside).2 lane (opponent prior.opponentSeen) allowedHere
  have reached (n : Nat) (bounded : n ≤ tick) : family (game.play plan.submit opponent arbitrate n) := by
    induction n with
    | zero => exact initial
    | succ n earlier =>
      exact (advance n (earlier (Nat.le_of_succ_le bounded)) (admitted n (Nat.lt_of_succ_le bounded))).2
  have current := reached tick le_rfl
  exact ⟨(here _ current).1, fun permitted => (advance tick current permitted).1⟩

theorem allowed_play_has_life_exit_and_the_original_next_ledger
    (allowed : Pos → Turn → Input → Prop) (plan : Plan)
    (preserves : game.PreservesAllowedPrefixes allowed plan)
    (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn)
    (legal : ∀ tick, game.AllowsBefore allowed plan opponent arbitrate tick) :
    game.Safe plan opponent arbitrate ∧ ∀ tick,
      HEq (game.ledger plan.submit opponent arbitrate (tick + 1))
        (Reparation.Actual.advance (game.ledger plan.submit opponent arbitrate tick)
          (game.inputAt plan.submit opponent arbitrate tick)) := by
  refine ⟨fun tick => ?_, game.every_arbitrated_tick_writes_the_original_joint_successor plan.submit opponent arbitrate⟩
  obtain ⟨exit, step⟩ := preserves opponent arbitrate tick (legal tick)
  exact ⟨step (legal (tick + 1) tick (Nat.lt_succ_self tick)), exit⟩

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
