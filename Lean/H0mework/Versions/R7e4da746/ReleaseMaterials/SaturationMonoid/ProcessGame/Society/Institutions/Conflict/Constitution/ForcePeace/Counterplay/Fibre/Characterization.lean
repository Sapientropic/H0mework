import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Pos" => Position Party Good Port Technology Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)

private def replaceReply (opponent : Opponent) (tick : Nat) (reply : Input) : Opponent :=
  fun seen => if seen.length = tick + 1 then reply else opponent seen

private def replaceTurn (arbitrate : Arbitration) (tick : Nat) (lane : Turn) : Arbitration :=
  fun n cut => if n = tick then lane else arbitrate n cut

section OneVisit

variable (plan : CivilPlan Party Good Port Technology Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

variable (tick : Nat) (lane : Turn)
  (reply : Reparation.Actual.Input Party Good Port Technology Instrument)

local notation "newOpponent" => replaceReply opponent tick reply
local notation "newArbitration" => replaceTurn arbitrate tick lane

omit [DecidableEq Community] in
private theorem sameEarlierInput {n : Nat} (earlier : n < tick)
    (same : game.play plan.submit newOpponent newArbitration n = game.play plan.submit opponent arbitrate n) :
    game.inputAt plan.submit newOpponent newArbitration n = game.inputAt plan.submit opponent arbitrate n := by
  unfold inputAt turnAt
  rw [same]
  simp only [replaceTurn, if_neg (Nat.ne_of_lt earlier)]
  cases arbitrate n (game.play plan.submit opponent arbitrate n).window.current with
  | civil => rfl
  | retained => rfl
  | opponent =>
    simp only [proposal, replaceReply, game.opponent_history_length plan opponent arbitrate,
      if_neg (by omega : n + 1 ≠ tick + 1)]

omit [DecidableEq Community] in
private theorem sameEarlierPosition {n : Nat} (earlier : n ≤ tick) :
    game.play plan.submit newOpponent newArbitration n = game.play plan.submit opponent arbitrate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have prior := ih (Nat.le_of_succ_le earlier)
    have input := game.sameEarlierInput plan opponent arbitrate tick lane reply (Nat.lt_of_succ_le earlier) prior
    change game.extend (game.play plan.submit newOpponent newArbitration n)
      (game.inputAt plan.submit newOpponent newArbitration n) =
      game.extend (game.play plan.submit opponent arbitrate n) (game.inputAt plan.submit opponent arbitrate n)
    rw [prior, input]

omit [DecidableEq Community] in
private theorem reply_is_selected :
    game.inputAt plan.submit newOpponent newArbitration tick =
      let prior := game.play plan.submit opponent arbitrate tick
      proposal prior (fun _ => plan.submit prior.civilSeen) (fun _ => reply) lane := by
  unfold inputAt turnAt
  rw [game.sameEarlierPosition plan opponent arbitrate tick lane reply le_rfl]
  rw [show replaceTurn arbitrate tick lane tick (game.play plan.submit opponent arbitrate tick).window.current =
    lane from if_pos rfl]
  cases lane with
  | civil => rfl
  | retained => rfl
  | opponent =>
    simp [proposal, replaceReply, game.opponent_history_length plan opponent arbitrate]

omit [DecidableEq Community] in
/-- A permitted local visit extends the reached original prefix. The
opponent changes its reply only at the observation length of this visit. -/
theorem one_allowed_visit_extends_the_actual_prefix (allowed : Pos → Turn → Input → Prop)
    (admitted : game.AllowsBefore allowed plan opponent arbitrate tick)
    (permitted : let prior := game.play plan.submit opponent arbitrate tick
      allowed prior lane (proposal prior (fun _ => plan.submit prior.civilSeen) (fun _ => reply) lane)) :
    let prior := game.play plan.submit opponent arbitrate tick
    let chosen := proposal prior (fun _ => plan.submit prior.civilSeen) (fun _ => reply) lane
    ∃ (trial : Opponent) (schedule : Arbitration),
      game.AllowsBefore allowed plan trial schedule (tick + 1) ∧
      game.play plan.submit trial schedule tick = prior ∧
      game.turnAt plan.submit trial schedule tick = lane ∧
      game.inputAt plan.submit trial schedule tick = chosen ∧
      game.play plan.submit trial schedule (tick + 1) = game.extend prior chosen := by
  let trial := replaceReply opponent tick reply
  let schedule := replaceTurn arbitrate tick lane
  have prior : ∀ n ≤ tick, game.play plan.submit trial schedule n = game.play plan.submit opponent arbitrate n :=
    fun _ bound => game.sameEarlierPosition plan opponent arbitrate tick lane reply bound
  have earlier : game.AllowsBefore allowed plan trial schedule tick := by
    intro n before
    have turn : game.turnAt plan.submit trial schedule n = game.turnAt plan.submit opponent arbitrate n := by
      unfold turnAt
      rw [prior n before.le]
      exact if_neg (Nat.ne_of_lt before)
    rw [prior n before.le, turn, game.sameEarlierInput plan opponent arbitrate tick lane reply before (prior n before.le)]
    exact admitted n before
  have selected := game.reply_is_selected plan opponent arbitrate tick lane reply
  have choosesLane : game.turnAt plan.submit trial schedule tick = lane := if_pos rfl
  have nextAllowed : allowed (game.play plan.submit trial schedule tick) (game.turnAt plan.submit trial schedule tick)
      (game.inputAt plan.submit trial schedule tick) := by
    rw [prior tick le_rfl, choosesLane, selected]
    exact permitted
  refine ⟨trial, schedule, ?_, prior tick le_rfl, choosesLane, selected, ?_⟩
  · intro n before
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ before) with strict | rfl
    · exact earlier n strict
    · exact nextAllowed
  · change game.extend (game.play plan.submit trial schedule tick) (game.inputAt plan.submit trial schedule tick) = _
    rw [prior tick le_rfl, selected]

end OneVisit

theorem one_observation_plan_preserves_the_allowed_prefixes_iff_a_family_closes
    (civilChoice : List CivilView → Input → Prop) (allowed : Pos → Turn → Input → Prop) :
    (∃ plan : Plan, (∀ seen, civilChoice seen (plan.submit seen)) ∧ game.PreservesAllowedPrefixes allowed plan) ↔
      ∃ family : Pos → Prop, family game.start ∧ game.FibreCloses civilChoice allowed family := by
  constructor
  · rintro ⟨plan, civil, preserves⟩
    let family (position : Pos) : Prop := ∃ (opponent : Opponent) (arbitrate : Arbitration) (tick : Nat),
      game.AllowsBefore allowed plan opponent arbitrate tick ∧ game.play plan.submit opponent arbitrate tick = position
    refine ⟨family, ⟨fun _ => none, fun _ _ => .retained, 0, fun _ before => (Nat.not_lt_zero _ before).elim, rfl⟩, ?_⟩
    intro seen
    refine ⟨⟨plan.submit seen, plan.exit seen⟩, civil seen, ?_⟩
    rintro _ ⟨opponent, arbitrate, tick, admitted, rfl⟩ visible
    have exit := (preserves opponent arbitrate tick admitted).1
    rw [← visible]
    refine ⟨exit, fun lane reply permitted => ?_⟩
    obtain ⟨trial, schedule, legal, prior, choosesLane, selected, successor⟩ :=
      game.one_allowed_visit_extends_the_actual_prefix plan opponent arbitrate tick lane reply allowed admitted permitted
    have earlier : game.AllowsBefore allowed plan trial schedule tick :=
      fun n before => legal n (before.trans (Nat.lt_succ_self tick))
    have good := (preserves trial schedule tick earlier).2 (legal tick (Nat.lt_succ_self tick))
    unfold stepGoodAt at good
    rw [choosesLane, prior, selected] at good
    exact ⟨good, trial, schedule, tick + 1, legal, successor⟩
  · rintro ⟨family, initial, closed⟩
    exact ⟨game.compileFibre civilChoice allowed family closed,
      game.compileFibre_uses_the_original_civil_choice civilChoice allowed family closed,
      game.compileFibre_preserves_each_allowed_original_prefix civilChoice allowed family initial closed⟩

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
