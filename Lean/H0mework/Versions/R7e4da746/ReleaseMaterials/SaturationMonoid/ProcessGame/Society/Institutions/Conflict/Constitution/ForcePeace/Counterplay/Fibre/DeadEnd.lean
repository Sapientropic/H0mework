import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre.Characterization
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre.Viability

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

structure AllowedDeadEnd (allowed : Pos → Turn → Input → Prop) (plan : Plan) where
  opponent : Opponent
  arbitrate : Arbitration
  tick : Nat
  prior : game.AllowsBefore allowed plan opponent arbitrate tick
  unavailable : let position := game.play plan.submit opponent arbitrate tick
    ∀ (lane : Turn) (reply : Input), ¬ allowed position lane
      (proposal position (fun _ => plan.submit position.civilSeen) (fun _ => reply) lane)

/-- The failure of all complete allowed executions has an actual finite
prefix with an empty menu. Safety of the prefix is a separate check. -/
def deadEndOfNoAllowedReplay (allowed : Pos → Turn → Input → Prop) (plan : Plan)
    (denied : ¬ Nonempty (game.AllowedReplay allowed plan)) : game.AllowedDeadEnd allowed plan := by
  classical
  have reached : Nonempty (game.AllowedDeadEnd allowed plan) := by
    by_contra absent
    let family (position : Pos) : Prop := ∃ (opponent : Opponent) (arbitrate : Arbitration) (tick : Nat),
      game.AllowsBefore allowed plan opponent arbitrate tick ∧ game.play plan.submit opponent arbitrate tick = position
    have initial : family game.start :=
      ⟨fun _ => none, fun _ _ => .retained, 0, fun _ earlier => (Nat.not_lt_zero _ earlier).elim, rfl⟩
    have closed : ∀ position, family position → ∀ (lane : Turn) (reply : Input),
        let input := proposal position (fun _ => plan.submit position.civilSeen) (fun _ => reply) lane
        allowed position lane input → family (game.extend position input) := by
      rintro _ ⟨opponent, arbitrate, tick, prior, rfl⟩ lane reply
      dsimp only
      intro permitted
      obtain ⟨trial, schedule, legal, _, _, _, successor⟩ :=
        game.one_allowed_visit_extends_the_actual_prefix plan opponent arbitrate tick lane reply allowed prior permitted
      exact ⟨trial, schedule, tick + 1, legal, successor⟩
    have live : LocalMenusNonempty allowed family plan := by
      rintro _ ⟨opponent, arbitrate, tick, prior, rfl⟩
      by_contra empty
      exact absent ⟨⟨opponent, arbitrate, tick, prior, fun lane reply permitted => empty ⟨(lane, reply), permitted⟩⟩⟩
    exact denied ⟨game.compileFamilyReplay allowed family plan initial closed live⟩
  exact Classical.choice reached

variable {allowed : Position Party Good Port Technology Instrument CivilView OpponentView →
    Turn → Reparation.Actual.Input Party Good Port Technology Instrument → Prop}
  {plan : CivilPlan Party Good Port Technology Instrument CivilView}
  (dead : game.AllowedDeadEnd allowed plan)

abbrev AllowedDeadEnd.publish := game.publishedAt plan dead.opponent dead.arbitrate dead.tick

theorem AllowedDeadEnd.the_dead_end_is_written_at_its_original_cut :
    let history := game.prefixAt plan dead.opponent dead.arbitrate dead.tick
    Quantities.Recorded game.seed history ∧ (dead.publish game).next =
      Reparation.Actual.run game.seed game.community history := by
  exact ⟨(dead.publish game).recorded, game.the_published_prefix_is_the_original_ledger _ _ _ _⟩

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
