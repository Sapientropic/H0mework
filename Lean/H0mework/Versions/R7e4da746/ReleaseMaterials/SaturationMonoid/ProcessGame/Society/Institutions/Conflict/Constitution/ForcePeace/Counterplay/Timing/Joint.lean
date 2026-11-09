import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window StepFailure RoundFailure inspectRound inspectStep)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Pos" => Position Party Good Port Technology Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (allowed : Position Party Good Port Technology Instrument CivilView OpponentView →
    Turn → Reparation.Actual.Input Party Good Port Technology Instrument → Prop)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)

abbrev VisitAllowed (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn) (tick : Nat) : Prop :=
  allowed (game.play plan.submit opponent arbitrate tick) (game.turnAt plan.submit opponent arbitrate tick)
    (game.inputAt plan.submit opponent arbitrate tick)

inductive JointIssue (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn) (tick : Nat)
  | material (permit : game.VisitAllowed allowed plan opponent arbitrate tick)
      (failed : StepFailure game.seed game.command game.community (game.turnAt plan.submit opponent arbitrate tick).isCivil
        (game.play plan.submit opponent arbitrate tick).window (game.inputAt plan.submit opponent arbitrate tick))
  | exit (failed : RoundFailure game.seed game.command game.community
      (Window.at (game.currentAt plan.submit opponent arbitrate tick)) (game.exitAt plan opponent arbitrate tick) [])

/-- The rival and arbitration are fixed only for the finite original
prefix. An exit can fail at a legal cut even if no following visit is allowed. -/
structure JointBreach where
  opponent : List OpponentView → Input
  arbitrate : Nat → C → Turn
  tick : Nat
  prior : game.AllowsBefore allowed plan opponent arbitrate tick
  issue : game.JointIssue allowed plan opponent arbitrate tick

def jointSafeBefore (limit : Nat) : Prop :=
  ∀ (opponent : List OpponentView → Input) (arbitrate : Nat → C → Turn) (tick : Nat), tick < limit →
    game.AllowsBefore allowed plan opponent arbitrate tick →
    game.exitGoodAt plan opponent arbitrate tick ∧
      (game.VisitAllowed allowed plan opponent arbitrate tick → game.stepGoodAt plan opponent arbitrate tick)

theorem joint_safety_before_iff_no_earlier_original_breach (limit : Nat) :
    game.jointSafeBefore allowed plan limit ↔ ∀ breach : game.JointBreach allowed plan, limit ≤ breach.tick := by
  classical
  constructor
  · intro safe breach
    by_contra notBefore
    have checks := safe breach.opponent breach.arbitrate breach.tick (lt_of_not_ge notBefore) breach.prior
    cases breach.issue with
    | material permit failed => exact failed.refutes (checks.2 permit)
    | exit failed => exact failed.refutes checks.1
  · intro before opponent arbitrate tick earlier prior
    let cut := game.currentAt plan.submit opponent arbitrate tick
    let exit := game.exitAt plan opponent arbitrate tick
    cases inspectRound game.seed game.command game.community (Window.at cut) exit [] with
    | inl issue =>
      exact (not_lt_of_ge (before ⟨opponent, arbitrate, tick, prior, .exit issue⟩) earlier).elim
    | inr exitChecked =>
      refine ⟨exitChecked.down, fun permit => ?_⟩
      cases inspectStep game.seed game.command game.community (game.turnAt plan.submit opponent arbitrate tick).isCivil
          (game.play plan.submit opponent arbitrate tick).window (game.inputAt plan.submit opponent arbitrate tick) with
      | inl issue =>
        exact (not_lt_of_ge (before ⟨opponent, arbitrate, tick, prior, .material permit issue⟩) earlier).elim
      | inr step => exact step.down

theorem preserving_allowed_prefixes_iff_every_finite_joint_boundary_is_safe :
    game.PreservesAllowedPrefixes allowed plan ↔ ∀ limit, game.jointSafeBefore allowed plan limit := by
  constructor
  · exact fun safe _ opponent arbitrate tick _ prior => safe opponent arbitrate tick prior
  · exact fun safe opponent arbitrate tick prior => safe (tick + 1) opponent arbitrate tick (Nat.lt_succ_self tick) prior

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
