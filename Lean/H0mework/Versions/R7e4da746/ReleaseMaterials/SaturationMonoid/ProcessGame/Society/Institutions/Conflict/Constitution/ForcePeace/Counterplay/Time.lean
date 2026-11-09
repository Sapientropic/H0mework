import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Allowed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Script)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (completed : Script Party Good Port Technology Instrument → Prop)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

def TimeCofinal : Prop :=
  ∀ bound : ℚ, ∃ tick, bound ≤ (game.currentAt plan.submit opponent arbitrate tick).raw.clock

def LiveSuccess : Prop := game.Succeeds completed plan opponent arbitrate ∧ game.TimeCofinal plan opponent arbitrate

structure TimeStall where
  bound : ℚ
  trapped : ∀ tick, (game.currentAt plan.submit opponent arbitrate tick).raw.clock < bound

theorem TimeStall.each_prefix_writes_the_original_successor
    (stall : game.TimeStall plan opponent arbitrate) (tick : Nat) :
    let written := game.publishedAt plan opponent arbitrate (tick + 1)
    (game.currentAt plan.submit opponent arbitrate (tick + 1)).raw.clock < stall.bound ∧
      Quantities.Recorded game.seed (game.prefixAt plan opponent arbitrate (tick + 1)) ∧
      HEq written.next (Reparation.Actual.advance (game.publishedAt plan opponent arbitrate tick).next
        (game.inputAt plan.submit opponent arbitrate tick)) := by
  refine ⟨stall.trapped _, (game.publishedAt plan opponent arbitrate _).recorded, ?_⟩
  rw [game.the_published_prefix_is_the_original_ledger, game.the_published_prefix_is_the_original_ledger]
  exact game.every_arbitrated_tick_writes_the_original_joint_successor plan.submit opponent arbitrate tick

/-- Finite safety, effective withdrawal and unbounded physical time are
separate obligations on one actual trajectory. -/
theorem a_live_play_fails_iff_first_defeat_pending_forever_or_an_original_clock_bound :
    ¬ game.LiveSuccess completed plan opponent arbitrate ↔
      Nonempty (game.Counter completed plan opponent arbitrate) ∨
      (game.Succeeds completed plan opponent arbitrate ∧ Nonempty (game.TimeStall plan opponent arbitrate)) := by
  classical
  constructor
  · intro denied
    by_cases succeeds : game.Succeeds completed plan opponent arbitrate
    · right
      refine ⟨succeeds, ?_⟩
      have bounded : ∃ bound : ℚ, ∀ tick,
          (game.currentAt plan.submit opponent arbitrate tick).raw.clock < bound := by
        by_contra unbounded
        apply denied
        refine ⟨succeeds, fun bound => Classical.byContradiction (fun unreachable => ?_)⟩
        exact unbounded ⟨bound, fun tick => lt_of_not_ge (fun seen => unreachable ⟨tick, seen⟩)⟩
      obtain ⟨bound, trapped⟩ := bounded
      exact ⟨⟨bound, trapped⟩⟩
    · exact .inl ⟨game.counter completed plan opponent arbitrate succeeds⟩
  · intro failed live
    rcases failed with counter | ⟨_, stalled⟩
    · obtain ⟨witness⟩ := counter
      exact witness.refutes game completed plan opponent arbitrate live.1
    · obtain ⟨stall⟩ := stalled
      obtain ⟨tick, reached⟩ := live.2 stall.bound
      exact (not_lt_of_ge reached) (stall.trapped tick)

end Game

namespace Game

local notation "Cut" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → Cut → Turn

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (allowed : CivilPlan Party Good Port Technology Instrument CivilView →
    (List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument) →
    (Nat → Root.Cut Party Good Port Technology Instrument → Turn) → Prop)
  (completed : Script Party Good Port Technology Instrument → Prop)

def LiveWithin (plan : Plan) : Prop :=
  HasAllowed allowed plan ∧ ∀ opponent arbitrate, allowed plan opponent arbitrate →
    game.LiveSuccess completed plan opponent arbitrate

theorem no_live_policy_iff_each_has_no_legal_play_or_a_rooted_failure :
    (¬ ∃ plan : Plan, game.LiveWithin allowed completed plan) ↔
      ∀ plan : Plan, ¬ HasAllowed allowed plan ∨
        ∃ (opponent : Opponent) (arbitrate : Arbitration), allowed plan opponent arbitrate ∧
          (Nonempty (game.Counter completed plan opponent arbitrate) ∨
            (game.Succeeds completed plan opponent arbitrate ∧ Nonempty (game.TimeStall plan opponent arbitrate))) := by
  classical
  constructor
  · intro noPolicy plan
    by_cases existsPlay : HasAllowed allowed plan
    · right
      have fails : ∃ (opponent : Opponent) (arbitrate : Arbitration), allowed plan opponent arbitrate ∧
          ¬ game.LiveSuccess completed plan opponent arbitrate := by
        by_contra noFailure
        exact noPolicy ⟨plan, existsPlay, fun opponent arbitrate legal => Classical.byContradiction
          (fun bad => noFailure ⟨opponent, arbitrate, legal, bad⟩)⟩
      obtain ⟨opponent, arbitrate, legal, fails⟩ := fails
      exact ⟨opponent, arbitrate, legal,
        (game.a_live_play_fails_iff_first_defeat_pending_forever_or_an_original_clock_bound _ _ _ _).mp fails⟩
    · exact .inl existsPlay
  · rintro every ⟨plan, plays, safe⟩
    rcases every plan with none | ⟨opponent, arbitrate, legal, failed⟩
    · exact none plays
    · exact (game.a_live_play_fails_iff_first_defeat_pending_forever_or_an_original_clock_bound _ _ _ _).mpr
        failed (safe opponent arbitrate legal)

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
