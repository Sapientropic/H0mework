import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Script)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Plan" => CivilPlan Party Good Port Technology Instrument CivilView
local notation "Opponent" => List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Arbitration" => Nat → C → Turn

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (completed : Script Party Good Port Technology Instrument → Prop)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

/-- Completion is tested on a prefix that the original dispatcher has
actually consumed. Safety and independent exit are required at every tick. -/
def Succeeds : Prop := game.Safe plan opponent arbitrate ∧
  ∃ tick, completed (game.prefixAt plan opponent arbitrate tick)

def Wins : Prop := ∀ (opponent : Opponent) (arbitrate : Arbitration), game.Succeeds completed plan opponent arbitrate

structure Delay : Prop where
  safe : game.Safe plan opponent arbitrate
  pending : ∀ tick, ¬ completed (game.prefixAt plan opponent arbitrate tick)

theorem Delay.each_prefix_keeps_its_original_successor_and_the_unfulfilled_request
    (delay : game.Delay completed plan opponent arbitrate) (tick : Nat) :
    Quantities.Recorded game.seed (game.prefixAt plan opponent arbitrate (tick + 1)) ∧
      HEq (game.publishedAt plan opponent arbitrate (tick + 1)).next
        (Reparation.Actual.advance (game.publishedAt plan opponent arbitrate tick).next
          (game.inputAt plan.submit opponent arbitrate tick)) ∧
      ¬ completed (game.prefixAt plan opponent arbitrate (tick + 1)) := by
  refine ⟨(game.publishedAt plan opponent arbitrate (tick + 1)).recorded, ?_, delay.pending (tick + 1)⟩
  rw [game.the_published_prefix_is_the_original_ledger, game.the_published_prefix_is_the_original_ledger]
  exact game.every_arbitrated_tick_writes_the_original_joint_successor plan.submit opponent arbitrate tick

/-- A finite failure carries the first rejected check. A delay is one
actual endless execution whose every finite prefix remains unfulfilled. -/
inductive Counter where
  | finite (first : game.FirstDefeat plan opponent arbitrate)
  | delay (actual : game.Delay completed plan opponent arbitrate)

theorem Counter.refutes (counter : game.Counter completed plan opponent arbitrate) :
    ¬ game.Succeeds completed plan opponent arbitrate := by
  intro success
  cases counter with
  | finite first =>
    exact first.issue.refutes game plan opponent arbitrate (success.1 first.tick)
  | delay actual =>
    obtain ⟨tick, paid⟩ := success.2
    exact actual.pending tick paid

def counter (failure : ¬ game.Succeeds completed plan opponent arbitrate) :
    game.Counter completed plan opponent arbitrate := by
  classical
  by_cases safe : game.Safe plan opponent arbitrate
  · exact .delay ⟨safe, fun tick paid => failure ⟨safe, tick, paid⟩⟩
  · exact .finite (game.firstDefeat plan opponent arbitrate safe)

def PointwiseCounter : Prop :=
  ∀ plan : Plan, ∃ (opponent : Opponent) (arbitrate : Arbitration),
    Nonempty (game.Counter completed plan opponent arbitrate)

theorem no_civilian_winning_policy_iff_each_policy_has_an_original_counter :
    (¬ ∃ plan : Plan, game.Wins completed plan) ↔ game.PointwiseCounter completed := by
  classical
  constructor
  · intro noPolicy plan
    have failed : ∃ (opponent : Opponent) (arbitrate : Arbitration),
        ¬ game.Succeeds completed plan opponent arbitrate := by
      by_contra absent
      apply noPolicy
      exact ⟨plan, fun opponent arbitrate => Classical.byContradiction
        (fun unsuccessful => absent ⟨opponent, arbitrate, unsuccessful⟩)⟩
    obtain ⟨opponent, arbitrate, unsuccessful⟩ := failed
    exact ⟨opponent, arbitrate, ⟨game.counter completed plan opponent arbitrate unsuccessful⟩⟩
  · rintro counters ⟨plan, wins⟩
    obtain ⟨opponent, arbitrate, ⟨witness⟩⟩ := counters plan
    exact witness.refutes game completed plan opponent arbitrate (wins opponent arbitrate)

/-- With the arbitration fixed, the same opposing observation policy
must generate an actual breakthrough against every civilian policy. -/
def OneForcesAt : Prop :=
  ∃ opponent : Opponent, ∀ plan : Plan, Nonempty (game.FirstAttack plan opponent arbitrate)

def OneForcesEveryInterleaving : Prop :=
  ∃ opponent : Opponent, ∀ (plan : Plan) (arbitrate : Arbitration), Nonempty (game.FirstAttack plan opponent arbitrate)

theorem one_forcing_policy_gives_a_counter_for_each_civilian
    (forces : game.OneForcesAt arbitrate) : game.PointwiseCounter completed := by
  obtain ⟨opponent, all⟩ := forces
  intro plan
  obtain ⟨first⟩ := all plan
  refine ⟨opponent, arbitrate, ⟨.finite (game.firstDefeat plan opponent arbitrate ?_)⟩⟩
  intro safe
  exact (safe first.tick).1.safe first.damage

theorem an_opposing_policy_forces_iff_its_actual_breakthrough_has_a_first_occurrence :
    (∃ opponent : Opponent, ∀ plan : Plan, ∃ tick,
      Nonempty (game.DamageAt plan opponent arbitrate tick)) ↔ game.OneForcesAt arbitrate := by
  constructor
  · rintro ⟨opponent, all⟩
    exact ⟨opponent, fun plan => ⟨game.firstAttack plan opponent arbitrate (all plan)⟩⟩
  · rintro ⟨opponent, all⟩
    refine ⟨opponent, fun plan => ?_⟩
    obtain ⟨first⟩ := all plan
    exact ⟨first.tick, ⟨first.damage⟩⟩

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
