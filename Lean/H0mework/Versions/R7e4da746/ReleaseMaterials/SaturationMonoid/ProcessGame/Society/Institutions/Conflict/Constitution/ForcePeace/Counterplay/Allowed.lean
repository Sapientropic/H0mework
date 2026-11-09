import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Quantifiers

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
  (allowed : CivilPlan Party Good Port Technology Instrument CivilView →
    (List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument) →
    (Nat → Root.Cut Party Good Port Technology Instrument → Turn) → Prop)
  (completed : Script Party Good Port Technology Instrument → Prop)

def HasAllowed (plan : Plan) : Prop :=
  ∃ (opponent : Opponent) (arbitrate : Arbitration), allowed plan opponent arbitrate

def WinsWithin (plan : Plan) : Prop := HasAllowed allowed plan ∧
  ∀ opponent arbitrate, allowed plan opponent arbitrate → game.Succeeds completed plan opponent arbitrate

def CounterWithin (plan : Plan) : Prop :=
  ∃ (opponent : Opponent) (arbitrate : Arbitration),
    allowed plan opponent arbitrate ∧ Nonempty (game.Counter completed plan opponent arbitrate)

/-- A policy without a permitted run cannot count as winning. A failed
policy with a permitted run has a finite first defeat or an actual delay. -/
theorem no_winning_policy_iff_each_has_no_allowed_play_or_an_actual_counter :
    (¬ ∃ plan : Plan, game.WinsWithin allowed completed plan) ↔
      ∀ plan : Plan, ¬ HasAllowed allowed plan ∨ game.CounterWithin allowed completed plan := by
  classical
  constructor
  · intro noWinner plan
    by_cases available : HasAllowed allowed plan
    · right
      have failure : ∃ (opponent : Opponent) (arbitrate : Arbitration),
          allowed plan opponent arbitrate ∧ ¬ game.Succeeds completed plan opponent arbitrate := by
        by_contra absent
        apply noWinner
        refine ⟨plan, available, fun opponent arbitrate admitted => ?_⟩
        exact Classical.byContradiction (fun unsuccessful => absent ⟨opponent, arbitrate, admitted, unsuccessful⟩)
      obtain ⟨opponent, arbitrate, admitted, failed⟩ := failure
      exact ⟨opponent, arbitrate, admitted, ⟨game.counter completed plan opponent arbitrate failed⟩⟩
    · exact .inl available
  · rintro counters ⟨plan, wins⟩
    rcases counters plan with unavailable | ⟨opponent, arbitrate, admitted, ⟨witness⟩⟩
    · exact unavailable wins.1
    · exact witness.refutes game completed plan opponent arbitrate (wins.2 opponent arbitrate admitted)

theorem when_scheduling_is_available_no_winner_iff_each_has_an_allowed_actual_counter
    (available : ∀ plan : Plan, HasAllowed allowed plan) :
    (¬ ∃ plan : Plan, game.WinsWithin allowed completed plan) ↔
      ∀ plan : Plan, game.CounterWithin allowed completed plan := by
  rw [game.no_winning_policy_iff_each_has_no_allowed_play_or_an_actual_counter allowed completed]
  constructor
  · intro branch plan
    exact (branch plan).resolve_left (fun absent => absent (available plan))
  · exact fun counters plan => .inr (counters plan)

/-- A single attacker must have a permitted execution against each
civilian and cause actual damage in every permitted execution. -/
def OneForcesWithin : Prop :=
  ∃ opponent : Opponent,
    (∀ plan : Plan, ∃ arbitrate : Arbitration, allowed plan opponent arbitrate) ∧
      ∀ (plan : Plan) (arbitrate : Arbitration), allowed plan opponent arbitrate →
        Nonempty (game.FirstAttack plan opponent arbitrate)

theorem one_allowed_forcing_attacker_gives_a_counter_for_every_civilian
    (forces : game.OneForcesWithin allowed) :
    ∀ plan : Plan, game.CounterWithin allowed completed plan := by
  obtain ⟨opponent, available, attack⟩ := forces
  intro plan
  obtain ⟨arbitrate, admitted⟩ := available plan
  obtain ⟨first⟩ := attack plan arbitrate admitted
  refine ⟨opponent, arbitrate, admitted, ⟨.finite (game.firstDefeat plan opponent arbitrate ?_)⟩⟩
  intro safe
  exact (safe first.tick).1.safe first.damage

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
