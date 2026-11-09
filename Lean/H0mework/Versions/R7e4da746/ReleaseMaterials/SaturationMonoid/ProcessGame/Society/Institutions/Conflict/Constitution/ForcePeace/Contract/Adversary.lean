import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Defeat
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Uniform

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate Counterplay

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Plan" => CivilPlan Party Good Port (State Party Technology) Instrument CivilView
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

/-- The adversary is fixed before the civilian chooses a signed policy.
It must allow a real interleaving and break every such interleaving. -/
def OneOpponentForces : Prop :=
  ∃ opponent : Opponent, ∀ plan : Plan, (∀ seen, signedChoice game scope actor seen (plan.submit seen)) →
    (∃ schedule : Arbitration, ConstitutionalPlay game plan opponent schedule) ∧
    ∀ schedule : Arbitration, ConstitutionalPlay game plan opponent schedule →
      Nonempty (game.FirstAttack plan opponent schedule)

omit [DecidableEq Technology] in
theorem the_uniform_attacker_files_the_first_original_loss_against_every_signed_policy
    (force : OneOpponentForces game scope actor) :
    ∃ opponent : Opponent, ∀ plan : Plan, (∀ seen, signedChoice game scope actor seen (plan.submit seen)) →
      (∃ schedule : Arbitration, ConstitutionalPlay game plan opponent schedule) ∧
      ∀ schedule : Arbitration, ConstitutionalPlay game plan opponent schedule →
        ∃ first : game.FirstAttack plan opponent schedule,
        ∃ balance, ∃ row, (game.publishedAt plan opponent schedule (first.tick + 1)).next.read row =
          .inr ((game.originalAttackAt plan opponent schedule first.tick first.damage).val, balance) := by
  obtain ⟨opponent, every⟩ := force
  refine ⟨opponent, fun plan chosen => ⟨(every plan chosen).1, fun schedule lawful => ?_⟩⟩
  obtain ⟨first⟩ := (every plan chosen).2 schedule lawful
  exact ⟨first, game.the_actual_attack_is_filed_on_its_own_next_visit plan opponent schedule first.tick first.damage⟩

theorem a_uniform_attacker_implies_a_rooted_counter_to_each_signed_policy
    (base : RawLaw Party Good Port Technology Instrument) (force : OneOpponentForces game scope actor) :
    ∀ plan : Plan, (∀ seen, signedChoice game scope actor seen (plan.submit seen)) →
      DefeatedAtOriginalCut game base scope actor plan := by
  obtain ⟨opponent, every⟩ := force
  intro plan chosen
  obtain ⟨schedule, lawful⟩ := (every plan chosen).1
  obtain ⟨first⟩ := (every plan chosen).2 schedule lawful
  exact .inr (.inl ⟨⟨opponent, schedule, first.tick, lawful first.tick,
    .material (lawful (first.tick + 1) first.tick (Nat.lt_succ_self _)) (.attack first.damage)⟩⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
