import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Safety
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Failure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (OriginalAttack Script)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

local notation "Word" => Script Party Good Port Technology Instrument

namespace Game

variable (game : Game Party Good Port Technology Instrument Community CivilView OpponentView)
  (plan : CivilPlan Party Good Port Technology Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn)

abbrev DamageAt (tick : Nat) :=
  Boundary.Actual.DamageAt (game.currentAt plan.submit opponent arbitrate tick)
    (game.inputAt plan.submit opponent arbitrate tick) game.community

omit [DecidableEq Community] in
theorem prefixAt_succ (tick : Nat) :
    game.prefixAt plan opponent arbitrate (tick + 1) =
      game.prefixAt plan opponent arbitrate tick ++ [game.inputAt plan.submit opponent arbitrate tick] :=
  (congrArg (game.past ++ ·) (game.play_succ_script plan.submit opponent arbitrate tick)).trans
    (List.append_assoc _ _ _).symm

omit [DecidableEq Community] in
theorem earlier_is_a_prefix {before after : Nat} (ordered : before ≤ after) :
    ∃ later : Word, game.prefixAt plan opponent arbitrate after =
      game.prefixAt plan opponent arbitrate before ++ later := by
  induction ordered with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | @step n _ previous =>
    obtain ⟨later, split⟩ := previous
    refine ⟨later ++ [game.inputAt plan.submit opponent arbitrate n], ?_⟩
    rw [game.prefixAt_succ plan opponent arbitrate n, split, List.append_assoc]

abbrev publishedAt (tick : Nat) : Reparation.Actual.Published game.seed game.community
    (game.prefixAt plan opponent arbitrate tick) :=
  Reparation.Actual.publishAfter (Reparation.Actual.run game.seed game.community game.past)
    (game.scriptAt plan.submit opponent arbitrate tick)

theorem the_published_prefix_is_the_original_ledger (tick : Nat) :
    (game.publishedAt plan opponent arbitrate tick).next = game.ledger plan.submit opponent arbitrate tick :=
  Reparation.Actual.publication_consumes_the_retained_visit game.seed game.community game.past _

theorem every_earlier_victim_keeps_their_actual_row {before after : Nat} (ordered : before ≤ after)
    (origin : Reparation.Actual.Occurrence game.seed game.community)
    (listed : origin ∈ Reparation.Actual.originalLosses game.seed game.community
      (game.prefixAt plan opponent arbitrate before)) :
    ∃ balance, ∃ row, (game.publishedAt plan opponent arbitrate after).next.read row = .inr (origin, balance) := by
  obtain ⟨later, split⟩ := game.earlier_is_a_prefix plan opponent arbitrate ordered
  rw [game.the_published_prefix_is_the_original_ledger]
  change ∃ balance, ∃ row, (Reparation.Actual.run game.seed game.community
    (game.prefixAt plan opponent arbitrate after)).read row = .inr (origin, balance)
  rw [split]
  exact Reparation.Actual.every_actual_loss_has_its_own_row_on_every_later_current
    game.seed game.community _ later origin listed

def originalAttackAt (tick : Nat) (damage : game.DamageAt plan opponent arbitrate tick) :
    OriginalAttack game.seed game.community (game.prefixAt plan opponent arbitrate (tick + 1)) :=
  ⟨⟨game.prefixAt plan opponent arbitrate tick, game.inputAt plan.submit opponent arbitrate tick,
      (game.play_is_the_original_current plan.submit opponent arbitrate tick) ▸ damage⟩,
    game.prefixAt_succ plan opponent arbitrate tick⟩

theorem the_actual_attack_is_filed_on_its_own_next_visit (tick : Nat)
    (damage : game.DamageAt plan opponent arbitrate tick) :
    ∃ balance, ∃ row, (game.publishedAt plan opponent arbitrate (tick + 1)).next.read row =
      .inr ((game.originalAttackAt plan opponent arbitrate tick damage).val, balance) :=
  Peace.an_original_breakthrough_is_written_at_its_first_failed_prefix
    (game.originalAttackAt plan opponent arbitrate tick damage)

structure FirstAttack where
  tick : Nat
  earlier : ∀ n < tick, ¬ Nonempty (game.DamageAt plan opponent arbitrate n)
  damage : game.DamageAt plan opponent arbitrate tick
  firstItem : (Boundary.Actual.damages (game.currentAt plan.submit opponent arbitrate tick)
    (game.inputAt plan.submit opponent arbitrate tick) game.community).head? = some damage

def firstAttack (occurs : ∃ n, Nonempty (game.DamageAt plan opponent arbitrate n)) :
    game.FirstAttack plan opponent arbitrate := by
  classical
  let tick := Nat.find occurs
  cases listed : Boundary.Actual.damages (game.currentAt plan.submit opponent arbitrate tick)
    (game.inputAt plan.submit opponent arbitrate tick) game.community with
  | nil =>
    have impossible : False := by
      obtain ⟨damage⟩ := Nat.find_spec occurs
      exact List.not_mem_nil (listed ▸ Boundary.Actual.every_actual_debit_is_assessed damage)
    exact impossible.elim
  | cons first rest =>
    refine ⟨tick, fun _ before => Nat.find_min occurs before, first, ?_⟩
    rw [listed]
    rfl

def FirstDefeat.writeTick (failed : game.FirstDefeat plan opponent arbitrate) : Nat :=
  match failed.issue with
  | .actual _ => failed.tick + 1
  | .exit .. => failed.tick

abbrev FirstDefeat.publish (failed : game.FirstDefeat plan opponent arbitrate) :=
  game.publishedAt plan opponent arbitrate (failed.writeTick game plan opponent arbitrate)

theorem FirstDefeat.an_actual_damage_is_on_the_failed_successor (failed : game.FirstDefeat plan opponent arbitrate)
    (damage : game.DamageAt plan opponent arbitrate failed.tick)
    (issue : failed.issue = .actual (.attack damage)) :
    ∃ balance, ∃ row, (failed.publish game plan opponent arbitrate).next.read row =
      .inr ((game.originalAttackAt plan opponent arbitrate failed.tick damage).val, balance) := by
  have index : failed.writeTick game plan opponent arbitrate = failed.tick + 1 :=
    congrArg (fun reason : game.Issue plan opponent arbitrate failed.tick =>
      match reason with
      | .actual _ => failed.tick + 1
      | .exit .. => failed.tick) issue
  change ∃ balance, ∃ row,
    (game.publishedAt plan opponent arbitrate (failed.writeTick game plan opponent arbitrate)).next.read row = _
  rw [index]
  exact game.the_actual_attack_is_filed_on_its_own_next_visit plan opponent arbitrate failed.tick damage

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
