import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Timing.Joint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (RoundFailure StepFailure Window)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {CivilView : Type u} {OpponentView : Type v}

namespace Game

variable {game : Game Party Good Port Technology Instrument Community CivilView OpponentView}
  {allowed : Position Party Good Port Technology Instrument CivilView OpponentView →
    Turn → Reparation.Actual.Input Party Good Port Technology Instrument → Prop}
  {plan : CivilPlan Party Good Port Technology Instrument CivilView}
  {opponent : List OpponentView → Reparation.Actual.Input Party Good Port Technology Instrument}
  {arbitrate : Nat → Root.Cut Party Good Port Technology Instrument → Turn} {tick : Nat}

def JointIssue.writeTick : game.JointIssue allowed plan opponent arbitrate tick → Nat
  | .material .. => tick + 1
  | .exit _ => tick

variable (breach : game.JointBreach allowed plan)

abbrev JointBreach.writeTick := breach.issue.writeTick

abbrev JointBreach.publish := game.publishedAt plan breach.opponent breach.arbitrate breach.writeTick

theorem JointBreach.the_written_successor_keeps_the_exact_original_ledger :
    let history := game.prefixAt plan breach.opponent breach.arbitrate breach.writeTick
    Quantities.Recorded game.seed history ∧
      breach.publish.next = Reparation.Actual.run game.seed game.community history ∧
      ∀ victim ∈ Reparation.Actual.originalLosses game.seed game.community
        (game.prefixAt plan breach.opponent breach.arbitrate breach.tick),
        ∃ balance, ∃ row, breach.publish.next.read row = .inr (victim, balance) := by
  have before : breach.tick ≤ breach.writeTick := by
    rcases breach with ⟨opponent, arbitrate, tick, prior, issue⟩
    cases issue with
    | material => exact Nat.le_succ _
    | exit => exact le_rfl
  exact ⟨breach.publish.recorded, game.the_published_prefix_is_the_original_ledger _ _ _ _,
    game.every_earlier_victim_keeps_their_actual_row _ _ _ before⟩

/-- An exit failure retains the unexecuted exit word and writes exactly the
actual prefix before any hypothetical action on that exit. -/
theorem JointBreach.exit_failure_writes_only_the_original_cut
    (failure : RoundFailure game.seed game.command game.community
      (Window.at (game.currentAt plan.submit breach.opponent breach.arbitrate breach.tick))
      (game.exitAt plan breach.opponent breach.arbitrate breach.tick) [])
    (selected : breach.issue = .exit failure) :
    breach.writeTick = breach.tick ∧
      HEq breach.publish (game.publishedAt plan breach.opponent breach.arbitrate breach.tick) := by
  have atCut : breach.writeTick = breach.tick :=
    congrArg (fun reason : game.JointIssue allowed plan breach.opponent breach.arbitrate breach.tick =>
      reason.writeTick) selected
  refine ⟨atCut, ?_⟩
  change HEq (game.publishedAt plan breach.opponent breach.arbitrate breach.writeTick) _
  rw [atCut]

theorem JointBreach.material_failure_writes_the_original_next_visit
    (permit : game.VisitAllowed allowed plan breach.opponent breach.arbitrate breach.tick)
    (failure : StepFailure game.seed game.command game.community
      (game.turnAt plan.submit breach.opponent breach.arbitrate breach.tick).isCivil
      (game.play plan.submit breach.opponent breach.arbitrate breach.tick).window
      (game.inputAt plan.submit breach.opponent breach.arbitrate breach.tick))
    (selected : breach.issue = .material permit failure) :
    breach.writeTick = breach.tick + 1 ∧
      HEq breach.publish.next (Reparation.Actual.advance
        (game.publishedAt plan breach.opponent breach.arbitrate breach.tick).next
        (game.inputAt plan.submit breach.opponent breach.arbitrate breach.tick)) := by
  have atVisit : breach.writeTick = breach.tick + 1 :=
    congrArg (fun reason : game.JointIssue allowed plan breach.opponent breach.arbitrate breach.tick =>
      reason.writeTick) selected
  refine ⟨atVisit, ?_⟩
  change HEq (game.publishedAt plan breach.opponent breach.arbitrate breach.writeTick).next _
  rw [atVisit, game.the_published_prefix_is_the_original_ledger, game.the_published_prefix_is_the_original_ledger]
  exact game.every_arbitrated_tick_writes_the_original_joint_successor plan.submit breach.opponent breach.arbitrate breach.tick

theorem JointBreach.material_attack_files_its_original_victim
    (permit : game.VisitAllowed allowed plan breach.opponent breach.arbitrate breach.tick)
    (damage : game.DamageAt plan breach.opponent breach.arbitrate breach.tick)
    (selected : breach.issue = .material permit (.attack damage)) :
    ∃ balance, ∃ row, breach.publish.next.read row =
      .inr ((game.originalAttackAt plan breach.opponent breach.arbitrate breach.tick damage).val, balance) := by
  have atVisit := (breach.material_failure_writes_the_original_next_visit permit (.attack damage) selected).1
  change ∃ balance, ∃ row,
    (game.publishedAt plan breach.opponent breach.arbitrate breach.writeTick).next.read row = _
  rw [atVisit]
  exact game.the_actual_attack_is_filed_on_its_own_next_visit plan breach.opponent breach.arbitrate breach.tick damage

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
