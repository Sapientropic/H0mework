import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Contract.Timing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Time
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre.DeadEnd

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
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)
  (plan : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)

local notation "legal" => SignedConstitutionalPlay game scope actor
local notation "paid" => game.WithdrawalComplete base scope actor
local notation "move" => constitutionalMove game

/-- Every finite legal cut must stay safe, including a cut with no legal
extension. At least one infinite legal interleaving must actually exist. -/
def ForcesAtEveryOriginalCut : Prop :=
  Game.HasAllowed legal plan ∧ game.PreservesAllowedPrefixes move plan ∧
    ∀ (rival : Opponent) (schedule : Arbitration), legal plan rival schedule →
      ∃ tick, paid (game.prefixAt plan rival schedule tick)

def DefeatedAtOriginalCut : Prop :=
  (¬ Game.HasAllowed legal plan ∧ Nonempty (game.AllowedDeadEnd move plan)) ∨
    Nonempty (game.JointBreach move plan) ∨
    ∃ (rival : Opponent) (schedule : Arbitration), legal plan rival schedule ∧
      game.Delay paid plan rival schedule

omit [DecidableEq Technology] in
theorem an_empty_original_menu_names_the_denied_civilian_item_and_keeps_its_cut
    (dead : game.AllowedDeadEnd move plan) :
    let current := game.play plan.submit dead.opponent dead.arbitrate dead.tick
    let input := plan.submit current.civilSeen
    Nonempty (Renewal.Violation current.window.current input) ∧
      Quantities.Recorded game.seed (game.prefixAt plan dead.opponent dead.arbitrate dead.tick) := by
  let current := game.play plan.submit dead.opponent dead.arbitrate dead.tick
  let input := plan.submit current.civilSeen
  refine ⟨?_, (dead.publish game).recorded⟩
  cases Renewal.inspectAdmission current.window.current input with
  | approved checked =>
    exact (dead.unavailable .civil none ⟨fun _ => rfl, checked⟩).elim
  | refused denied => exact ⟨denied⟩

theorem a_committed_plan_fails_at_the_root_iff_blocked_finite_breach_or_actual_pending_forever
    (signed : ∀ seen, signedChoice game scope actor seen (plan.submit seen)) :
    ¬ ForcesAtEveryOriginalCut game base scope actor plan ↔
      DefeatedAtOriginalCut game base scope actor plan := by
  classical
  constructor
  · intro fails
    by_cases possible : Game.HasAllowed legal plan
    · right
      by_cases preserves : game.PreservesAllowedPrefixes move plan
      · right
        have denied : ∃ (rival : Opponent) (schedule : Arbitration), legal plan rival schedule ∧
            ∀ tick, ¬ paid (game.prefixAt plan rival schedule tick) := by
          by_contra none
          apply fails
          refine ⟨possible, preserves, fun rival schedule admitted => Classical.byContradiction (fun unpaid => ?_)⟩
          exact none ⟨rival, schedule, admitted, fun tick success => unpaid ⟨tick, success⟩⟩
        obtain ⟨rival, schedule, admitted, pending⟩ := denied
        exact ⟨rival, schedule, admitted,
          (game.allowed_play_has_life_exit_and_the_original_next_ledger move plan preserves rival schedule admitted.2).1, pending⟩
      · left
        by_contra noBreach
        apply preserves
        refine (game.preserving_allowed_prefixes_iff_every_finite_joint_boundary_is_safe move plan).mpr (fun limit => ?_)
        exact (game.joint_safety_before_iff_no_earlier_original_breach move plan limit).mpr
          (fun breach => (noBreach ⟨breach⟩).elim)
    · have noReplay : ¬ Nonempty (game.AllowedReplay move plan) := by
        rintro ⟨replay⟩
        exact possible ⟨replay.opponent, replay.arbitrate, signed, replay.legal⟩
      exact .inl ⟨possible, ⟨game.deadEndOfNoAllowedReplay move plan noReplay⟩⟩
  · intro denied wins
    rcases denied with noPlay | breach | ⟨rival, schedule, admitted, delay⟩
    · exact noPlay.1 wins.1
    · obtain ⟨breach⟩ := breach
      have all := (game.preserving_allowed_prefixes_iff_every_finite_joint_boundary_is_safe move plan).mp wins.2.1
      have impossible := (game.joint_safety_before_iff_no_earlier_original_breach move plan _).mp
        (all (breach.tick + 1)) breach
      exact Nat.not_succ_le_self _ impossible
    · obtain ⟨tick, reached⟩ := wins.2.2 rival schedule admitted
      exact delay.pending tick reached

theorem no_civilian_strategy_forces_peace_iff_each_signed_policy_has_an_original_obstruction :
    (¬ ∃ policy : CivilPlan Party Good Port (State Party Technology) Instrument CivilView,
      ForcesAtEveryOriginalCut game base scope actor policy) ↔
    ∀ policy : CivilPlan Party Good Port (State Party Technology) Instrument CivilView,
      (∀ seen, signedChoice game scope actor seen (policy.submit seen)) →
        DefeatedAtOriginalCut game base scope actor policy := by
  constructor
  · intro noPolicy policy signed
    exact (a_committed_plan_fails_at_the_root_iff_blocked_finite_breach_or_actual_pending_forever
      game base scope actor policy signed).mp (fun wins => noPolicy ⟨policy, wins⟩)
  · rintro each ⟨policy, wins⟩
    obtain ⟨_, _, signed, _⟩ := wins.1
    exact (a_committed_plan_fails_at_the_root_iff_blocked_finite_breach_or_actual_pending_forever
      game base scope actor policy signed).mpr (each policy signed) wins

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
