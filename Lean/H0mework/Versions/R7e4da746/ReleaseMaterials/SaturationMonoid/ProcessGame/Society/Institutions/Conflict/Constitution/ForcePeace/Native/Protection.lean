import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Scheduler
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Withdrawal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Allowed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.ExitWrite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
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

def HonorsPriority (plan : Plan) (opponent : Opponent) (arbitrate : Arbitration) : Prop :=
  ∀ tick, tick = 0 ∨ tick = reservedRank game → game.turnAt (plan).submit opponent arbitrate tick = .civil

/-- Only actual material writes after the submitted cut are checked here.
The original whole ledger continues to carry every earlier refusal. -/
def LawfulPriority (plan : Plan) (opponent : Opponent) (arbitrate : Arbitration) : Prop :=
  HonorsPriority game plan opponent arbitrate ∧
    ∀ tick, Reparation.Actual.SourceAuthority (submittedCut game)
      (game.scriptAt (plan).submit opponent arbitrate tick)

variable (follow : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port (State Party Technology) Instrument → Turn)

local notation "plan" => committedPlan game scope actor follow

omit [DecidableEq Technology] [DecidableEq Community] in
theorem a_schedule_honoring_the_priority_replays_the_same_original_path
    (honored : HonorsPriority game plan opponent arbitrate) (tick : Nat) :
    game.play (plan).submit opponent arbitrate tick =
      game.play (plan).submit opponent (protectedTurn game arbitrate) tick := by
  induction tick with
  | zero => rfl
  | succ tick same =>
    let prior := game.play (plan).submit opponent arbitrate tick
    change game.extend prior (Game.proposal prior (plan).submit opponent (arbitrate tick prior.window.current)) =
      game.extend (game.play (plan).submit opponent (protectedTurn game arbitrate) tick) _
    rw [← same]
    unfold protectedTurn
    split
    · rename_i due
      exact congrArg (game.extend prior) (congrArg (Game.proposal prior (plan).submit opponent) (honored tick due))
    · rfl

variable {base : RawLaw Party Good Port Technology Instrument}

theorem the_submitted_release_is_paid_at_the_first_material_visit_in_every_priority_interleaving
    (installed : Emergency.Installed (submittedCut game) base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor))
    (honored : HonorsPriority game plan opponent arbitrate) :
    game.WithdrawalComplete base scope actor (game.prefixAt plan opponent arbitrate (reservedRank game + 1)) ∧
    ∀ earlier ≤ reservedRank game, ¬ game.WithdrawalComplete base scope actor
      (game.prefixAt plan opponent arbitrate earlier) := by
  constructor
  · unfold Game.prefixAt Game.scriptAt
    rw [a_schedule_honoring_the_priority_replays_the_same_original_path game scope actor follow opponent arbitrate
      honored (reservedRank game + 1)]
    let receipt := paidWithdrawalAtPriority game scope actor follow opponent arbitrate installed admitted
    have exactOrdinal := (the_protected_dispatch_pays_at_the_first_material_ordinal_on_the_original_clock
      game scope actor follow opponent arbitrate installed admitted).1
    exact ⟨receipt, by rw [exactOrdinal]; exact Nat.le_add_right _ _⟩
  · intro earlier within ⟨receipt, afterSubmission⟩
    have exactLength : (game.scriptAt (plan).submit opponent arbitrate earlier).length = earlier := by
      unfold Game.scriptAt
      rw [a_schedule_honoring_the_priority_replays_the_same_original_path game scope actor follow opponent arbitrate
        honored earlier]
      exact (original_prefix_lengths game scope actor follow opponent arbitrate earlier).1
    have tooEarly := a_native_only_prefix_cannot_complete_a_post_submission_withdrawal scope game.seed game.past actor
      (game.scriptAt (plan).submit opponent arbitrate earlier) (by rw [exactLength]; exact within) receipt
    exact (not_lt_of_ge afterSubmission) tooEarly

theorem an_admitted_committed_policy_wins_iff_every_lawful_priority_interleaving_keeps_life_and_exit
    (installed : Emergency.Installed (submittedCut game) base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor)) :
    game.WinsWithin (LawfulPriority game) (game.WithdrawalComplete base scope actor) plan ↔
    Game.HasAllowed (LawfulPriority game) plan ∧
      ∀ (rival : Opponent) (scheduler : Arbitration), LawfulPriority game plan rival scheduler →
        game.Safe plan rival scheduler := by
  constructor
  · intro wins
    exact ⟨wins.1, fun rival scheduler valid => (wins.2 rival scheduler valid).1⟩
  · rintro ⟨existsPlay, safe⟩
    refine ⟨existsPlay, fun rival scheduler valid => ⟨safe rival scheduler valid, ?_⟩⟩
    exact ⟨reservedRank game + 1, (the_submitted_release_is_paid_at_the_first_material_visit_in_every_priority_interleaving
      game scope actor follow rival scheduler installed admitted valid.1).1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
