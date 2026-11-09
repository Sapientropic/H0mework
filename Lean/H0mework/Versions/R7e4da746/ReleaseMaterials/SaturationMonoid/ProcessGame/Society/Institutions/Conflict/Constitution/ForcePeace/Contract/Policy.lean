import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Protection
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Fibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate Counterplay
open Quantities.Execution (endAt endAt_append)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Pos" => Position Party Good Port (State Party Technology) Instrument CivilView OpponentView
local notation "Plan" => CivilPlan Party Good Port (State Party Technology) Instrument CivilView
local notation "Opponent" => List OpponentView → Input
local notation "Arbitration" => Nat → C → Turn

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

def signedChoice (seen : List CivilView) (input : Input) : Prop :=
  seen.length ≤ reservedRank game + 1 → input = withdrawalInput scope (submittedCut game) actor

def constitutionalMove (position : Pos) (lane : Turn) (input : Input) : Prop :=
  ((position.script.length = 0 ∨ position.script.length = reservedRank game) → lane = .civil) ∧
  Renewal.AdmittedHistory position.window.current [input]

def ConstitutionalPlay (plan : Plan) (opponent : Opponent) (arbitrate : Arbitration) : Prop :=
  ∀ tick, game.AllowsBefore (constitutionalMove game) plan opponent arbitrate tick

def SignedConstitutionalPlay (plan : Plan) (opponent : Opponent) (arbitrate : Arbitration) : Prop :=
  (∀ seen, signedChoice game scope actor seen (plan.submit seen)) ∧ ConstitutionalPlay game plan opponent arbitrate

omit [DecidableEq Technology] [DecidableEq Community] in
theorem a_signed_choice_is_already_the_committed_policy (plan : Plan)
    (chosen : ∀ seen, signedChoice game scope actor seen (plan.submit seen)) :
    committedPlan game scope actor plan = plan := by
  cases plan with
  | mk submit exit =>
    have exactly : (committedPlan game scope actor ⟨submit, exit⟩).submit = submit := by
      funext seen
      by_cases due : seen.length ≤ reservedRank game + 1
      · exact (if_pos due).trans (chosen seen due).symm
      · exact if_neg due
    exact congrArg (fun submit => CivilPlan.mk submit exit) exactly

variable (plan : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)
  (arbitrate : Nat → Root.Cut Party Good Port (State Party Technology) Instrument → Turn)

omit [DecidableEq Technology] [DecidableEq Community] in
theorem constitutional_play_honors_the_original_priority
    (allowed : ConstitutionalPlay game plan opponent arbitrate) :
    HonorsPriority game plan opponent arbitrate := by
  have length (tick : Nat) : (game.scriptAt plan.submit opponent arbitrate tick).length = tick := by
    induction tick with
    | zero => rfl
    | succ tick earlier =>
      rw [game.play_succ_script, List.length_append, earlier]
      rfl
  intro tick due
  exact (allowed (tick + 1) tick (Nat.lt_succ_self tick)).1 (by rw [length]; exact due)

omit [DecidableEq Technology] [DecidableEq Community] in
theorem constitutional_play_has_original_admission_at_every_prefix
    (allowed : ConstitutionalPlay game plan opponent arbitrate) (tick : Nat) :
    Renewal.AdmittedHistory (submittedCut game) (game.scriptAt plan.submit opponent arbitrate tick) := by
  induction tick with
  | zero => simp [Game.scriptAt, Game.play, Game.start, Renewal.AdmittedHistory, Quantities.Execution.inventory]
  | succ tick earlier =>
    have current := game.play_is_the_original_current plan.submit opponent arbitrate tick
    rw [endAt_append] at current
    have step := (allowed (tick + 1) tick (Nat.lt_succ_self tick)).2
    change Renewal.AdmittedHistory (game.currentAt plan.submit opponent arbitrate tick)
      [game.inputAt plan.submit opponent arbitrate tick] at step
    rw [current] at step
    rw [game.play_succ_script]
    exact earlier.append step

variable {base : RawLaw Party Good Port Technology Instrument}

theorem an_admitted_constitutional_policy_keeps_its_exact_payment_and_life_at_every_cut
    (installed : Emergency.Installed (submittedCut game) base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor))
    (chosen : ∀ seen, signedChoice game scope actor seen (plan.submit seen))
    (protects : game.PreservesAllowedPrefixes (constitutionalMove game) plan)
    (allowed : ConstitutionalPlay game plan opponent arbitrate) :
    game.Safe plan opponent arbitrate ∧
    game.WithdrawalComplete base scope actor (game.prefixAt plan opponent arbitrate (reservedRank game + 1)) ∧
    (∀ earlier ≤ reservedRank game, ¬ game.WithdrawalComplete base scope actor
      (game.prefixAt plan opponent arbitrate earlier)) ∧
    ∀ tick, HEq (game.ledger plan.submit opponent arbitrate (tick + 1))
      (Reparation.Actual.advance (game.ledger plan.submit opponent arbitrate tick)
        (game.inputAt plan.submit opponent arbitrate tick)) := by
  have exactPriority := constitutional_play_honors_the_original_priority game plan opponent arbitrate allowed
  have literal := a_signed_choice_is_already_the_committed_policy game scope actor plan chosen
  rw [← literal] at exactPriority
  have exactFinish := the_submitted_release_is_paid_at_the_first_material_visit_in_every_priority_interleaving
    game scope actor plan opponent arbitrate installed admitted exactPriority
  rw [literal] at exactFinish
  have safe := game.allowed_play_has_life_exit_and_the_original_next_ledger
    (constitutionalMove game) plan protects opponent arbitrate allowed
  exact ⟨safe.1, exactFinish.1, exactFinish.2, safe.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
