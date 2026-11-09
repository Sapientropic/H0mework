import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Allowed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Effective

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Script)
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Word" => Script Party Good Port (State Party Technology) Instrument
local notation "Plan" => CivilPlan Party Good Port (State Party Technology) Instrument CivilView

namespace Game

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

/-- A withdrawal is effective only when its exact signed request has a
material receipt at or after the actual submission cut. -/
def WithdrawalComplete (word : Word) : Prop :=
  ∃ receipt : EffectiveRelease base scope game.seed (endAt game.seed game.past) actor word,
    game.past.length ≤ receipt.ordinal

theorem a_receipt_from_before_submission_cannot_complete_this_withdrawal :
    ¬ game.WithdrawalComplete base scope actor game.past := by
  rintro ⟨receipt, afterSubmission⟩
  have position := congrArg List.length receipt.original
  simp only [List.length_append, List.length_cons] at position
  change game.past.length ≤ receipt.before.length at afterSubmission
  omega

theorem effective_withdrawal_is_retained_by_every_original_extension (word tail : Word)
    (paid : game.WithdrawalComplete base scope actor word) :
    game.WithdrawalComplete base scope actor (word ++ tail) := by
  obtain ⟨receipt, afterSubmission⟩ := paid
  exact ⟨receipt.extend tail, afterSubmission⟩

variable [DecidableEq Community]

theorem no_civilian_can_force_the_submitted_withdrawal_iff_each_policy_has_an_actual_counter :
    (¬ ∃ plan : Plan, game.Wins (game.WithdrawalComplete base scope actor) plan) ↔
      game.PointwiseCounter (game.WithdrawalComplete base scope actor) :=
  game.no_civilian_winning_policy_iff_each_policy_has_an_original_counter (game.WithdrawalComplete base scope actor)

theorem no_civilian_forces_the_withdrawal_on_allowed_plays_iff_each_has_an_allowed_actual_counter
    (allowed : Plan → (List OpponentView → Reparation.Actual.Input Party Good Port (State Party Technology) Instrument) →
      (Nat → C → Turn) → Prop) (available : ∀ plan : Plan, HasAllowed allowed plan) :
    (¬ ∃ plan : Plan, game.WinsWithin allowed (game.WithdrawalComplete base scope actor) plan) ↔
      ∀ plan : Plan, game.CounterWithin allowed (game.WithdrawalComplete base scope actor) plan :=
  game.when_scheduling_is_available_no_winner_iff_each_has_an_allowed_actual_counter
    allowed (game.WithdrawalComplete base scope actor) available

end Game

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay
