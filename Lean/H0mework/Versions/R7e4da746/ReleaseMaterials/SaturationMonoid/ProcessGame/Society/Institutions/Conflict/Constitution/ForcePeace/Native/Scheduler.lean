import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Effective
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Safety

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate
open Counterplay
open Quantities.Execution

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Plan" => CivilPlan Party Good Port (State Party Technology) Instrument CivilView

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)

abbrev submittedCut := endAt game.seed game.past
abbrev reservedRank := remainingNative (submittedCut game)

/-- Reserve the submission and the first material visit. All other
interleaving choices still go to the same original dispatcher. -/
def protectedTurn (interleave : Nat → C → Turn) (tick : Nat) (cut : C) : Turn :=
  if tick = 0 ∨ tick = reservedRank game then .civil else interleave tick cut

def committedPlan (follow : Plan) : Plan where
  submit := fun seen => if seen.length ≤ reservedRank game + 1 then
    withdrawalInput scope (submittedCut game) actor else follow.submit seen
  exit := follow.exit

variable (follow : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)
  (opponent : List OpponentView → Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)
  (interleave : Nat → Root.Cut Party Good Port (State Party Technology) Instrument → Turn)

local notation "plan" => committedPlan game scope actor follow
local notation "turn" => protectedTurn game interleave

omit [DecidableEq Technology] [DecidableEq Community] in
theorem original_prefix_lengths (tick : Nat) :
    (game.scriptAt (plan).submit opponent turn tick).length = tick ∧
    (game.play (plan).submit opponent turn tick).civilSeen.length = tick + 1 := by
  induction tick with
  | zero => exact ⟨rfl, rfl⟩
  | succ tick lengths =>
    constructor
    · rw [game.play_succ_script, List.length_append, lengths.1]
      rfl
    · change ((game.play (plan).submit opponent turn tick).civilSeen ++ [_]).length = tick + 1 + 1
      rw [List.length_append, lengths.2]
      rfl

omit [DecidableEq Technology] [DecidableEq Community] in
theorem both_original_priority_visits_use_the_literal_submitted_request (tick : Nat)
    (reserved : tick = 0 ∨ tick = reservedRank game) :
    game.inputAt (plan).submit opponent turn tick = withdrawalInput scope (submittedCut game) actor := by
  have within : tick ≤ reservedRank game := by rcases reserved with rfl | rfl <;> omega
  unfold Game.inputAt Game.turnAt
  rw [show protectedTurn game interleave tick _ = .civil from if_pos reserved]
  change (if (game.play (plan).submit opponent turn tick).civilSeen.length ≤ reservedRank game + 1 then _ else _) = _
  rw [(original_prefix_lengths game scope actor follow opponent interleave tick).2]
  exact if_pos (Nat.succ_le_succ within)

omit [DecidableEq Technology] [DecidableEq Community] in
theorem every_competing_tick_before_release_is_original_native_work (tick : Nat)
    (earlier : tick < reservedRank game) :
    inventory (game.currentAt (plan).submit opponent turn tick) [game.inputAt (plan).submit opponent turn tick] = [] := by
  have length := (original_prefix_lengths game scope actor follow opponent interleave tick).1
  have busy : Quantities.Pending (game.currentAt (plan).submit opponent turn tick) := by
    rw [game.play_is_the_original_current, endAt_append]
    apply (exactly_the_original_rank_precedes_the_first_material_visit (submittedCut game) _
      (by rw [length]; exact earlier.le)).mpr
    rw [length]
    exact earlier
  exact (a_competing_input_cannot_add_native_work_to_the_pending_visit _ _ busy).2.2.2

variable {base : RawLaw Party Good Port Technology Instrument}

def paidWithdrawalAtPriority (installed : Emergency.Installed (submittedCut game) base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor)) :
    EffectiveRelease base scope game.seed (submittedCut game) actor
      (game.prefixAt plan opponent turn (reservedRank game + 1)) := by
  let n := reservedRank game
  let wait := game.scriptAt (plan).submit opponent turn n
  have length : wait.length = n := (original_prefix_lengths game scope actor follow opponent interleave n).1
  have within : wait.length ≤ remainingNative (submittedCut game) := le_of_eq length
  have unchanged := all_native_interleavings_spend_the_same_backlog_without_material_effects
    (submittedCut game) wait within
  have ready : ¬ Quantities.Pending (endAt (submittedCut game) wait) := by
    intro busy
    have earlier := (exactly_the_original_rank_precedes_the_first_material_visit _ wait within).mp busy
    exact Nat.not_lt_of_ge length.ge earlier
  have review : ReviewAvailable (endAt (submittedCut game) wait) := by
    unfold ReviewAvailable
    rw [unchanged.2.2.1]
    exact admitted.1
  have valid : (law base scope).Valid (endAt (submittedCut game) wait).raw
      (withdrawal scope (submittedCut game) actor) := unchanged.2.1.symm ▸ admitted.2
  refine ⟨game.past ++ wait, [], ?_, ?_⟩
  · unfold Game.prefixAt
    rw [game.play_succ_script, ← List.append_assoc,
      both_original_priority_visits_use_the_literal_submitted_request game scope actor follow opponent interleave n (Or.inr rfl)]
  · rw [endAt_append]
    exact release_at_the_original_material_visit actor (installed.along wait) ready review valid

theorem the_protected_dispatch_pays_at_the_first_material_ordinal_on_the_original_clock
    (installed : Emergency.Installed (submittedCut game) base scope)
    (admitted : ReviewAvailable (submittedCut game) ∧
      (law base scope).Valid (submittedCut game).raw (withdrawal scope (submittedCut game) actor)) :
    let receipt := paidWithdrawalAtPriority game scope actor follow opponent interleave installed admitted
    receipt.ordinal = game.past.length + reservedRank game ∧
    receipt.clock = (submittedCut game).raw.clock ∧
    Quantities.Recorded game.seed (game.prefixAt plan opponent turn (reservedRank game + 1)) ∧
    HEq (game.ledger (plan).submit opponent turn (reservedRank game + 1))
      (Reparation.Actual.advance (game.ledger (plan).submit opponent turn (reservedRank game))
        (withdrawalInput scope (submittedCut game) actor)) := by
  let n := reservedRank game
  have length := (original_prefix_lengths game scope actor follow opponent interleave n).1
  refine ⟨?_, ?_, game.every_interleaving_prefix_is_recorded (plan).submit opponent turn _, ?_⟩
  · change (game.past ++ game.scriptAt (plan).submit opponent turn n).length = game.past.length + n
    rw [List.length_append, length]
  · change (endAt game.seed (game.past ++ game.scriptAt (plan).submit opponent turn n)).raw.clock =
      (submittedCut game).raw.clock
    rw [endAt_append]
    exact congrArg (·.clock)
      (all_native_interleavings_spend_the_same_backlog_without_material_effects _ _ length.le).2.1
  · rw [← both_original_priority_visits_use_the_literal_submitted_request game scope actor follow opponent
      interleave n (Or.inr rfl)]
    exact game.every_arbitrated_tick_writes_the_original_joint_successor (plan).submit opponent turn n

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
