import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Stall
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Scheduler
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Withdrawal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Counterplay.Time

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate Counterplay
open Quantities.Execution

noncomputable section

universe u v

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]
  {CivilView : Type u} {OpponentView : Type v}

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument

def unprotectedSchedule (tick : Nat) (_ : C) : Turn :=
  if tick = 0 then .civil else .opponent

def stopOpponent (_ : List OpponentView) : Input := some Compile.RawInput.stopReview

variable (game : Game Party Good Port (State Party Technology) Instrument Community CivilView OpponentView)
  {base : RawLaw Party Good Port Technology Instrument}
  (scope : Scope (Party := Party) (Good := Good) (Port := Port)) (actor : Party)
  (follow : CivilPlan Party Good Port (State Party Technology) Instrument CivilView)

local notation "policy" => committedPlan game scope actor follow
local notation "later" => game.currentAt (CivilPlan.submit policy) stopOpponent unprotectedSchedule
local notation "received" => game.inputAt (CivilPlan.submit policy) stopOpponent unprotectedSchedule
local notation "tape" => game.scriptAt (CivilPlan.submit policy) stopOpponent unprotectedSchedule

omit [DecidableEq Technology] [DecidableEq Community] in
/-- Outside the priority rule, the actual first visit can lodge a request
while busy, and later stops can keep that original request unpaid. -/
private theorem the_original_stop_trajectory
    (busy : Quantities.Pending (submittedCut game)) (review : ReviewAvailable (submittedCut game)) (tick : Nat) :
    (later tick).raw = (submittedCut game).raw ∧ (later tick).control = (submittedCut game).control ∧
      inventory (submittedCut game) (tape tick) = [] := by
  have advanceAt (n : Nat) : later (n + 1) = next (later n) (received n) :=
    Civil.Persistence.Window.write_current _ _
  induction tick with
  | zero =>
    have original : later 0 = submittedCut game := by
      rw [game.play_is_the_original_current]
      change endAt game.seed (game.past ++ []) = submittedCut game
      rw [List.append_nil]
    exact ⟨congrArg (·.raw) original, congrArg (·.control) original, rfl⟩
  | succ tick retained =>
    have paidNoMaterial : (next (later tick) (received tick)).raw = (later tick).raw ∧
        (next (later tick) (received tick)).control = (later tick).control ∧
        inventory (later tick) [received tick] = [] := by
      cases tick with
      | zero =>
        apply (a_competing_input_cannot_add_native_work_to_the_pending_visit (later 0) (received 0) ?_).2
        rw [game.play_is_the_original_current]
        change Quantities.Pending (endAt game.seed (game.past ++ []))
        rwa [List.append_nil]
      | succ earlier =>
        have reviewHere : ReviewAvailable (later (earlier + 1)) := by
          unfold ReviewAvailable
          rw [retained.2.1]
          exact review
        exact an_original_recourse_stop_spends_no_material_and_keeps_the_clock_and_control _ reviewHere
    refine ⟨(congrArg (·.raw) (advanceAt tick)).trans (paidNoMaterial.1.trans retained.1),
      (congrArg (·.control) (advanceAt tick)).trans (paidNoMaterial.2.1.trans retained.2.1), ?_⟩
    have original : later tick = endAt (submittedCut game) (tape tick) := by
      rw [game.play_is_the_original_current, endAt_append]
    rw [game.play_succ_script, inventory_append, ← original, retained.2.2, paidNoMaterial.2.2]
    rfl

theorem a_lodged_withdrawal_has_an_actual_infinite_delay_without_priority
    (busy : Quantities.Pending (submittedCut game)) (review : ReviewAvailable (submittedCut game)) :
    received 0 = withdrawalInput scope (submittedCut game) actor ∧
    Nonempty (game.TimeStall policy stopOpponent unprotectedSchedule) ∧
    (∀ tick, Reparation.Actual.SourceAuthority (submittedCut game) (tape tick)) ∧
    (∀ tick, ¬ game.WithdrawalComplete base scope actor (game.prefixAt policy stopOpponent unprotectedSchedule tick)) ∧
    Nonempty (game.Counter (game.WithdrawalComplete base scope actor) policy stopOpponent unprotectedSchedule) := by
  have pending (tick : Nat) :
      ¬ game.WithdrawalComplete base scope actor (game.prefixAt policy stopOpponent unprotectedSchedule tick) := by
    rintro ⟨receipt, same⟩
    have earlier := a_material_free_prefix_cannot_complete_a_post_submission_withdrawal
      scope game.seed game.past actor (tape tick) (the_original_stop_trajectory game scope actor follow busy review tick).2.2 receipt
    exact (not_lt_of_ge same) earlier
  refine ⟨?_, ⟨⟨(submittedCut game).raw.clock + 1, fun tick => ?_⟩⟩, ?_, pending, ?_⟩
  · change (if 1 ≤ reservedRank game + 1 then withdrawalInput scope (submittedCut game) actor
      else follow.submit game.start.civilSeen) = withdrawalInput scope (submittedCut game) actor
    exact if_pos (Nat.succ_le_succ (Nat.zero_le (reservedRank game)))
  · rw [(the_original_stop_trajectory game scope actor follow busy review tick).1]
    linarith
  · intro tick item existsItem
    rw [(the_original_stop_trajectory game scope actor follow busy review tick).2.2] at existsItem
    exact (List.not_mem_nil existsItem).elim
  · exact ⟨game.counter _ _ _ _ (fun success => by obtain ⟨tick, paid⟩ := success.2; exact pending tick paid)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
