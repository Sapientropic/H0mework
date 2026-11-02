import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Padding
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument} {fuel : Nat}

def controls (original : Prefix.Rule code) (programme : Program code fuel) : List (Prefix.Rule code) :=
  programme.controls ++ List.replicate (fuel-programme.controls.length) (programme.controls.getLast?.getD original)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem length (original : Prefix.Rule code) (programme : Program code fuel) :
    (controls original programme).length = fuel := by
  simp only [controls,List.length_append,List.length_replicate]
  exact Nat.add_sub_of_le programme.bounded

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem last_stage (original : Prefix.Rule code) (programme : Program code fuel) :
    (controls original programme).getLast?.getD original = programme.controls.getLast?.getD original := by
  simp only [controls,List.getLast?_append,List.getLast?_replicate]
  split <;> simp

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_stage_is_the_original_stage (original : Prefix.Rule code) (programme : Program code fuel)
    (offset : Nat) : (Splice.word (controls original programme)).at original offset = programme.at original offset := by
  change ((controls original programme)[offset]?).getD ((controls original programme).getLast?.getD original) =
    (programme.controls[offset]?).getD (programme.controls.getLast?.getD original)
  rw [last_stage]
  by_cases inside : offset < programme.controls.length
  · rw [controls,List.getElem?_append_left inside]
  · rw [controls,List.getElem?_append_right (Nat.le_of_not_gt inside),
      List.getElem?_eq_none (Nat.le_of_not_gt inside),List.getElem?_replicate]
    split <;> rfl

omit [DecidableEq Port] [DecidableEq Technology] in
theorem preserves_prefix (original : Prefix.Rule code) (programme : Program code fuel)
    (past : List (Prefix.Rule code)) (retained : programme.controls.take past.length = past) :
    (controls original programme).take past.length = past := by
  have bounded : past.length ≤ programme.controls.length := by
    have counts := congrArg List.length retained
    simp only [List.length_take] at counts
    omega
  rw [controls,List.take_append_of_le_length bounded]
  exact retained

variable (point : Cursor code) (original : Prefix.Rule code) (programme : Program code fuel) (rival : Opponent code)

theorem same_entire_entry :
    entry point original (Splice.word (controls original programme)) rival = entry point original programme rival := by
  apply congrArg (Future.takeover point.source point.entry point.cut)
  funext history past frame
  unfold Continuation.Whole.controller
  rw [every_stage_is_the_original_stage]

theorem same_entire_source :
    source point original (Splice.word (controls original programme)) rival = source point original programme rival := by
  have inputs := same_entire_entry point original programme rival
  have schedules : schedule point original (Splice.word (controls original programme)) = schedule point original programme := by
    apply Subtype.ext
    apply List.map_congr_left
    intro offset _
    rw [every_stage_is_the_original_stage]
  change Execution.target {point.source with feedback? := some (entry point original (Splice.word (controls original programme)) rival)}
    point.cut (schedule point original (Splice.word (controls original programme))).val =
    Execution.target {point.source with feedback? := some (entry point original programme rival)} point.cut (schedule point original programme).val
  rw [inputs,schedules]


theorem same_entire_states :
    (source point original (Splice.word (controls original programme)) rival).feedbackState
        (entry point original (Splice.word (controls original programme)) rival) =
      (source point original programme rival).feedbackState (entry point original programme rival) := by
  have schedules : schedule point original (Splice.word (controls original programme)) = schedule point original programme := by
    apply Subtype.ext
    apply List.map_congr_left
    intro offset _
    rw [every_stage_is_the_original_stage]
  change (Execution.target {point.source with feedback? := some (entry point original (Splice.word (controls original programme)) rival)}
      point.cut (schedule point original (Splice.word (controls original programme))).val).feedbackState
        (entry point original (Splice.word (controls original programme)) rival) =
    (Execution.target {point.source with feedback? := some (entry point original programme rival)} point.cut
      (schedule point original programme).val).feedbackState (entry point original programme rival)
  rw [same_entire_entry,schedules]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Padding
