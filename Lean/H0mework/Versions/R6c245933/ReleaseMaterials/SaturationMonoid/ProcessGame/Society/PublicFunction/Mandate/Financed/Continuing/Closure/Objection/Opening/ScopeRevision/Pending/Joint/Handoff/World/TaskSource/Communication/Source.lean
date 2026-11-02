import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Core

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Source
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch)
  {original : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit} (old : Cursor original)

/-- The initial response is empty; recorded events each receive their own
actual feedback cut. The original local architecture and policy language stay. -/
abbrev code : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit :=
  {Communication.code inventory old with eventLimit := 0}

def commands : List (Feedback.Reconstruction.Command (code inventory old)) :=
  (Feedback.Reconstruction.transcript old.source old.entry old.cut).map
    (fun command => ⟨command.policy,command.move⟩)

def opponent : Opponent (code inventory old) := fun history _ _ =>
  ((commands inventory old)[history.length-1]?).bind (fun command => command.move)

abbrev input : Feedback.Input (code inventory old) :=
  ⟨opponent inventory old,(commands inventory old).length +
    max (old.source.feedbackState old.entry old.cut).remaining
      (Input.Event.Future.Expiry.horizon epoch.bound)⟩

abbrev baseMachine : Machine Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code inventory old
  reference := old.reference
  reference_generated := old.reference_generated
  history := (code inventory old).publicPrefix
  original := Code.public_prefix_is_an_actual_generated_history _
  opponent := opponent inventory old
  side := .original
  feedback? := some (input inventory old)

def schedule := (commands inventory old).map Feedback.Reconstruction.Command.policy
abbrev machine := Feedback.Execution.target (baseMachine inventory old) 0 (schedule inventory old)

def cursor : Cursor (code inventory old) :=
  let source := machine inventory old
  ⟨source.reference,source.reference_generated,source.history,source.original,source.opponent,source.side,
    input inventory old,source.feedbackOverrides,(commands inventory old).length,1⟩

theorem cursor_is_the_actual_emitter : (cursor inventory old).source = machine inventory old := rfl

/-- Both native initialization visits are actual World submissions. -/
def prepared := Writeback.append inventory [[],[]]
def preparation : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) ⟨epoch,prepared inventory⟩ :=
  .append (.submit inventory []) (.submit (World.submit inventory []) [])

def words := (machine inventory old).feedbackWords (commands inventory old).length
def saved := Writeback.append (prepared inventory) (words inventory old)
def native : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) ⟨epoch,saved inventory old⟩ :=
  .append (preparation inventory) (Writeback.appendNative (prepared inventory) (words inventory old))

theorem initialization_is_the_same_actual_world :
    ((machine inventory old).feedbackInitial (input inventory old)).current =
      current epoch (prepared inventory).inputs := by
  rw [show prepared inventory = Writeback.append inventory [[],[]] by rfl,
    Writeback.current_is_the_raw_fold]
  rfl

private theorem history_length (index : Nat) :
    ((machine inventory old).feedbackState (input inventory old) index).history.length = 1+index := by
  rw [(machine inventory old).feedback_keeps_the_complete_actual_history (input inventory old) rfl rfl]
  simp only [Machine.feedbackWords,List.length_append,List.length_map,List.length_range,List.length_singleton]
  rfl

theorem each_old_control_is_actually_installed (index : Nat) (inside : index < (commands inventory old).length) :
    (machine inventory old).feedbackPolicy index = (commands inventory old)[index].policy := by
  have installed := Feedback.Execution.policy_at (baseMachine inventory old) 0 (schedule inventory old) index
  rw [Nat.zero_add] at installed
  rw [installed]
  simp only [Feedback.Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_eq_getElem inside,
    Option.map_some,Option.getD_some]

theorem each_old_move_is_actually_offered (index : Nat) (inside : index < (commands inventory old).length) :
    (input inventory old).opponent
      ((machine inventory old).feedbackState (input inventory old) index).history
      ((machine inventory old).feedbackState (input inventory old) index).past
      ((machine inventory old).feedbackState (input inventory old) index).frame =
      (commands inventory old)[index].move := by
  change ((commands inventory old)[_ - 1]?).bind (fun command => command.move) = _
  rw [history_length]
  simp only [Nat.add_sub_cancel_left,List.getElem?_eq_getElem inside,Option.bind_some]

theorem each_old_command_runs_in_the_original_emitter (index : Nat) (inside : index < (commands inventory old).length) :
    (machine inventory old).feedbackState (input inventory old) (index+1) =
      Feedback.Reconstruction.next (code inventory old)
        ((machine inventory old).feedbackState (input inventory old) index) (commands inventory old)[index] := by
  rw [Machine.feedbackState,each_old_control_is_actually_installed inventory old index inside,
    Feedback.Residual.advance_is_its_actual_choice,each_old_move_is_actually_offered inventory old index inside]
  rfl

theorem remaining_at (count : Nat) :
    ((machine inventory old).feedbackState (input inventory old) count).remaining =
      (input inventory old).budget-count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change ((machine inventory old).feedbackState (input inventory old) count).remaining-1 = _
      rw [ih]
      omega

theorem replay_keeps_the_old_budget_and_the_new_source_horizon :
    ((machine inventory old).feedbackState (input inventory old) (commands inventory old).length).remaining =
      max (old.source.feedbackState old.entry old.cut).remaining
        (Input.Event.Future.Expiry.horizon epoch.bound) := by
  rw [remaining_at]
  exact Nat.add_sub_cancel_left _ _

def failureAt (index : Nat) (inside : index < (commands inventory old).length) :=
  Feedback.Reconstruction.failure? (code inventory old)
    ((machine inventory old).feedbackState (input inventory old) index) (commands inventory old)[index]

theorem cursor_current_is_the_same_written_world :
    (cursor inventory old).source.currentAt (2+(cursor inventory old).cut) =
      current epoch (saved inventory old).inputs := by
  have aligned : (machine inventory old).currentAt (1+1) = current epoch (prepared inventory).inputs :=
    ((machine inventory old).feedback_initial_is_the_actual_response_successor (input inventory old)).trans
      (initialization_is_the_same_actual_world inventory old)
  have written := Writeback.writeback_keeps_the_exact_native_endpoint
    (machine inventory old) (prepared inventory) 1 (commands inventory old).length rfl aligned
  change current epoch (Writeback.append (prepared inventory)
    (Writeback.words (machine inventory old) 1 (commands inventory old).length)).inputs = _ at written
  have sameWords : words inventory old =
      Writeback.words (machine inventory old) 1 (commands inventory old).length := rfl
  change _ = current epoch (Writeback.append (prepared inventory) (words inventory old)).inputs
  rw [sameWords,written]
  congr 1
  change 2+(commands inventory old).length = 1+(commands inventory old).length+1
  omega

def model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨base,epoch.scope,(cursor inventory old).source,rfl,rfl⟩

theorem the_original_view_reads_the_paid_reconstructed_frame :
    (Owned.PublicTask.currentView (cursor inventory old)).point.source.feedbackState
      (cursor inventory old).entry (cursor inventory old).cut =
      (machine inventory old).feedbackState (input inventory old) (commands inventory old).length := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Source
