import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback.Prefix
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Reconstruction

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Input.Challenge.Redress.Shared.Iteration

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)
  {original : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit} (old : Cursor original)

abbrev code := Feedback.Reconstruction.code old.source.code (Mandate.law base epoch.scope)
  (current epoch inventory.inputs) epoch.source.seed.task

def commands : List (Feedback.Reconstruction.Command (code inventory old)) :=
  (Feedback.Reconstruction.transcript old.source old.entry old.cut).map
    (Feedback.Reconstruction.recode original (Mandate.law base epoch.scope)
      (current epoch inventory.inputs) epoch.source.seed.task)

def seed : Feedback.State (code inventory old) := Feedback.Reconstruction.seed (code inventory old)
  (current epoch inventory.inputs) ((commands inventory old).length +
    (old.source.feedbackState old.entry old.cut).remaining)

structure Result where
  private mk ::
  replay : Feedback.Reconstruction.Run (code inventory old) (seed inventory old) (commands inventory old)
  generated : replay = Feedback.Reconstruction.execute (code inventory old) (seed inventory old) (commands inventory old)

def produce : Result inventory old :=
  ⟨Feedback.Reconstruction.execute (code inventory old) (seed inventory old) (commands inventory old),rfl⟩

namespace Result
variable {inventory old} (made : Result inventory old)

def saved : Inventory epoch := Writeback.append inventory made.replay.words
abbrev packet : Packet := ⟨epoch,made.saved⟩
def native : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) made.packet :=
  Writeback.appendNative inventory made.replay.words

theorem the_new_frame_uses_the_exact_actual_world :
    made.replay.state.current = current epoch made.saved.inputs := by
  rw [saved,Writeback.current_is_the_raw_fold]
  exact made.replay.current_is_the_actual_raw_fold

theorem every_actual_replay_cut_is_written_back :
    made.saved.inputs = inventory.inputs ++ made.replay.words ∧
    made.replay.words.length = (commands inventory old).length :=
  ⟨Writeback.inputs_are_the_actual_append _ _,made.replay.every_cut_is_retained⟩

theorem the_new_interpreter_keeps_the_old_local_architecture :
    (code inventory old).sites = original.sites ∧
    (code inventory old).signals = original.signals ∧
    (code inventory old).readLocal = original.readLocal ∧
    (code inventory old).afterDelivery = original.afterDelivery ∧
    (code inventory old).law = Mandate.law base epoch.scope ∧
    (code inventory old).task = epoch.source.seed.task := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def respond (pending : List Action) : Requests.Result (⟨made.packet,pending⟩ : Requests.Cursor) [] :=
  Requests.produce (⟨made.packet,pending⟩ : Requests.Cursor) []
def next (pending : List Action) : Requests.Cursor := (made.respond pending).next

def nextNative (pending : List Action) :
    Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) (made.next pending).saved :=
  .append made.native (made.respond pending).native

theorem every_old_row_follows_the_actual_new_law_replay
    (row : Input.Event.Future.Expiry.Progress.Responsibility.Row (⟨epoch,inventory⟩ : Packet)) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).native.Run
      row.origin.initial (Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history _ row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history _ row).2,
    ⟨(Input.Event.Future.Expiry.Progress.Responsibility.transport made.native row).complete⟩⟩
end Result

/-- Eliminate the abstract dependent packet once; do not unfold the source
response merely to identify a packet with its own two projections. -/
def appendAt {first last : Packet} (middle : Packet)
    (before : Input.Event.Evolution first middle)
    (after : Input.Event.Evolution (⟨middle.1,middle.2⟩ : Packet) last) :
    Input.Event.Evolution first last := by
  rcases middle with ⟨epoch,inventory⟩
  exact .append before after
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication
