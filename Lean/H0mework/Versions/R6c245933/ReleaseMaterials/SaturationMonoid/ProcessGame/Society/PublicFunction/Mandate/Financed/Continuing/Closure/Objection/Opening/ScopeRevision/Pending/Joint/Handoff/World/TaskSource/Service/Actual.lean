import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Result
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service.Actual
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local Owned.PublicTask.Local.Inquiry Owned.PublicTask.Local.Inquiry.Planning
open Input.Challenge.Redress.Shared.Iteration
noncomputable section

variable {prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)} {cache : Inquiry.Frame prior}
  {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)
  (made : GlobalPolicy.Service prior cache)

/-- Use the carried Task's actual cut; no fresh Task or source is compiled here. -/
def next := Writeback.next made.full.source inventory (depth prior.point.point) (controls made).length pending

def native : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) (next inventory pending made).saved :=
  Writeback.native made.full.source inventory (depth prior.point.point) (controls made).length pending

theorem raw_writeback_reaches_the_same_service_endpoint
    (law : prior.model.source.code.law = Mandate.law base epoch.scope)
    (aligned : prior.point.point.source.currentAt (depth prior.point.point+1) = current epoch inventory.inputs) :
    current epoch (Writeback.append inventory
      (Writeback.words made.full.source (depth prior.point.point) (controls made).length)).inputs =
      made.full.source.currentAt (depth made.full+1) := by
  have kept : made.full.source.currentAt (depth prior.point.point+1) = current epoch inventory.inputs := by
    rw [full_is_the_actual_control_installation made,installed_current (model := prior.model)]
    exact aligned
  have endpoint := Writeback.writeback_keeps_the_exact_native_endpoint made.full.source inventory
    (depth prior.point.point) (controls made).length law kept
  have address : depth prior.point.point + (controls made).length = depth made.full := by
    rw [full_is_the_actual_control_installation made,installed_depth]
  rw [address] at endpoint
  exact endpoint

abbrev Rebuilt := Communication.Rebuilt
abbrev rebuildAt := Communication.result

def rebuilt := rebuildAt (next inventory pending made).saved (next inventory pending made).pending prior made.full

def task := (rebuilt inventory pending made).task
def target := (rebuilt inventory pending made).target

def reconstructedNative : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet)
    (target inventory pending made).saved :=
  .append (native inventory pending made) (rebuilt inventory pending made).native

theorem target_task_keeps_the_actual_source :
    (task inventory pending made).point.point =
      Communication.Source.cursor (next inventory pending made).saved.2 made.full := rfl

theorem target_task_cut_is_the_written_world :
    (task inventory pending made).point.point.source.currentAt
      (depth (task inventory pending made).point.point+1) =
      current (target inventory pending made).saved.1 (target inventory pending made).saved.2.inputs :=
  (rebuilt inventory pending made).aligned


def SelectedNextIsChecked : Prop :=
  match made with
  | .worldCompleted step _ _ _ _ _ _ _ _ selected =>
      ∀ candidate,selected.candidate? prior = some candidate →
        next inventory pending made = Commitment.next prior inventory step.path.finish.past candidate.protocol ∧
        task inventory pending made = (Commitment.rebuilt prior inventory step.path.finish.past candidate.protocol).task ∧
        target inventory pending made = (Commitment.rebuilt prior inventory step.path.finish.past candidate.protocol).target
  | _ => True

theorem selected_next_is_the_prechecked_actual_next (samePending : pending = prior.worldPending) :
    SelectedNextIsChecked inventory pending made := by
  cases made with
  | unavailable => trivial
  | completed => trivial
  | worldShort => trivial
  | worldCompleted step generated permit paid input supplied rate declared covered selected =>
      intro candidate chosen
      let service : GlobalPolicy.Service prior cache :=
        .worldCompleted step generated permit paid input supplied rate declared covered selected
      have word : controls service = Commitment.controls prior step.path.finish.past candidate.protocol := by
        simp only [service,controls,chosen]
        rfl
      have installed : service.full = Commitment.full prior step.path.finish.past candidate.protocol := by
        rw [full_is_the_actual_control_installation,word]
        rfl
      have entered : next inventory pending service =
          Commitment.next prior inventory step.path.finish.past candidate.protocol := by
        unfold next Commitment.next
        rw [installed,word,samePending]
      have key : (next inventory pending service,service.full) =
          (Commitment.next prior inventory step.path.finish.past candidate.protocol,
            Commitment.full prior step.path.finish.past candidate.protocol) := by
        apply Prod.ext
        · with_reducible exact entered
        · with_reducible exact installed
      dsimp only [service] at entered installed key
      constructor
      · with_reducible exact entered
      constructor
      · simpa only [task,rebuilt,Commitment.rebuilt] using congrArg (fun pair : Requests.Cursor × Continuation.Cursor prior.model.source.code =>
          (rebuildAt pair.1.saved pair.1.pending prior pair.2).task) key
      · simpa only [target,rebuilt,Commitment.rebuilt] using congrArg (fun pair : Requests.Cursor × Continuation.Cursor prior.model.source.code =>
          (rebuildAt pair.1.saved pair.1.pending prior pair.2).target) key

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service.Actual
