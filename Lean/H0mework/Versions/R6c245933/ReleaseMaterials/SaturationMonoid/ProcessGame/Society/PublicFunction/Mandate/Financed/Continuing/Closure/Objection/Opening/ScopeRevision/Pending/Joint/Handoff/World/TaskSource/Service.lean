import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local
open Owned.PublicTask.Local.Inquiry
open Owned.PublicTask.Local.Inquiry.Planning
noncomputable section

variable {task : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)} {cache : Inquiry.Frame task}

def controls : GlobalPolicy.Service task cache → List (Rule task.model.source.code)
  | .unavailable step .. => step.path.finish.past
  | .completed step _ _ _ outcome _ => match outcome with
      | .blocked _ => step.path.finish.past
      | .selected candidate => step.path.finish.past ++ Prefix.Runtime.suffix
          (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol
  | .worldShort step .. => step.path.finish.past
  | .worldCompleted step _ _ _ _ _ _ _ _ selected =>
      step.path.finish.past ++ match GlobalPolicy.World.Selection.candidate? task selected with
        | none => []
        | some candidate => Prefix.Runtime.suffix
            (original := task.original) (past := step.path.finish.past) task.point.point candidate.protocol

theorem full_is_the_actual_control_installation (made : GlobalPolicy.Service task cache) :
    made.full = Splice.install task.point.point task.rival (controls made) := by
  cases made with
  | unavailable step => exact Computation.Search.Segmented.Publication.Learning.Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival
  | worldShort step => exact Computation.Search.Segmented.Publication.Learning.Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival
  | completed step _ _ _ outcome _ =>
      cases outcome with
      | blocked => exact Computation.Search.Segmented.Publication.Learning.Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival
      | selected candidate =>
          change Splice.install (Owned.PublicTask.Local.Inquiry.Planning.current task step.path.finish).point task.rival _ = _
          rw [Computation.Search.Segmented.Publication.Learning.Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival]
          exact (List.foldl_append ..).symm
  | worldCompleted step _ _ _ _ _ _ _ _ selected =>
      cases found : GlobalPolicy.World.Selection.candidate? task selected with
      | none =>
          simp only [GlobalPolicy.Service.full,controls,found,List.append_nil]
          exact Computation.Search.Segmented.Publication.Learning.Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival
      | some candidate =>
          simp only [GlobalPolicy.Service.full,controls,found]
          rw [Computation.Search.Segmented.Publication.Learning.Paid.State.current_is_the_actual_control_prefix step.path.finish.shell task.point task.rival]
          exact (List.foldl_append ..).symm

theorem installed_depth (model : Native.Authority.Bound (Party := Bool) (Good := Good)
    (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (point : Cursor model.source.code) (rival : Opponent model.source.code) (rules : List (Rule model.source.code)) :
    depth (Splice.install point rival rules) = depth point + rules.length := by
  induction rules generalizing point with
  | nil => exact (Nat.add_zero _).symm
  | cons rule later ih =>
      change depth (Splice.install (point.after rule rival) rival later) = _
      rw [ih]
      have step : depth (point.after rule rival) = depth point + 1 := by
        change point.history.length+1+(point.cut+1) = (point.history.length+1+point.cut)+1
        omega
      rw [step,List.length_cons]
      omega

theorem installed_current (model : Native.Authority.Bound (Party := Bool) (Good := Good)
    (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (point : Cursor model.source.code) (rival : Opponent model.source.code) (rules : List (Rule model.source.code)) :
    (Splice.install point rival rules).source.currentAt (depth point+1) = point.source.currentAt (depth point+1) := by
  have visits := Machine.actual_prefix_from_events point.source.input (Splice.install point rival rules).source.input
    rfl rfl (point.history.length+2+point.cut)
    (Installation.Chain.fold_keeps_every_prior_raw_event (model := model) point rival rules)
    (depth point+1) (by change point.history.length+1+point.cut+1 ≤ point.history.length+2+point.cut;omega)
  unfold Machine.currentAt
  rw [visits]
  cases (ProgrammeHistory.visitAt point.source.input (depth point+1)).current <;> rfl

variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)
variable {cache : Inquiry.Frame (TaskSource.task inventory pending)}
  (made : GlobalPolicy.Service (TaskSource.task inventory pending) cache)

def start := depth (cursor inventory pending)
def count := (controls made).length

theorem full_keeps_the_saved_actual_cut :
    made.full.source.currentAt (start inventory pending+1) = current epoch (prepared inventory).inputs := by
  rw [full_is_the_actual_control_installation made]
  change (Splice.install (TaskSource.task inventory pending).point.point
    (TaskSource.task inventory pending).rival (controls made)).source.currentAt
      (depth (TaskSource.task inventory pending).point.point+1) = _
  rw [installed_current]
  exact native_current_is_the_same_actual_cut inventory pending

theorem all_service_branches_write_back_their_actual_endpoint :
    current epoch (Writeback.append (prepared inventory)
      (Writeback.words made.full.source (start inventory pending) (count inventory pending made))).inputs =
      made.full.source.currentAt (depth made.full+1) := by
  have endpoint := Writeback.writeback_keeps_the_exact_native_endpoint made.full.source (prepared inventory)
    (start inventory pending) (count inventory pending made) rfl (full_keeps_the_saved_actual_cut inventory pending made)
  have address : start inventory pending + count inventory pending made = depth made.full := by
    rw [full_is_the_actual_control_installation made,installed_depth]
    rfl
  rw [address] at endpoint
  exact endpoint

def next := Writeback.next made.full.source (prepared inventory) (start inventory pending) (count inventory pending made) pending
def native : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet) (next inventory pending made).saved :=
  .append (TaskSource.preparation inventory)
    (Writeback.native made.full.source (prepared inventory) (start inventory pending) (count inventory pending made) pending)
def nextTask := Writeback.nextTask made.full.source (prepared inventory) (start inventory pending) (count inventory pending made) pending

/-- Re-entry calls the original paid planner with the newly compiled actual scope. -/
def reenter := GlobalPolicy.produce (nextTask inventory pending made)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service
