import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.TaskReentryContract
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction
open World.TaskSource
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local
open Owned.PublicTask.Local.Inquiry
open Owned.PublicTask.Local.Inquiry.Planning
open World.Input.Challenge.Redress.Shared.Iteration

variable {epoch : World.Epoch} (inventory : World.Inventory epoch) (pending : List Action)

example (words : List (List Action)) : (Writeback.append inventory words).inputs = inventory.inputs ++ words :=
  Writeback.inputs_are_the_actual_append inventory words

example (source : Machine Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit) (start count : Nat) :
    (Writeback.words source start count).foldl source.code.law.next (source.currentAt (start+1)) =
      source.currentAt (start+count+1) := Writeback.source_words_reach_their_actual_current source start count

example (source : Machine Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit) (start count : Nat)
    (law : source.code.law = Mandate.law Mandate.Financed.base epoch.scope)
    (same : source.currentAt (start+1) = World.current epoch inventory.inputs) :
    World.current epoch (Writeback.append inventory (Writeback.words source start count)).inputs =
      source.currentAt (start+count+1) :=
  Writeback.writeback_keeps_the_exact_native_endpoint source inventory start count law same

variable {cache : Inquiry.Frame (World.TaskSource.task inventory pending)}
  (made : GlobalPolicy.Service (World.TaskSource.task inventory pending) cache)

example : made.full = Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Splice.install
    (World.TaskSource.task inventory pending).point.point (World.TaskSource.task inventory pending).rival (Service.controls made) :=
  Service.full_is_the_actual_control_installation made

example : made.full.source.currentAt (Service.start inventory pending+1) =
    World.current epoch (prepared inventory).inputs := Service.full_keeps_the_saved_actual_cut inventory pending made

example : World.current epoch (Writeback.append (prepared inventory)
    (Writeback.words made.full.source (Service.start inventory pending) (Service.count inventory pending made))).inputs =
      made.full.source.currentAt (Budget.Programme.Debt.depth made.full+1) :=
  Service.all_service_branches_write_back_their_actual_endpoint inventory pending made

example : World.Input.Event.Evolution (⟨epoch,inventory⟩ : World.Packet) (Service.next inventory pending made).saved :=
  Service.native inventory pending made

example : Service.reenter inventory pending made = GlobalPolicy.produce (Service.nextTask inventory pending made) := rfl

variable (state : Requests.Cursor) (count : Nat)

example : (World.TaskSource.Iteration.execute 0 state).finish = state := rfl

example (run : World.TaskSource.Iteration.Run state count)
    (row : World.Input.Event.Future.Expiry.Progress.Responsibility.Row state.saved) :
    (World.Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).row.origin = row.origin ∧
      row.state.history <+: (World.Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state.history ∧
      Nonempty ((World.Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).native.Run row.origin.initial
        (World.Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state) :=
  run.no_original_responsibility_is_erased row

example (run : World.TaskSource.Iteration.Run state count) : Nonempty ((Financial.Family.process World.sources).Run
    state.saved.2.finance.current run.finish.saved.2.finance.current) := ⟨run.finance⟩

example (step : World.TaskSource.Iteration.Step state) : step.original =
    GlobalPolicy.produce (World.TaskSource.Iteration.task state) := step.generated

#eval IO.println "PUBLIC TASK REENTRY CONTRACT PASS: 12/12 (actual endpoint, original rows/finance and regenerated Task recursion)"
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.TaskReentryContract
