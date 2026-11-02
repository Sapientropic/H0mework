import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Planning

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback.Prefix

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction
open Input.Challenge.Redress.Shared.Iteration
noncomputable section

variable {epoch : Epoch}

variable (source : Machine Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit)

variable (inventory : Inventory epoch) (start count : Nat) (pending : List Action)

def nextTask := TaskSource.task (next source inventory start count pending).saved.2
  (next source inventory start count pending).pending

theorem next_task_receives_this_exact_residual_and_packet :
    (nextTask source inventory start count pending).worldInput = some (.actual
      (prepared (next source inventory start count pending).saved.2)) ∧
    (next source inventory start count pending).pending = (receive source inventory start count pending).report.residual :=
  ⟨rfl,rfl⟩

theorem no_original_responsibility_is_erased (row : Input.Event.Future.Expiry.Progress.Responsibility.Row (⟨epoch,inventory⟩ : Packet)) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport (native source inventory start count pending) row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport (native source inventory start count pending) row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport (native source inventory start count pending) row).native.Run
      row.origin.initial (Input.Event.Future.Expiry.Progress.Responsibility.transport (native source inventory start count pending) row).state) :=
  ⟨(Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history _ row).1,
    (Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history _ row).2,
    ⟨(Input.Event.Future.Expiry.Progress.Responsibility.transport (native source inventory start count pending) row).complete⟩⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback
