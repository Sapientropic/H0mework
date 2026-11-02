import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Task.Core

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt
open Computation.Search.Segmented.Publication.Learning.Paid
open Input.Challenge.Redress.Shared.Iteration
noncomputable section

/-- Cache one packet-indexed reconstruction before composing it with the
Service call. Dependent consumers read these fields without unfolding Requests. -/
structure Rebuilt (saved : Packet) where
  private mk ::
  target : Requests.Cursor
  task : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)
  native : Input.Event.Evolution saved target.saved
  law : task.model.source.code.law = Mandate.law base target.saved.1.scope
  aligned : task.point.point.source.currentAt (depth task.point.point+1) =
    current target.saved.1 target.saved.2.inputs

def result (saved : Packet) (pending : List Action)
    (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
      (Technology := Unit) (Instrument := Unit)) (old : Cursor prior.model.source.code) : Rebuilt saved :=
  ⟨⟨⟨saved.1,Communication.Source.saved saved.2 old⟩,pending⟩,
    Communication.task saved.2 pending prior old,Communication.Source.native saved.2 old,rfl,
    Communication.original_task_cut_is_the_same_actual_world saved.2 pending prior old⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication
