import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Core
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local
open Owned.PublicTask.Local.Inquiry
open Owned.PublicTask.Local.Inquiry.Planning
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)
  {cache : Inquiry.Frame (TaskSource.task inventory pending)}
  (made : GlobalPolicy.Service (TaskSource.task inventory pending) cache)

/-- The actual original Service supplies both the old event cursor and its
own next scope. No frame, event schedule or successful target is supplied. -/
def reconstructCommunication :=
  Communication.produce (next inventory pending made).saved.2 made.full

def reconstructedCommunicationNative : Input.Event.Evolution (⟨epoch,inventory⟩ : Packet)
    (reconstructCommunication inventory pending made).packet :=
  Communication.appendAt (next inventory pending made).saved
    (native inventory pending made) (reconstructCommunication inventory pending made).native
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Service
