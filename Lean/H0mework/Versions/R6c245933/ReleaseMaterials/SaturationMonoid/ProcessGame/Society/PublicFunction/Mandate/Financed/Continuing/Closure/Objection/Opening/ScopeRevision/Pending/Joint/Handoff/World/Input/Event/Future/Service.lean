import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeService.Response
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Service
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def payments := (OutstandingSource.History.trailAt epoch.source inventory.inputs (inventory.inputs.length+2)).frame.payments

def decision := epoch.source.decideAt (current epoch inventory.inputs) (payments inventory)

def response (index : epoch.source.Slot) :=
  OutstandingSource.History.NativeService.Response.produce epoch.source (inventory.services index) (ownWord inventory)

def nativeRun (index : epoch.source.Slot) := (inventory.services index).actualRun epoch.source (ownWord inventory)

def image (index : epoch.source.Slot) := OutstandingSource.History.NativeService.Response.image
  epoch.source (epochInputs epoch.fresh) inventory.inputs index (ownWord inventory)

theorem original_live_slot_drives_the_actual_pending_task (index : epoch.source.Slot)
    (live : (inventory.services index).state.current.LiveAt 0) :
    epoch.source.seed.slot index ∈ epoch.source.pendingSlots (payments inventory) ∧
    ownWord inventory = (decision inventory).word :=
  ⟨OutstandingSource.History.NativeService.Response.live_is_in_the_original_pending_task epoch.source
    (inventory.services index) live,own_word_is_generated_by_the_actual_residual inventory⟩

theorem the_actual_advance_records_the_original_service_event (index : epoch.source.Slot)
    (live : (inventory.services index).state.current.LiveAt 0) :
    ((World.submit inventory (ownWord inventory)).services index).state.current.history =
      (inventory.services index).state.current.history ++ [image inventory index] :=
  OutstandingSource.History.NativeService.Response.advance_history epoch.source (inventory.services index) live (ownWord inventory)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Service
