import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} {inventory : Inventory epoch}

def Result.packet (result : Result inventory) : Packet := by
  cases result
  next receipt => exact ⟨epoch,inventory⟩
  next needed request request_exact response response_exact => exact response.packet

def Result.native (result : Result inventory) : Evolution ⟨epoch,inventory⟩ result.packet := by
  cases result
  next receipt => exact .same _
  next needed request request_exact response response_exact =>
    exact .append (Event.inputEvolution inventory (intent inventory)) response.native

namespace Iteration

def next (packet : Packet) : Packet := (produce packet.2).packet

def after (packet : Packet) : Nat → Packet
  | 0 => packet
  | count+1 => next (after packet count)

def native (packet : Packet) : (count : Nat) → Evolution packet (after packet count)
  | 0 => .same packet
  | count+1 => .append (native packet count) (produce (after packet count).2).native

def original (packet : Packet) (count : Nat) (row : Row packet) := transport (native packet count) row

def originalRun (packet : Packet) (count : Nat) (row : Row packet) := (original packet count row).complete

def financialSlot (packet : Packet) (count index : Nat) (slot : ObligationSlot (Financial.Family.vocabulary sources))
    (present : packet.2.finance.current.slots[index]? = some slot) :=
  Progress.Response.financialSlotAlong (native packet count) index slot present

theorem every_finite_actual_redress_history_keeps_every_original_native_row
    (packet : Packet) (count : Nat) (row : Row packet) :
    (original packet count row).row.origin = row.origin ∧
      row.state.history <+: (original packet count row).state.history :=
  every_actual_step_retains_its_original_admission_and_history (native packet count) row

end Iteration
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Dispatch
