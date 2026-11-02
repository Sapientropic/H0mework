import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.DelayedFinancing.Cash

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.AssignedFinancing
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration
noncomputable section
variable {first last : Packet} (actual : Evolution first last)

/-- Each source-checked assignment refines its own original native slot. -/
theorem original_slot_assignment_and_exact_shares
    (birth : Exposure.Birth sources (DelayedFinancing.fullRun actual))
    (report : AssignedFinancing.Report sources birth.follow.path) :
    record sources birth.index report.occurrence.boundary ∈ (DelayedFinancing.fullRun actual).events ∧
    report.occurrence.obligation.content = birth.claim ∧
    report.occurrence.boundary.receipt.kind = .assignment ∧
    0 < AssignedFinancing.quantity sources report.occurrence.boundary ∧
    last.2.finance.current.slots[birth.index]? = some birth.follow.slot ∧
    (∀ party, report.flow.final.selected party + report.flow.final.remainder party = Financial.Family.slotBalance sources birth.follow.slot party) ∧
    Financial.total (sources report.occurrence.obligation.content.1) report.flow.final.selected + report.flow.selectedPaid =
      AssignedFinancing.quantity sources report.occurrence.boundary := by
  have member := report.occurrence.actual_record birth.index
  rw [birth.follow.recorded] at member
  have suffix := (List.mem_filter.mp member).1
  refine ⟨?_,report.occurrence.same_claim,report.origin.assignment,report.origin.positive,
    birth.actual_slot,report.exact_remaining_shares,report.actual_acquisition_is_not_reissued_or_counted_twice⟩
  rw [birth.exact_events]
  exact List.mem_append_right _ suffix

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.AssignedFinancing
