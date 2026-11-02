import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint.Posting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.AssignedFinancing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.AssignedFinancing.Cohort
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration
noncomputable section
variable {first last : Packet} (actual : Evolution first last)

abbrev flow (birth : Exposure.Birth sources (DelayedFinancing.fullRun actual)) := AssignedFinancing.Joint.atBirth sources birth

structure Receipt (birth : Exposure.Birth sources (DelayedFinancing.fullRun actual)) where
  original_slot : last.2.finance.current.slots[birth.index]? = some birth.follow.slot
  original_claim : Financial.Family.slotClaim sources birth.follow.slot = birth.claim
  complete_trace : (flow actual birth).entries.map AssignedFinancing.Joint.Entry.event =
    ((birth.suffix.events.filter fun event => event.slot == birth.index).map (sourceEvent sources))
  complete_balances : ∀ party, (flow actual birth).final.selected party + (flow actual birth).final.remainder party =
    Financial.Family.slotBalance sources birth.follow.slot party
  selected_principal : Financial.total (sources birth.claim.1) (flow actual birth).final.selected +
    AssignedFinancing.Joint.selectedPaid sources (flow actual birth).entries =
      AssignedFinancing.Joint.acquired sources (flow actual birth).entries
  remainder_principal : Financial.total (sources birth.claim.1) (flow actual birth).final.remainder +
    AssignedFinancing.Joint.remainderPaid sources (flow actual birth).entries +
      AssignedFinancing.Joint.acquired sources (flow actual birth).entries = birth.claim.2.quantity
  entry_claim : ∀ entry ∈ (flow actual birth).entries, entry.obligation.content = birth.claim
  fresh_source : ∀ entry ∈ (flow actual birth).entries, 0 < entry.result.fresh → Nonempty (AssignedFinancing.Open sources entry.boundary)
  payment_windows : ∀ side party good window,
    AssignedFinancing.Joint.Posting.payments sources (flow actual birth).entries true side party good window +
      AssignedFinancing.Joint.Posting.payments sources (flow actual birth).entries false side party good window =
        AssignedFinancing.Joint.Posting.actualPayments sources birth.follow.path side party good window
  asset_windows : ∀ side party good window,
    AssignedFinancing.Joint.Posting.assignments sources (flow actual birth).entries true side party good window +
      AssignedFinancing.Joint.Posting.assignments sources (flow actual birth).entries false side party good window =
        AssignedFinancing.Joint.Posting.actualAssignments sources birth.follow.path side party good window
  entry_balances : ∀ entry ∈ (flow actual birth).entries, ∀ selected side party good,
    Financial.Family.Migration.Posting.Balance.holding sources entry.obligation.content
        (AssignedFinancing.Joint.Posting.afterShares sources entry selected) side party good +
      AssignedFinancing.Joint.Posting.payment sources entry selected side party good =
    Financial.Family.Migration.Posting.Balance.holding sources entry.obligation.content
        (AssignedFinancing.Joint.Posting.beforeShares sources entry selected) side party good +
      AssignedFinancing.Joint.Posting.assignment sources entry selected side party good

theorem receive (birth : Exposure.Birth sources (DelayedFinancing.fullRun actual)) : Receipt actual birth where
  original_slot := birth.actual_slot
  original_claim := birth.original_claim
  complete_trace := by
    rw [(flow actual birth).events_exact,← birth.follow.path.records_sources sources birth.index,birth.follow.recorded]
  complete_balances := (flow actual birth).final.pointwise
  selected_principal := (AssignedFinancing.Joint.canonical_acquisitions_and_original_principal_conserve sources birth).1
  remainder_principal := (AssignedFinancing.Joint.canonical_acquisitions_and_original_principal_conserve sources birth).2
  entry_claim := by
    intro entry member
    exact birth.follow.path.events_preserve_original_claim sources entry.event
      ((flow actual birth).each_entry_is_an_actual_original_event entry member)
  fresh_source := by intro entry _ positive; exact entry.result.fresh_source positive
  payment_windows := AssignedFinancing.Joint.Posting.exact_payments sources (flow actual birth)
  asset_windows := AssignedFinancing.Joint.Posting.exact_assignments sources (flow actual birth)
  entry_balances := by intro entry _ selected side party good; exact AssignedFinancing.Joint.Posting.entry_balance sources entry selected side party good

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.AssignedFinancing.Cohort
