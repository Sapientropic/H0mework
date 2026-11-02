import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Exposure

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Exposure

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev endpoint := (Shared.Runtime.answer inventory).packet

/-- The existing generated prefix and the actual shared response form one run.
Both old and newly admitted debts are enumerated at the same final account. -/
def run : (Financial.Family.process sources).Run
    (ResponsibilityState.empty (Financial.Family.vocabulary sources)) (endpoint inventory).2.finance.current :=
  inventory.finance.generated.concatRuns _
    (Input.Event.Future.Expiry.Progress.Response.financeAlong (Shared.Runtime.native inventory))

def births := Financial.Family.Migration.Exposure.admissions sources (run inventory)

theorem covers_every_final_slot_once :
    (births inventory).map Financial.Family.Migration.Exposure.Birth.index =
      List.range (endpoint inventory).2.finance.current.slots.length := by
  simpa only [births, ResponsibilityState.empty, List.length_nil, List.range_zero, List.nil_append] using
    Financial.Family.Migration.Exposure.admission_indices sources (run inventory)

theorem every_final_slot_retains_its_issue_and_actual_payment
    (index : Fin (endpoint inventory).2.finance.current.slots.length) :
    ∃ birth ∈ births inventory,
      birth.index = index.val ∧
      (endpoint inventory).2.finance.current.slots[index.val]? = some birth.follow.slot ∧
      Financial.Family.slotClaim sources birth.follow.slot = birth.claim ∧
      birth.remaining + birth.paid = birth.claim.2.quantity := by
  have present : index.val ∈ List.range (endpoint inventory).2.finance.current.slots.length :=
    List.mem_range.mpr index.isLt
  rw [← covers_every_final_slot_once inventory] at present
  obtain ⟨birth, member, same⟩ := List.mem_map.mp present
  exact ⟨birth, member, same, same ▸ birth.actual_slot, birth.original_claim, birth.conservation⟩

structure Receipt where
  private mk ::
  joint : Iteration.JointReceipt inventory
  joint_exact : joint = Iteration.joint inventory
  census : (births inventory).map Financial.Family.Migration.Exposure.Birth.index =
    List.range (endpoint inventory).2.finance.current.slots.length
  admissions : (births inventory).map Financial.Family.Migration.Exposure.Birth.address =
    (run inventory).events.filterMap (Financial.Family.Migration.Exposure.admittedAddress sources)
  debts : ∀ birth ∈ births inventory,
    (endpoint inventory).2.finance.current.slots[birth.index]? = some birth.follow.slot ∧
    Financial.Family.slotClaim sources birth.follow.slot = birth.claim ∧
    birth.remaining + birth.paid = birth.claim.2.quantity
  windows : ∀ debtor unit window,
    Financial.Family.Migration.Exposure.remainingQuote sources (run inventory) debtor unit window +
      Financial.Family.Migration.Exposure.paidQuote sources (run inventory) debtor unit window =
      Financial.Family.Migration.Exposure.issuedQuote sources (run inventory) debtor unit window

def generate : Receipt inventory :=
  ⟨Iteration.joint inventory, rfl, covers_every_final_slot_once inventory,
    Financial.Family.Migration.Exposure.admissions_exact sources (run inventory),
    fun birth _ => ⟨birth.actual_slot, birth.original_claim, birth.conservation⟩,
    Financial.Family.Migration.Exposure.per_debtor_unit_window_conservation sources (run inventory)⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Exposure
