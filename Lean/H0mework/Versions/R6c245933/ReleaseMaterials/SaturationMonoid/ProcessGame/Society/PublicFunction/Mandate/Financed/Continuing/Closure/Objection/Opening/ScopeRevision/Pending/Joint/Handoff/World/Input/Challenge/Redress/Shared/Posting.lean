import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Costs
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Posting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Posting

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def receipts := Input.Event.Posting.receipts (Shared.Runtime.native inventory)

structure Receipt where
  private mk ::
  costs : Shared.Costs.Receipt inventory
  costs_exact : costs = Shared.Costs.generate inventory
  keys : (receipts inventory).map (VisitReceipt.window sources) = Shared.Costs.records inventory
  events : ((receipts inventory).map (fun receipt => (receipt.native sources).events)).flatten =
    (Input.Event.Future.Expiry.Progress.Response.financeAlong (Shared.Runtime.native inventory)).events
  postings : ∀ side party good,
    Input.Event.Posting.actual (Shared.Runtime.native inventory) side party good =
      Financial.Family.Migration.Posting.total sources (Shared.Costs.records inventory) side party good
  debit : ∀ party good,
    Input.Event.Posting.actual (Shared.Runtime.native inventory) .debit party good =
      Shared.Costs.actual inventory party (.debtPayment good)

def generate : Receipt inventory :=
  ⟨Shared.Costs.generate inventory, rfl, Input.Event.Posting.keys (Shared.Runtime.native inventory),
    Input.Event.Posting.events (Shared.Runtime.native inventory),
    Input.Event.Posting.exact_amount (Shared.Runtime.native inventory),
    Input.Event.Posting.debit_is_the_same_material_payment (Shared.Runtime.native inventory)⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Posting
