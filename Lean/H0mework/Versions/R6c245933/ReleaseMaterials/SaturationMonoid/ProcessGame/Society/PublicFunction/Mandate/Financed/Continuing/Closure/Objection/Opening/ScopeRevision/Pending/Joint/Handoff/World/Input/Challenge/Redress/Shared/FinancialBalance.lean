import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Posting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancialBalance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.FinancialBalance

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

structure Receipt where
  private mk ::
  posting : Shared.Posting.Receipt inventory
  posting_exact : posting = Shared.Posting.generate inventory
  balance : ∀ side party good,
    Input.Event.FinancialBalance.positions (Shared.Exposure.endpoint inventory) side party good +
        Input.Event.Posting.actual (Shared.Runtime.native inventory) side party good =
      Input.Event.FinancialBalance.positions ⟨epoch, inventory⟩ side party good +
        Input.Event.FinancialBalance.issues (Shared.Runtime.native inventory) side party good +
        Input.Event.FinancialBalance.assignments (Shared.Runtime.native inventory) side party good
  net : ∀ party good,
    Input.Event.FinancialBalance.quotedNet (Shared.Exposure.endpoint inventory) party good +
        Shared.Costs.actual inventory party (.operating good) =
      Input.Event.FinancialBalance.quotedNet ⟨epoch, inventory⟩ party good +
        Input.Event.FinancialBalance.otherCredits (Shared.Runtime.native inventory) party good +
        Input.Event.FinancialBalance.issues (Shared.Runtime.native inventory) .credit party good -
        Input.Event.FinancialBalance.issues (Shared.Runtime.native inventory) .debit party good +
        Input.Event.FinancialBalance.assignments (Shared.Runtime.native inventory) .credit party good
  nonpayment_credit : ∀ party good, 0 ≤ Input.Event.FinancialBalance.otherCredits (Shared.Runtime.native inventory) party good

def generate : Receipt inventory :=
  ⟨Shared.Posting.generate inventory, rfl,
    Input.Event.FinancialBalance.financial_balance (Shared.Runtime.native inventory),
    Input.Event.FinancialBalance.actual_net_balance (Shared.Runtime.native inventory),
    Input.Event.FinancialBalance.otherTotal_nonnegative (Shared.Costs.records inventory)⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.FinancialBalance
