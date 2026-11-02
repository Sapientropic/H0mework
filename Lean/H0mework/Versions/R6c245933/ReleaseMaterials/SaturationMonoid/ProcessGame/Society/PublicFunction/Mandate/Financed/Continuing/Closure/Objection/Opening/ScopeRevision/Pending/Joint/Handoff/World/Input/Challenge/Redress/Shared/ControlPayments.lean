import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.FinancialBalance
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.ControlPayments

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.ControlPayments

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

structure Receipt where
  private mk ::
  finance : Shared.FinancialBalance.Receipt inventory
  finance_exact : finance = Shared.FinancialBalance.generate inventory
  partition : ∀ credit party good,
    Input.Event.ControlPayments.actual (Shared.Runtime.native inventory) true credit party good +
      Input.Event.ControlPayments.actual (Shared.Runtime.native inventory) false credit party good =
        Input.Event.Posting.actual (Shared.Runtime.native inventory) (Input.Event.ControlPayments.side credit) party good
  debit : ∀ party good,
    Input.Event.ControlPayments.actual (Shared.Runtime.native inventory) true false party good +
      Input.Event.ControlPayments.actual (Shared.Runtime.native inventory) false false party good =
        Shared.Costs.actual inventory party (.debtPayment good)
  bounded : ∀ credit party good,
    Input.Event.ControlPayments.actual (Shared.Runtime.native inventory) true credit party good ≤
      Input.Event.Posting.actual (Shared.Runtime.native inventory) (Input.Event.ControlPayments.side credit) party good

def generate : Receipt inventory :=
  ⟨Shared.FinancialBalance.generate inventory, rfl,
    Input.Event.ControlPayments.actual_partition (Shared.Runtime.native inventory),
    Input.Event.ControlPayments.actual_debit_is_partitioned_once (Shared.Runtime.native inventory),
    Input.Event.ControlPayments.actual_selected_bounded (Shared.Runtime.native inventory)⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.ControlPayments
