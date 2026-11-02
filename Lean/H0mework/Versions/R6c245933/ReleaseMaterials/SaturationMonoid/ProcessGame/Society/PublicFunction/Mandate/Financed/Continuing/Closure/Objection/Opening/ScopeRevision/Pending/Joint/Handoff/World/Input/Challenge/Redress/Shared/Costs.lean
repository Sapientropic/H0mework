import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Exposure
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Costs

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Costs

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup

noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def records := Input.Event.Costs.records (Shared.Runtime.native inventory)
def actual := Input.Event.Costs.cost (Shared.Runtime.native inventory)
def credits := Input.Event.Costs.credits (Shared.Runtime.native inventory)

def inWindow (window : PublicFunction.Costs.Visits.Window sources → Bool) (bearer : Bool) :=
  PublicFunction.Costs.Visits.total sources ((records inventory).filter window) bearer

structure Receipt where
  private mk ::
  exposure : Shared.Exposure.Receipt inventory
  exposure_exact : exposure = Shared.Exposure.generate inventory
  material : ∀ bearer good,
    (current (Shared.Exposure.endpoint inventory).1 (Shared.Exposure.endpoint inventory).2.inputs).stock bearer good +
      actual inventory bearer (.operating good) + actual inventory bearer (.debtPayment good) =
    (current epoch inventory.inputs).stock bearer good + credits inventory bearer good
  clock : ∀ bearer, actual inventory bearer .elapsed =
    (current (Shared.Exposure.endpoint inventory).1 (Shared.Exposure.endpoint inventory).2.inputs).clock -
      (current epoch inventory.inputs).clock
  nonnegative : ∀ bearer, PublicFunction.Costs.BoundedBy 0 (actual inventory bearer)
  windows_nonnegative : ∀ window bearer, PublicFunction.Costs.BoundedBy 0 (inWindow inventory window bearer)

def generate : Receipt inventory :=
  ⟨Shared.Exposure.generate inventory, rfl,
    Input.Event.Costs.material_balance (Shared.Runtime.native inventory),
    Input.Event.Costs.elapsed_exact (Shared.Runtime.native inventory),
    PublicFunction.Costs.Visits.total_nonnegative sources (records inventory),
    fun window => PublicFunction.Costs.Visits.total_nonnegative sources ((records inventory).filter window)⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Costs
