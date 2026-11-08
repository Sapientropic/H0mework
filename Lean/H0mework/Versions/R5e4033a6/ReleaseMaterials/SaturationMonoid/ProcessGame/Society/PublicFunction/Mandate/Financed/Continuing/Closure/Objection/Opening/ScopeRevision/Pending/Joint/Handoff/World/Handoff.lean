import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Inventory

/-! An actual later review transports every old cohort and every native
birth of the outgoing epoch into the new source's own after-cut. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.BalanceConservation
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (fresh : Handoff.Ready epoch.bound inventory.inputs)

inductive Result where
  | private revised (fresh : Handoff.Ready epoch.bound inventory.inputs)
      (selected : Handoff.choose epoch.bound inventory.inputs = some fresh)
      (next : Inventory (Epoch.ofFresh fresh)) (exact : next = handoff inventory fresh)
  | private blocked (absent : Handoff.choose epoch.bound inventory.inputs = none)
      (reason : Handoff.Blocked epoch.bound inventory.inputs)

def generate : Result inventory :=
  match selected : Handoff.choose epoch.bound inventory.inputs with
  | some fresh => .revised fresh selected (handoff inventory fresh) rfl
  | none => .blocked selected (Handoff.every_failed_handoff_has_an_actual_reason _ _ selected)

abbrev Packet := Sigma Inventory

def Result.packet : Result inventory → Packet
  | .revised fresh _ next _ => ⟨Epoch.ofFresh fresh,next⟩
  | .blocked .. => ⟨epoch,inventory⟩

def Result.financialRun (result : Result inventory) :
    (Financial.Family.process sources).Run inventory.finance.current (result.packet inventory).2.finance.current := by
  cases result
  next fresh selected next same => subst next; exact handoffFinancialRun inventory fresh
  next absent reason => exact .nil

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
