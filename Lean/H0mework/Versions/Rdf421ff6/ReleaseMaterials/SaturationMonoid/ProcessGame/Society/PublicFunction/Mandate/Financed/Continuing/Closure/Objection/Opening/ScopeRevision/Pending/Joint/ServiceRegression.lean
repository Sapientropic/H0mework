import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
noncomputable section

abbrev ready := Pending.Regression.ready
abbrev ownSource := epochSource ready

def initialInventory := initial ready []
def served := submit ready initialInventory (epochWord ready (epochBefore ready))
def withoutUse := (epochWord ready (epochBefore ready)).filter fun action => match action.operation with | .use .. => false | _ => true
def unpaid := submit ready initialInventory withoutUse
def late := submit ready (submit ready initialInventory []) (epochWord ready (epochBefore ready))

def terminalFlags {originInputs : List (List Action)} (inventory : Inventory ready originInputs) :=
  (List.finRange ownSource.seed.task.slots.length).map fun index =>
    match (inventory.services index).state.current.slots with | [.terminal _] => true | _ => false

def remoteFlags {originInputs : List (List Action)} (inventory : Inventory ready originInputs) :=
  (List.finRange ownSource.seed.task.slots.length).map fun index =>
    match (inventory.services index).state.current.slots with
    | [.terminal archive] => archive.sourceEvent.inputOverride.isSome
    | _ => false

def kinds {originInputs : List (List Action)} (inventory : Inventory ready originInputs) :=
  inventory.objections.map fun resident => resident.history.state.current.history.map LifecycleEvent.kind

theorem the_new_actual_word_pays_all_original_native_services_and_creates_its_own_grant_and_claim :
    terminalFlags initialInventory = [false, false, false, false] ∧
    terminalFlags served = [true, true, true, true] ∧ remoteFlags served = [true, true, true, true] ∧
    served.grants.length = 1 ∧ kinds served = [[.admitted, .obligationTerminal]] := by decide +kernel

theorem deleting_payment_or_missing_the_original_window_does_not_settle_the_original_services :
    terminalFlags unpaid = [false, false, false, false] ∧
    terminalFlags late = [false, false, false, false] := by decide +kernel

theorem every_paid_original_service_is_natively_terminal (index : ownSource.Slot) :
    (served.services index).state.current.TerminalAt 0 := by
  apply ((served.services index).native_terminal_iff_recorded ownSource).mpr
  have paid : ∀ slot : ownSource.Slot,
      (OutstandingSource.History.NativeService.frameAt ownSource served.inputs (served.inputs.length + 2)).payments slot = some 2 := by
    decide +kernel
  exact ⟨2, paid index⟩

theorem the_first_archive_and_complete_native_state_are_preserved_after_response (index : ownSource.Slot) :
    ((advance ready served).services index).state = (served.services index).state :=
  original_service_terminal_archive_is_literal ready served (emit ready served) index (every_paid_original_service_is_natively_terminal index)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Regression
