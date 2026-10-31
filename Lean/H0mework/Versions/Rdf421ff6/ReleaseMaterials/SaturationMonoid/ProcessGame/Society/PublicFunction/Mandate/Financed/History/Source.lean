import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.History.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.History

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Mandate.Source (Port)

/-- A financial responsibility is selected from the current holder and
original account, independently of the last authorization command. -/
def source (fuel : ℚ) : OutstandingSource Bool Good Port (State Bool Unit) Unit :=
  { Repair.sourceWithFuel fuel with
    completionReport := fun current =>
      if current.technology.holder = none then Repair.report current
      else (Response.produce base scope current).report }

def bound (fuel : ℚ) : BoundSource base scope := ⟨source fuel, rfl⟩
abbrev input (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.input (source fuel) inputs
abbrev currentAt (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.currentAt (source fuel) inputs
abbrev actualExecution (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.actualExecution (source fuel) inputs
abbrev trailAt (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.trailAt (source fuel) inputs

theorem zero_financial_genesis (fuel : ℚ) (inputs : List (List Action)) :
    (input fuel inputs).initial.claims = fun _ _ _ => 0 := rfl

theorem unseated_has_no_authorization_input (fuel : ℚ) (current : Current)
    (unseated : current.technology.holder = none) : (source fuel).incoming? current = none := by
  change Repair.authorizationIncoming current = none
  unfold Repair.authorizationIncoming
  rw [unseated]
  rfl

theorem every_completed_unseated_history_emits_its_financial_residual
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none) :
    (actualExecution fuel inputs (depth + 1)).submitted = Repair.word (currentAt fuel inputs (depth + 2)) := by
  rw [OutstandingSource.History.residual_is_actually_emitted _ _ depth observed]
  unfold OutstandingSource.decideAt
  rw [unseated_has_no_authorization_input fuel _ unseated, dif_pos complete]
  change (if (currentAt fuel inputs (depth + 2)).technology.holder = none then
    Repair.report (currentAt fuel inputs (depth + 2)) else
    (Response.produce base scope (currentAt fuel inputs (depth + 2))).report).word = _
  rw [if_pos unseated]
  rfl

theorem every_completed_unseated_history_writes_its_financial_residual
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none) :
    (OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).val =
      Repair.report (currentAt fuel inputs (depth + 2)) := by
  rw [(OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).property]
  change OutstandingSource.History.reportAt (source fuel) inputs (currentAt fuel inputs (depth + 2)) = _
  unfold OutstandingSource.History.reportAt OutstandingSource.History.report
  rw [OutstandingSource.History.ordinal_exact, if_neg (by omega), List.getElem?_eq_none (by omega)]
  unfold OutstandingSource.decideAt
  rw [unseated_has_no_authorization_input fuel _ unseated, dif_pos complete]
  change (if (currentAt fuel inputs (depth + 2)).technology.holder = none then
    Repair.report (currentAt fuel inputs (depth + 2)) else
    (Response.produce base scope (currentAt fuel inputs (depth + 2))).report) = _
  rw [if_pos unseated]

theorem original_refusals_and_repair_requests_are_actual
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none)
    (positive : 0 < Repayment.balance position (currentAt fuel inputs (depth + 2)))
    (failed : ¬ Repayment.Ready law position (currentAt fuel inputs (depth + 2)))
    (order : Repair.Order (currentAt fuel inputs (depth + 2)))
    (present : order ∈ Repair.orders (currentAt fuel inputs (depth + 2))) :
    order.failed ∈ (actualExecution fuel inputs (depth + 1)).interpreted.items ∧
    ¬ law.Valid order.failed.before order.failed.request ∧
    order.request ∈ (actualExecution fuel inputs (depth + 1)).submitted := by
  have emitted := every_completed_unseated_history_emits_its_financial_residual fuel inputs depth observed complete unseated
  change order.failed ∈ law.rawItems (currentAt fuel inputs (depth + 2))
    (actualExecution fuel inputs (depth + 1)).submitted ∧ _
  rw [emitted]
  have actual := Repair.every_order_has_a_real_prefix_refusal _ order positive failed
  exact ⟨actual.1, actual.2, Repair.every_order_is_an_actual_requested_suffix _ order present positive failed⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.History
