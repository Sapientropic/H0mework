import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalWirePrivacy
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.ArrivalBisimulationConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalWireConsumer
open Lean Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ArrivalWirePrivacy

theorem accumulated_state_is_the_actual_successor {plan : Plan}
    (prior : Consume.State plan × List Json) (commands : List Json) :
    (commands.foldl accumulate prior).1 = commands.foldl Wire.advance prior.1 := by
  induction commands generalizing prior with
  | nil => rfl
  | cons command rest ih => exact ih (accumulate prior command)

theorem actual_execution_keeps_its_own_private_frame_and_original_admissions
    (larger : Bool) (request source : Json) (commands : Array Json)
    (first : History.Execution larger) (execution : Wire.Execution larger)
    (sourceRead : request.getObjVal? "source" = .ok source)
    (eventsRead : request.getObjValAs? (Array Json) "events" = .ok commands)
    (restored : History.restore larger source [] = .ok first)
    (generated : Wire.execute larger request = .ok execution) :
    ArrivalDeliveryLedger.Tracked execution.state.service ∧
      Supply.Privacy.ownFrame execution.state.service.session.current =
        Supply.Privacy.ownFrame first.state.service.session.current ∧
      first.state.service.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
        execution.state.service.account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  rw [original_execute_is_its_exact_fold larger request source commands first sourceRead eventsRead restored] at generated
  cases Except.ok.inj generated
  have native := ArrivalDeliveryLedger.json_word_is_tracked first.state
    (ArrivalDeliveryLedger.restored_source_is_tracked larger source [] first restored) commands.toList
  have privateFrame := ArrivalBisimulationConsumer.every_json_word_keeps_its_own_private_frame first.state commands.toList
  have admissions := ArrivalBisimulationConsumer.every_json_word_keeps_every_original_financial_admission first.state commands.toList
  simpa only [← Array.foldl_toList, accumulated_state_is_the_actual_successor] using ⟨native, privateFrame, admissions⟩

def arrival : Json := Json.mkObj [("kind", toJson "arrival"), ("quantity", toJson (3 : Nat))]
def malformed : Json := Json.mkObj [("kind", toJson "arrival"), ("quantity", toJson "three")]

theorem the_actual_fresh_arrival_is_distinct_from_blocked {plan : Plan} (state : Consume.State plan)
    (fresh : state.spent = false) :
    (Wire.render state arrival).getObjVal? "status" = .ok (toJson "ARRIVED") ∧
      (Wire.advance state arrival).spent = true ∧
      (Wire.advance state arrival).service.account = state.service.account := by
  have parsed : Wire.eventOfJson arrival = .ok (.arrival 3) := rfl
  have accepted : (!state.spent && decide (((3 : Nat) : ℚ) = Effect.quantity)) = true := by
    rw [fresh, Effect.original_source_pays_three_units_and_six_steps.1]
    decide +kernel
  refine ⟨?_, ?_, Consume.original_account_is_preserved state 3⟩
  · simp only [Wire.render, parsed, accepted]
    rfl
  · change (Consume.arrival state 3).spent = true
    simp only [Consume.arrival, accepted]
    rfl

theorem replay_is_blocked_without_a_new_source_debit {plan : Plan} (state : Consume.State plan)
    (used : state.spent = true) :
    Wire.advance state arrival = state ∧
      (Wire.render state arrival).getObjVal? "status" = .ok (toJson "BLOCKED") ∧
      (Wire.render state arrival).getObjVal? "sourceRows" = .ok (Json.arr #[]) ∧
      (Wire.render state arrival).getObjVal? "debit" = .ok (Json.arr #[]) := by
  have parsed : Wire.eventOfJson arrival = .ok (.arrival 3) := rfl
  refine ⟨?_, ?_⟩
  · change Consume.arrival state 3 = state
    exact Consume.no_repeated_credit state used 3
  · simp only [Wire.render, parsed, used, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    exact ⟨rfl, rfl, rfl⟩

theorem malformed_input_keeps_the_entire_state {plan : Plan} (state : Consume.State plan) :
    Wire.advance state malformed = state := rfl

theorem deleting_the_source_prevents_execution (larger : Bool) (request : Json) (message : String)
    (missing : request.getObjVal? "source" = .error message) :
    Wire.execute larger request = .error message ∧ Wire.actual larger request = .error message := by
  have refused : Wire.execute larger request = .error message := by
    simp only [Wire.execute, missing, bind, Except.bind]
  exact ⟨refused, by simp only [Wire.actual, refused, bind, Except.bind]⟩

theorem no_event_is_not_a_successful_decision (larger : Bool) (request source : Json)
    (first : History.Execution larger) (sourceRead : request.getObjVal? "source" = .ok source)
    (eventsRead : request.getObjValAs? (Array Json) "events" = .ok #[])
    (restored : History.restore larger source [] = .ok first) :
    Wire.actual larger request = .error "ARRIVAL_EVENT_REQUIRED" := by
  unfold Wire.actual
  rw [original_execute_is_its_exact_fold larger request source #[] first sourceRead eventsRead restored]
  rfl

theorem the_full_public_state_json_does_not_reconstruct_the_private_current (visible : Current) :
    Supply.Privacy.Wire.stateJson (Supply.Privacy.rebuild visible 0) =
      Supply.Privacy.Wire.stateJson (Supply.Privacy.rebuild visible 1) ∧
      Supply.Privacy.rebuild visible 0 ≠ Supply.Privacy.rebuild visible 1 := by
  refine ⟨(actual_state_json_is_equal (Supply.Privacy.rebuild_twin visible 0)).symm.trans
    (actual_state_json_is_equal (Supply.Privacy.rebuild_twin visible 1)), ?_⟩
  intro equal
  have different := congrArg Supply.Privacy.ownFrame equal
  norm_num [Supply.Privacy.ownFrame, Supply.Privacy.rebuild] at different

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.ArrivalWireConsumer
