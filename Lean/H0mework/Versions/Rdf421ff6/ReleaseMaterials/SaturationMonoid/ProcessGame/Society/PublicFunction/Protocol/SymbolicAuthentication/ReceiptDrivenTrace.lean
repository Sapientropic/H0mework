import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenMaterialization

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenTrace
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource

def response (reading : Fin (code .normal).signals) : Rule (code .normal) where
  work := ⟨fun key _ => if key.1 = 1 ∧ key.2 = reading then RequestResponse.work key.1 key.2 else [], by
    apply (code .normal).every_local_policy_is_enumerated
    intro key _
    split
    · exact RequestResponse.work_supported key.1 key.2
    · exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun key _ => if key.1 = 1 ∧ key.2 = reading then RequestResponse.activation key.1
    else ⟨none, List.mem_cons_self⟩

def ruleAt (index : Nat) : Rule (code .normal) :=
  if index = 6 then response 1 else if index = 10 then response 2
  else (programme .normal)[index]?.getD (quiet .normal)

def moveAt (index : Nat) : Move (code .normal) :=
  if index = 5 then some ⟨.deliver 0, by simp [code]⟩
  else if index = 9 then some ⟨.deliver 1, by simp [code]⟩ else none

def slots : ReceiptDrivenMaterialization.Slots (model .normal) := (List.range 16).map fun index =>
  ⟨ruleAt index, moveAt index, fun _ => []⟩
def stages := ReceiptDrivenMaterialization.extend (model .normal) [] slots

theorem every_literal_slot_is_generated_by_its_original_fresh_receipt_and_actual_input :
    ReceiptDrivenMaterialization.verify (model .normal) (start .normal 16) vocabulary (encoding .normal) (law .normal) 1
      (EagerDelivery.callback (start .normal 16))
      (ReceiptDrivenRun.template (model .normal) (start .normal 16) (programme .normal)) [] (fun _ => []) slots = true := by decide +kernel

def terminal := ReceiptDrivenRun.run (model .normal) (start .normal 16) vocabulary (encoding .normal) (law .normal) 1
  [] stages (ReceiptDrivenMaterialization.finalPending (model .normal) (fun _ => []) slots)
  (EagerDelivery.callback (start .normal 16))

theorem actual_state_is_the_verified_source_trace : (actual .normal).state = terminal.state := by
  unfold actual
  exact (ReceiptDrivenMaterialization.verified_slots_are_the_original_dynamic_executor (model .normal) (start .normal 16)
    vocabulary (encoding .normal) (law .normal) 1 (EagerDelivery.callback (start .normal 16))
    (ReceiptDrivenRun.template (model .normal) (start .normal 16) (programme .normal)) [] (fun _ => []) slots
    every_literal_slot_is_generated_by_its_original_fresh_receipt_and_actual_input).1

theorem actual_status_is_the_verified_source_trace : (actual .normal).status = terminal.status := by
  unfold actual
  exact (ReceiptDrivenMaterialization.verified_slots_are_the_original_dynamic_executor (model .normal) (start .normal 16)
    vocabulary (encoding .normal) (law .normal) 1 (EagerDelivery.callback (start .normal 16))
    (ReceiptDrivenRun.template (model .normal) (start .normal 16) (programme .normal)) [] (fun _ => []) slots
    every_literal_slot_is_generated_by_its_original_fresh_receipt_and_actual_input).2.1

theorem actual_history_is_the_verified_source_trace : (actual .normal).state.past = stages := by
  rw [actual_state_is_the_verified_source_trace]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenTrace
