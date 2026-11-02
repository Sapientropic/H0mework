import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Physics
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Payment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

theorem the_original_common_word_has_no_native_financial_mutation :
    Settlement.NonFinancial Control.Scenario.commonWork := by decide +kernel

theorem the_original_initial_operation_has_no_native_financial_mutation
    (operation : Actual.Operation input 0 count 0 0 (Actual.initial input 0 count)) :
    Settlement.NonFinancial (operation.word input 0 count 0 0) := by
  cases operation with
  | migration plan selected =>
      have original : Actual.origin input 0 count = Control.Scenario.seed :=
        the_original_physical_seed_is_the_actual_capital_successor
      rw [original, the_original_member_inventory_is_generated_before_the_trial] at plan
      exact ((a_zero_length_renewal_cannot_pay_the_original_members _).false plan).elim
  | renewal word phase checked => cases phase
  | repair cause attempt =>
      have remaining : (Actual.initial input 0 count).remaining = Repair.alphabet input Control.Scenario.seed := by
        change Repair.alphabet input (Actual.origin input 0 count) = _
        exact congrArg (Repair.alphabet input) the_original_physical_seed_is_the_actual_capital_successor
      have original := Eq.mp (congrArg (fun xs => attempt.request ∈ xs) remaining) attempt.original
      change attempt.request ∈ Control.Scenario.commonWork ++ Control.Scenario.commonWork at original
      intro request present
      obtain rfl := List.mem_singleton.mp present
      exact the_original_common_word_has_no_native_financial_mutation _ ((List.mem_append.mp original).elim id id)

theorem the_original_first_requests_have_no_native_financial_mutation :
    Settlement.NonFinancial (Compile.requests input 0 count 0 0 (Actual.initial input 0 count)
      (Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
        (.primitive Control.Scenario.ownerPresent))) := by
  rcases the_initial_opcode_is_an_advance_or_the_original_primitive with advance | primitive
  · rw [advance]
    unfold Compile.requests Compile.compile
    cases Actual.dispatch input 0 count 0 0 (Actual.initial input 0 count) with
    | automatic generated =>
        exact the_original_initial_operation_has_no_native_financial_mutation generated.operation
    | refusal obstruction source => intro request absent; cases absent
  · rw [primitive]
    unfold Compile.requests
    simp only [Compile.compile]
    cases Actual.inspectPrimitive input (Actual.initial input 0 count) Control.Scenario.ownerPresent <;>
      intro request present <;> obtain rfl := List.mem_singleton.mp present <;> trivial

theorem the_original_first_native_items_have_no_financial_mutation :
    ∀ item ∈ Macro.Inventory.items (review := none) input 0 count 0 0 Physical.initial
      (.primitive Control.Scenario.ownerPresent),
      Native.Payment.NonFinancial (item.instruction input 0 count).request.operation := by
  have inventory := Macro.Inventory.inventory_is_the_literal_physical_execution (review := none)
    input 0 count 0 0 Physical.initial (.primitive Control.Scenario.ownerPresent)
  have requests :
      (Macro.Inventory.items (review := none) input 0 count 0 0 Physical.initial
        (.primitive Control.Scenario.ownerPresent)).map (fun item => (item.instruction input 0 count).request) =
      Compile.requests input 0 count 0 0 (Actual.initial input 0 count)
        (Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
          (.primitive Control.Scenario.ownerPresent)) := by
    calc
      _ = ((Macro.Inventory.items (review := none) input 0 count 0 0 Physical.initial
          (.primitive Control.Scenario.ownerPresent)).map (Epoch.Finance.ActualItem.instruction input 0 count)).map
          ExecutionItem.request := by simp only [List.map_map]; rfl
      _ = _ := (congrArg (List.map ExecutionItem.request) inventory).trans
        (Compile.compiled_requests_are_exactly_interpreted input 0 count 0 0 (Actual.initial input 0 count) _)
  intro item original
  have member : (item.instruction input 0 count).request ∈
      (Macro.Inventory.items (review := none) input 0 count 0 0 Physical.initial
        (.primitive Control.Scenario.ownerPresent)).map (fun item => (item.instruction input 0 count).request) :=
    List.mem_map.mpr ⟨item, original, rfl⟩
  rw [requests] at member
  have safe := the_original_first_requests_have_no_native_financial_mutation _ member
  cases operation : (item.instruction input 0 count).request.operation <;>
    simp_all only [Native.Payment.NonFinancial, Settlement.NonFinancialRequest]

theorem the_closed_original_account_is_the_same_native_macro_base (nature : RequestAt) :
    (closedOriginal nature).account = Epoch.Finance.Future.Installed.initial input 0 count 0 count := by
  have original := the_closed_original_account_is_the_literal_source_prefix_account nature
  have complete := Macro.Continuation.completed_event_is_the_literal_next_input_seed
    (review := none) input 0 count 0 0 0 count Physical.initial (.primitive Control.Scenario.ownerPresent)
  have folded := Macro.Continuation.inventory_position_is_the_same_original_fold
    (review := none) input 0 count 0 0 0 count Physical.initial (.primitive Control.Scenario.ownerPresent)
    (Macro.Inventory.items (review := none) input 0 count 0 0 Physical.initial
      (.primitive Control.Scenario.ownerPresent)).length
  have noChange := Native.Payment.the_original_nonfinancial_inventory_keeps_the_native_account
    (Macro.Inventory.items (review := none) input 0 count 0 0 Physical.initial
      (.primitive Control.Scenario.ownerPresent))
    (Epoch.Finance.Future.Installed.initial input 0 count 0 count)
    the_original_first_native_items_have_no_financial_mutation
  rw [List.take_length] at folded
  exact original.trans (complete.trans (folded.trans noChange))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
