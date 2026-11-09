import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers.Plan
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Acceptance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root
open Abolition.Root.Registered Quantifiers.Joint

noncomputable section

theorem the_original_financial_account_contains_one_existing_slot :
    (Selected.before Fixture.seed).current.slots.length = 1 := by
  have original := congrArg List.length (Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained
    Fixture.seed.input Fixture.seed.depth Fixture.seed.count (Background.account Fixture.seed)).1
  simp only [List.length_map] at original
  exact original.trans ((congrArg (fun state => state.current.slots.length)
    Quantifiers.Joint.Consumers.Compact.live_native_account).trans
      Quantifiers.Joint.Consumers.Compact.original_slot_count)

theorem the_native_execution_does_not_create_a_second_slot :
    (Selected.after Fixture.seed Fixture.grossClaim).current.slots.length = 1 := by
  have same := congrArg List.length
    (Selected.the_same_repair_neither_reissues_nor_deletes_any_original_claim Fixture.seed Fixture.grossClaim)
  simp only [List.length_map] at same
  exact same.trans the_original_financial_account_contains_one_existing_slot

def originalSettlement : Request Bool Bool Bool Unit Unit := ⟨false,[],false,[],.settle () false true 1⟩

theorem the_original_loan_has_its_actual_settlement_item_in_the_same_new_inventory :
    ∃ item ∈ Selected.items Fixture.seed Fixture.grossClaim,
      (item.instruction Fixture.seed.input Fixture.seed.depth Fixture.seed.count).request = originalSettlement := by
  have member : originalSettlement ∈ Selected.word Fixture.seed Fixture.grossClaim := by
    rw [the_selected_source_word_is_the_original_funded_plan]
    change originalSettlement ∈ Planning.Menu.materialPlan Fixture.seed Fixture.grossClaim Consumers.Compact.shared true () ++
      Settlement.word Fixture.seed
    apply List.mem_append_right
    rw [Consumers.Compact.original_financial_tail]
    exact List.mem_singleton_self _
  rw [← Selected.every_actual_requested_instruction_is_the_same_selected_instruction Fixture.seed Fixture.grossClaim] at member
  exact List.mem_map.mp member

theorem the_original_settlement_generates_one_actual_native_quota :
    ∃ item ∈ Selected.items Fixture.seed Fixture.grossClaim,
      ∃ movement : Epoch.Finance.Movement Fixture.seed.input Fixture.seed.depth Fixture.seed.count item,
        Epoch.Finance.readMovement Fixture.seed.input Fixture.seed.depth Fixture.seed.count item = some movement ∧
        movement.quantity = 1 ∧
        (Epoch.Finance.allocate Fixture.seed.input Fixture.seed.depth Fixture.seed.count item movement
          (Selected.before Fixture.seed)).used Fixture.seed.input Fixture.seed.depth Fixture.seed.count +
        (Epoch.Finance.allocate Fixture.seed.input Fixture.seed.depth Fixture.seed.count item movement
          (Selected.before Fixture.seed)).remaining = 1 := by
  obtain ⟨item,original,request⟩ := the_original_loan_has_its_actual_settlement_item_in_the_same_new_inventory
  have accepted := Selected.no_actual_item_is_rejected_by_its_native_financial_interpreter Fixture.seed Fixture.grossClaim item original
  have operation : (item.instruction Fixture.seed.input Fixture.seed.depth Fixture.seed.count).request.operation =
      .settle () false true 1 := congrArg Request.operation request
  have produced : (Epoch.Finance.readMovement Fixture.seed.input Fixture.seed.depth Fixture.seed.count item).isSome = true := by
    unfold Epoch.Finance.readMovement
    simp only [dif_pos accepted]
    split <;> simp_all
  obtain ⟨movement,generated⟩ := Option.isSome_iff_exists.mp produced
  have amount : movement.quantity = 1 := by
    have same := operation.symm.trans movement.operation
    cases kind : movement.kind with
    | payment =>
        rw [kind] at same
        exact (congrArg (fun op : Operation Bool Bool Unit Unit =>
          match op with | .settle _ _ _ quantity => quantity | _ => 0) same).symm
    | assignment => rw [kind] at same; cases same
  exact ⟨item,original,movement,generated,amount,
    (Epoch.Finance.one_actual_movement_has_one_quota Fixture.seed.input Fixture.seed.depth Fixture.seed.count
      item movement (Selected.before Fixture.seed)).trans amount⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Consumers
