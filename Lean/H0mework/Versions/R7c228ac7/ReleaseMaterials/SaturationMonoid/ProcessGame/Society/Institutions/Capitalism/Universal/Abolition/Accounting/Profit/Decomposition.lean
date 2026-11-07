import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (initial : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

/-- This is a signed net position at a checked controller's original addresses.
It is not gross repayment, and its complement is not declared independent. -/
def controlAt (item : ExecutionItem Party Good Port Technology Instrument) :
    Vector (Party := Party) (Good := Good) :=
  (transferAt law item).filter fun cell => sourceOwnerMarked law initial word item.index cell.1 = true

def otherTransferAt (item : ExecutionItem Party Good Port Technology Instrument) :
    Vector (Party := Party) (Good := Good) :=
  (transferAt law item).filter fun cell => sourceOwnerMarked law initial word item.index cell.1 = false

theorem every_original_position_is_in_exactly_one_transfer_component
    (item : ExecutionItem Party Good Port Technology Instrument) :
    controlAt law initial word item + otherTransferAt law initial word item = transferAt law item := by
  ext cell
  simp only [controlAt,otherTransferAt,Finsupp.add_apply,Finsupp.filter_apply]
  cases sourceOwnerMarked law initial word item.index cell.1 <;> simp

def controlIncome : Vector (Party := Party) (Good := Good) :=
  ((law.rawItems initial word).map (controlAt law initial word)).sum

def otherTransfers : Vector (Party := Party) (Good := Good) :=
  ((law.rawItems initial word).map (otherTransferAt law initial word)).sum

theorem actual_production_is_never_relabelled_as_control_income
    (item : ExecutionItem Party Good Port Technology Instrument) (operator : Party)
    (operation : item.request.operation = .produce operator) :
    controlAt law initial word item = 0 ∧ otherTransferAt law initial word item = 0 ∧
      productionAt law item = Financial.materialChange law item.before item.request := by
  simp only [controlAt,otherTransferAt,transferAt,productionAt,operation,Finsupp.filter_zero]
  trivial

theorem all_original_transfers_are_exhausted_without_double_counting :
    controlIncome law initial word + otherTransfers law initial word = transfers law (law.rawItems initial word) := by
  unfold controlIncome otherTransfers transfers
  induction law.rawItems initial word with
  | nil => simp only [List.map_nil,List.sum_nil,add_zero]
  | cons item rest inherited =>
      simp only [List.map_cons,List.sum_cons]
      have first := every_original_position_is_in_exactly_one_transfer_component law initial word item
      calc
        _ = (controlAt law initial word item + otherTransferAt law initial word item) +
            ((rest.map (controlAt law initial word)).sum + (rest.map (otherTransferAt law initial word)).sum) := by abel
        _ = transferAt law item + (rest.map (transferAt law)).sum := by rw [first,inherited]

theorem the_original_full_account_separates_production_transfer_and_control :
    fullIncome law (law.rawItems initial word) =
      production law (law.rawItems initial word) + otherTransfers law initial word + controlIncome law initial word := by
  rw [every_original_inventory_separates_production_and_existing_positions,
    ← all_original_transfers_are_exhausted_without_double_counting law initial word]
  abel

omit [DecidableEq Port] in
theorem the_original_financial_component_is_the_actual_claim_matrix_change
    (instrument : Instrument) (debtor holder : Party) :
    Financial.inventoryClaims law (law.rawItems initial word) (instrument,debtor,holder) =
      (law.next initial word).claims instrument debtor holder - initial.claims instrument debtor holder := by
  rw [Financial.inventory_claims_are_the_original_financial_delta]
  have actual := law.execute_financial_balance initial 0 word instrument debtor holder
  change (law.next initial word).claims instrument debtor holder = initial.claims instrument debtor holder +
    law.totalFinancialDelta (law.rawItems initial word) instrument debtor holder at actual
  linarith

omit [DecidableEq Port] in
theorem the_original_full_account_uses_its_actual_stock_and_financial_changes
    (person : Party) (good : Good) :
    fullIncome law (law.rawItems initial word) (person,good) =
      (law.next initial word).stock person good - initial.stock person good +
        Financial.value law (Financial.inventoryClaims law (law.rawItems initial word)) (person,good) := by
  simp only [fullIncome,Finsupp.add_apply]
  rw [Financial.inventory_material_is_the_original_net_flow]
  have actual := law.actual_next_material_balance initial word person good
  linarith

theorem a_nonzero_control_component_has_the_same_original_controller
    (item : ExecutionItem Party Good Port Technology Instrument) (person : Party) (good : Good)
    (nonzero : controlAt law initial word item (person,good) ≠ 0) :
    ∃ kernel ∈ originalControlImage law initial word,
      item.index ∈ originalControlIndices law initial word kernel ∧
      person = law.controller kernel.proposal.access.access.val.before.technology kernel.proposal.access.port ∧
      kernel.proposal.Checks law initial word := by
  have marked : sourceOwnerMarked law initial word item.index person = true := by
    by_contra absent
    exact nonzero (by simp only [controlAt,Finsupp.filter_apply,if_neg absent])
  exact an_owner_mark_is_its_original_controller_and_actual_position law initial word item.index person marked

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit
