import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Budget
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Posting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (itemPositions)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance
local notation "Cell" => MaterialCell Party Good

theorem dueFor_eq_zero_of_key_absent (rows : List Row) (key : Key Party Good)
    (absent : key ∉ rows.map (fun row => row.1.key)) :
    dueFor key rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rest earlier =>
    have same : row.1.key ≠ key := fun equal => absent (List.mem_cons.mpr (Or.inl equal.symm))
    have tail : key ∉ rest.map (fun row => row.1.key) := fun listed => absent (List.mem_cons_of_mem _ listed)
    simpa only [dueFor_is_the_keyed_sum, List.map_cons, List.sum_cons, if_neg same, zero_add] using earlier tail

private theorem split_cell_by_claim_key (rows : List Row) (key : Key Party Good) (cell : Cell) :
    cellDue rows cell =
      (if payerCell key = cell then dueFor key rows else 0) +
      cellDue (rows.filter fun row => decide (row.1.key ≠ key)) cell := by
  induction rows with
  | nil => simp [cellDue, dueFor_is_the_keyed_sum]
  | cons row rest earlier =>
    by_cases same : row.1.key = key
    · by_cases atCell : key.2 = cell <;>
        simp [cellDue, dueFor_is_the_keyed_sum, same, atCell] at earlier ⊢ <;> linarith only [earlier]
    · by_cases atCell : key.2 = cell <;>
        simp [cellDue, dueFor_is_the_keyed_sum, same, atCell] at earlier ⊢ <;> linarith only [earlier]

theorem dueFor_le_its_original_cell (rows : List Row) (key : Key Party Good) :
    dueFor key rows ≤ cellDue rows (payerCell key) := by
  rw [split_cell_by_claim_key rows key, if_pos rfl]
  exact le_add_of_nonneg_right (cellDue_nonnegative _ _)

theorem cellDue_after_clearing_one_key {before after : List Row} (key : Key Party Good) (cell : Cell)
    (cleared : dueFor key after = 0)
    (others : after.filter (fun row => decide (row.1.key ≠ key)) =
      before.filter (fun row => decide (row.1.key ≠ key))) :
    cellDue after cell = cellDue before cell -
      (if payerCell key = cell then dueFor key before else 0) := by
  rw [split_cell_by_claim_key after key, split_cell_by_claim_key before key, cleared, others]
  split <;> ring

theorem a_material_free_tick_keeps_the_original_balances
    (answers : ReceiptAnswers seed) {past : Reparation.Actual.Script Party Good Port Technology Instrument}
    {input : Reparation.Actual.Input Party Good Port Technology Instrument} (state : State seed community past)
    (empty : Boundary.Actual.items (endAt seed past) input = []) :
    (Settlement.writeTick answers state input).stack.balances = state.stack.balances := by
  have noItems : itemPositions (seed := seed) past input = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [itemPositions, List.length_finRange, empty, List.length_nil]
  have noOpenings : openings seed community past input = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ empty]
    rfl
  rw [Settlement.writeTick_balances, noItems, Settlement.writePositions, posted_balances, noOpenings]
  simp only [List.map_nil, List.append_nil]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
