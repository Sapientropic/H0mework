import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Accumulation
import Mathlib.Data.Rat.Floor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Reparation Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

abbrev MaterialCell (Party Good : Type) := Party × Good
abbrev payerCell (key : Key Party Good) : MaterialCell Party Good := (key.2.1, key.2.2)

local notation "Row" => Occurrence seed community × Balance
local notation "Cell" => MaterialCell Party Good

/-- Sum the actual open balances drawn on the same payer and good. -/
def cellDue (rows : List Row) (cell : Cell) : ℚ :=
  (rows.map fun row => if payerCell row.1.key = cell then row.2.remaining else 0).sum

theorem cellDue_nonnegative (rows : List Row) (cell : Cell) : 0 ≤ cellDue rows cell := by
  apply List.sum_nonneg
  rintro amount listed
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp listed
  split
  · exact row.2.nonnegative
  · exact le_rfl

theorem positive_cellDue_has_an_original_row (rows : List Row) (cell : Cell)
    (positive : 0 < cellDue rows cell) :
    ∃ row ∈ rows, payerCell row.1.key = cell ∧ 0 < row.2.remaining := by
  induction rows with
  | nil => simp [cellDue] at positive
  | cons row rest earlier =>
    by_cases key : payerCell row.1.key = cell
    · by_cases due : 0 < row.2.remaining
      · exact ⟨row, List.mem_cons_self, key, due⟩
      · have zero := le_antisymm (le_of_not_gt due) row.2.nonnegative
        have tail : 0 < cellDue rest cell := by
          simpa only [cellDue, List.map_cons, List.sum_cons, if_pos key, zero, zero_add] using positive
        obtain ⟨older, present, atCell, owing⟩ := earlier tail
        exact ⟨older, List.mem_cons_of_mem _ present, atCell, owing⟩
    · have tail : 0 < cellDue rest cell := by
        simpa only [cellDue, List.map_cons, List.sum_cons, if_neg key, zero_add] using positive
      obtain ⟨older, present, atCell, owing⟩ := earlier tail
      exact ⟨older, List.mem_cons_of_mem _ present, atCell, owing⟩

def Funds (rows : List Row) (spendable gain : Cell → ℚ) (cycles : Nat) : Prop :=
  ∀ cell, cellDue rows cell ≤ spendable cell + (cycles : ℚ) * gain cell

/-- On each owing payer and good, round the uncovered material up to
whole periods. A short account with zero gain is detected separately. -/
def fundingCycles (rows : List Row) (spendable gain : Cell → ℚ) : Nat :=
  ((rows.map fun row => payerCell row.1.key).dedup.map fun cell =>
    ⌈(cellDue rows cell - spendable cell) / gain cell⌉₊).foldr max 0

private theorem folded_max_le {values : List Nat} {n : Nat} :
    values.foldr max 0 ≤ n ↔ ∀ value ∈ values, value ≤ n := by
  induction values with
  | nil => simp
  | cons head tail earlier => simp [earlier]

theorem fundingCycles_le_iff_funds (rows : List Row) (spendable gain : Cell → ℚ)
    (stock_nonnegative : ∀ cell, 0 ≤ spendable cell) (gain_nonnegative : ∀ cell, 0 ≤ gain cell)
    (grows : ∀ cell, spendable cell < cellDue rows cell → 0 < gain cell) (n : Nat) :
    fundingCycles rows spendable gain ≤ n ↔ Funds rows spendable gain n := by
  unfold fundingCycles
  rw [folded_max_le]
  constructor
  · intro bound cell
    by_cases short : spendable cell < cellDue rows cell
    · obtain ⟨row, listed, atCell, _⟩ :=
        positive_cellDue_has_an_original_row rows cell ((stock_nonnegative cell).trans_lt short)
      have present : cell ∈ (rows.map fun row => payerCell row.1.key).dedup :=
        List.mem_dedup.mpr (List.mem_map.mpr ⟨row, listed, atCell⟩)
      have rounded := bound _ (List.mem_map_of_mem present)
      exact sub_le_iff_le_add'.mp ((div_le_iff₀ (grows cell short)).mp (Nat.ceil_le.mp rounded))
    · exact (le_of_not_gt short).trans
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (gain_nonnegative cell)))
  · intro covered value listed
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp listed
    apply Nat.ceil_le.mpr
    change (cellDue rows cell - spendable cell) / gain cell ≤ (n : ℚ)
    by_cases short : spendable cell < cellDue rows cell
    · exact (div_le_iff₀ (grows cell short)).mpr (sub_le_iff_le_add'.mpr (covered cell))
    · exact (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt short))
        (gain_nonnegative cell)).trans (Nat.cast_nonneg _)

/-- Only cells whose original spendable amount is short need a positive
net material gain. The bound ranges over the complete finite portfolio. -/
theorem finite_funding_iff_every_short_cell_grows (rows : List Row) (spendable gain : Cell → ℚ)
    (stock_nonnegative : ∀ cell, 0 ≤ spendable cell) (gain_nonnegative : ∀ cell, 0 ≤ gain cell) :
    (∃ n, Funds rows spendable gain n) ↔
      ∀ cell, spendable cell < cellDue rows cell → 0 < gain cell := by
  constructor
  · rintro ⟨n, covered⟩ cell short
    by_contra! never
    have extra : (n : ℚ) * gain cell ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) never
    linarith only [covered cell, short, extra]
  · intro grows
    exact ⟨fundingCycles rows spendable gain,
      (fundingCycles_le_iff_funds rows spendable gain stock_nonnegative gain_nonnegative grows _).mp le_rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
