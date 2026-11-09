import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Physical
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Balance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (past : Script Party Good Port Technology Instrument) (input : Input Party Good Port Technology Instrument)

local notation "Row" => Occurrence seed community × Balance
local notation "Pos" => Position seed past input

/-- A dependent calculation trace over original positions. Each cons uses the
generated allocation and feeds the exact resulting balances to the tail. -/
inductive ItemWrites : List Pos → List Row → Type
  | nil {rows : List Row} : ItemWrites [] rows
  | next {position : Pos} {later : List Pos} {rows : List Row}
      (tail : ItemWrites later (atItem seed past input position rows).changes.result) :
      ItemWrites (position :: later) rows

namespace ItemWrites

variable {past input}

def result : {positions : List Pos} → {rows : List Row} → ItemWrites (community := community) past input positions rows → List Row
  | _, rows, .nil => rows
  | _, _, .next tail => result tail

def assignedForGood (good : Good) :
    {positions : List Pos} → {rows : List Row} → ItemWrites (community := community) past input positions rows → ℚ
  | _, _, .nil => 0
  | _, _, .next (position := position) (rows := rows) tail =>
    (atItem seed past input position rows).changes.assignedForGood good + assignedForGood good tail

theorem every_good_respects_its_original_item_inventory (good : Good)
    {positions : List Pos} {rows : List Row} (trace : ItemWrites (community := community) past input positions rows) :
    trace.assignedForGood good ≤ (positions.map (fun position => unitQuantity past input position good)).sum := by
  induction trace with
  | nil => exact le_rfl
  | @next position later rows tail prior =>
    exact add_le_add (one_material_good_cannot_be_spent_twice past input position rows good) prior

theorem same_original_rows
    {positions : List Pos} {rows : List Row} (trace : ItemWrites (community := community) past input positions rows) :
    trace.result.map Prod.fst = rows.map Prod.fst := by
  induction trace with
  | nil => rfl
  | @next position _ rows _ prior =>
    exact prior.trans (Changes.result_origins (atItem seed past input position rows).changes)

theorem outstanding_and_assigned_eq_before (good : Good)
    {positions : List Pos} {rows : List Row} (trace : ItemWrites (community := community) past input positions rows) :
    outstandingForGood good trace.result + trace.assignedForGood good = outstandingForGood good rows := by
  induction trace with
  | nil => exact add_zero _
  | @next position _ rows tail prior =>
    let step := atItem seed past input position rows
    have balance := Changes.outstanding_and_assigned_eq_before (fun origin => origin.key.2.2 = good) step.changes
    change outstandingForGood good tail.result +
      (step.changes.assignedForGood good + tail.assignedForGood good) = outstandingForGood good rows
    linarith only [prior, balance]

end ItemWrites

private def forPositions : (positions : List Pos) → (rows : List Row) → ItemWrites past input positions rows
  | [], _ => .nil
  | position :: remaining, rows =>
    .next (forPositions remaining (atItem seed past input position rows).changes.result)

abbrev itemPositions (past : Script Party Good Port Technology Instrument) (input : Input Party Good Port Technology Instrument) :
    List (Position seed past input) :=
  List.finRange (Boundary.Actual.items (Quantities.Execution.endAt seed past) input).length

def atInput (past : Script Party Good Port Technology Instrument) (input : Input Party Good Port Technology Instrument)
    (rows : List Row) : ItemWrites past input (itemPositions (seed := seed) past input) rows :=
  forPositions past input _ rows

theorem no_original_items_keeps_rows (rows : List Row)
    (empty : Boundary.Actual.items (Quantities.Execution.endAt seed past) input = []) :
    (atInput past input rows).result = rows ∧ ∀ good, (atInput past input rows).assignedForGood good = 0 := by
  have noPositions : itemPositions (seed := seed) past input = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [itemPositions, List.length_finRange, empty, List.length_nil]
  unfold atInput
  rw [noPositions]
  exact ⟨rfl, fun _ => rfl⟩

theorem each_input_visits_every_original_position_once :
    (itemPositions (seed := seed) past input).Nodup ∧ ∀ position : Pos, position ∈ itemPositions (seed := seed) past input :=
  ⟨List.nodup_finRange _, List.mem_finRange⟩

def inputQuantity (good : Good) : ℚ :=
  ((itemPositions (seed := seed) past input).map (fun position => unitQuantity past input position good)).sum

theorem an_input_cannot_overdraw_any_good (rows : List Row) (good : Good) :
    (atInput past input rows).assignedForGood good ≤ inputQuantity (seed := seed) past input good :=
  ItemWrites.every_good_respects_its_original_item_inventory good (atInput past input rows)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
