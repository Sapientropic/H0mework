import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Input

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "History" => Script Party Good Port Technology Instrument
local notation "Row" => Occurrence seed community × Balance

/-- Inherited visits advance by their original input. A payment at one
visit has no second position in the same chronological trace. -/
inductive HistoryWrites : History → History → List Row → Type
  | nil {past : History} {rows : List Row} : HistoryWrites past [] rows
  | next {past : History} {input : Input Party Good Port Technology Instrument}
      {remaining : History} {rows : List Row}
      (tail : HistoryWrites (past ++ [input]) remaining (atInput past input rows).result) :
      HistoryWrites past (input :: remaining) rows

def along : (past remaining : History) → (rows : List Row) → HistoryWrites past remaining rows
  | _, [], _ => .nil
  | past, input :: remaining, rows =>
    .next (along (past ++ [input]) remaining (atInput past input rows).result)

def historyQuantity (seed : Root.Cut Party Good Port Technology Instrument) (good : Good) :
    History → History → ℚ
  | _, [] => 0
  | past, input :: remaining =>
    inputQuantity (seed := seed) past input good + historyQuantity seed good (past ++ [input]) remaining

namespace HistoryWrites

def result : {past remaining : History} → {rows : List Row} → HistoryWrites past remaining rows → List Row
  | _, _, rows, .nil => rows
  | _, _, _, .next tail => result tail

def assignedForGood (good : Good) :
    {past remaining : History} → {rows : List Row} → HistoryWrites (community := community) past remaining rows → ℚ
  | _, _, _, .nil => 0
  | _, _, _, .next (past := past) (input := input) (rows := rows) tail =>
    (atInput past input rows).assignedForGood good + assignedForGood good tail

theorem every_good_respects_the_original_history (good : Good)
    {past remaining : History} {rows : List Row} (trace : HistoryWrites past remaining rows) :
    trace.assignedForGood good ≤ historyQuantity seed good past remaining := by
  induction trace with
  | nil => exact le_rfl
  | @next past input _ rows tail prior =>
    exact add_le_add (an_input_cannot_overdraw_any_good past input rows good) prior

theorem outstanding_and_assigned_eq_before (good : Good)
    {past remaining : History} {rows : List Row} (trace : HistoryWrites past remaining rows) :
    outstandingForGood good trace.result + trace.assignedForGood good = outstandingForGood good rows := by
  induction trace with
  | nil => exact add_zero _
  | @next past input _ rows tail prior =>
    let step := atInput past input rows
    have balance := ItemWrites.outstanding_and_assigned_eq_before good step
    change outstandingForGood good tail.result +
      (step.assignedForGood good + tail.assignedForGood good) = outstandingForGood good rows
    linarith only [prior, balance]

end HistoryWrites

theorem all_generated_shares_respect_each_units_original_history
    (past remaining : History) (rows : List Row) (good : Good) :
    (along past remaining rows).assignedForGood good ≤ historyQuantity seed good past remaining :=
  HistoryWrites.every_good_respects_the_original_history good (along past remaining rows)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
