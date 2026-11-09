import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

def outstandingWhere (select : Occurrence seed community → Prop) [DecidablePred select]
    (rows : List Row) : ℚ :=
  (rows.map (fun row => if select row.1 then row.2.remaining else 0)).sum

abbrev outstandingFor (key : Key Party Good) (rows : List Row) : ℚ :=
  outstandingWhere (fun origin => origin.key = key) rows

abbrev outstandingForGood (good : Good) (rows : List Row) : ℚ :=
  outstandingWhere (fun origin => origin.key.2.2 = good) rows

/-- The updated balances carry exactly the debits generated at their original
positions, also when restricted to any one address or material good. -/
theorem Changes.outstanding_and_assigned_eq_before
    (select : Occurrence seed community → Prop) [DecidablePred select]
    {rows : List Row} (moves : Changes rows) :
    outstandingWhere select moves.result + moves.assignedWhere select = outstandingWhere select rows := by
  induction moves with
  | nil => exact add_zero _
  | @cons row rows head tail prior =>
    by_cases counted : select row.1
    · simp only [outstandingWhere, Changes.result, Changes.assignedWhere, List.map_cons, List.sum_cons,
        if_pos counted, Change.after_exact]
      unfold outstandingWhere at prior
      linarith only [prior]
    · simpa only [outstandingWhere, Changes.result, Changes.assignedWhere, List.map_cons, List.sum_cons,
        if_neg counted, zero_add] using prior

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
