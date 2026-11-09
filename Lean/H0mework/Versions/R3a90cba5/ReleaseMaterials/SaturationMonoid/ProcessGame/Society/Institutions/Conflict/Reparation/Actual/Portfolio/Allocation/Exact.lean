import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Greedy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

private theorem min_successive (stock first rest : ℚ) (rest_nonnegative : 0 ≤ rest) :
    min stock first + min (stock - min stock first) rest = min stock (first + rest) := by
  rcases le_total stock first with enough | little
  · rw [min_eq_left enough, sub_self, min_eq_left rest_nonnegative, add_zero,
      min_eq_left (enough.trans (le_add_of_nonneg_right rest_nonnegative))]
  · rw [min_eq_right little]
    rcases le_total (stock - first) rest with enough | littleRest
    · rw [min_eq_left enough, min_eq_left (by linarith)]
      ring
    · rw [min_eq_right littleRest, min_eq_right (by linarith)]

theorem allocation_attains_the_joint_tight_bound
    (offer : Offer seed) (available : Capacity offer) (rows : List Row) (key : Key Party Good) :
    (scan offer available rows).changes.assignedFor key =
      min (available.balance key).remaining (demand offer key rows) := by
  induction rows generalizing available with
  | nil => exact (min_eq_right ((available.balance key).nonnegative)).symm
  | cons row remaining prior =>
    let head := allot offer available row
    let tail := scan offer head.remainder remaining
    let firstAssigned := if row.1.key = key then head.change.amount else 0
    let firstDue := if row.1.key = key then eligible offer row else 0
    have exactHead : firstAssigned = min (available.balance key).remaining firstDue := by
      by_cases same : row.1.key = key
      · have exactRow := head.amount_exact
        rw [same] at exactRow
        simpa only [firstAssigned, firstDue, if_pos same] using exactRow
      · simp only [firstAssigned, firstDue, if_neg same, min_eq_right ((available.balance key).nonnegative)]
    have left : (head.remainder.balance key).remaining = (available.balance key).remaining - firstAssigned :=
      available.spend_exact row.1.key key head.change.amount head.change.amount_nonnegative head.available_bound
    change firstAssigned + tail.changes.assignedFor key =
      min (available.balance key).remaining (firstDue + demand offer key remaining)
    rw [prior head.remainder, left, exactHead]
    exact min_successive _ _ _ (demand_nonnegative offer key remaining)

theorem remainder_is_the_exact_unspent_delivery
    (offer : Offer seed) (available : Capacity offer) (rows : List Row) (key : Key Party Good) :
    ((scan offer available rows).remainder.balance key).remaining =
      max 0 ((available.balance key).remaining - demand offer key rows) := by
  have total := conserved offer available rows key
  rw [allocation_attains_the_joint_tight_bound offer available rows key] at total
  rcases le_total (available.balance key).remaining (demand offer key rows) with smaller | larger
  · rw [min_eq_left smaller] at total
    rw [max_eq_left (sub_nonpos.mpr smaller)]
    linarith only [total]
  · rw [min_eq_right larger] at total
    rw [max_eq_right (sub_nonneg.mpr larger)]
    linarith only [total]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
