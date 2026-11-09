import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Exact

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

def Changes.head {row : Row} {tail : List Row} : Changes (row :: tail) → Change row.1 row.2
  | .cons first _ => first

theorem scan_splits_at_the_original_prefix (offer : Offer seed) (available : Capacity offer)
    (front tail : List Row) :
    let initial := scan offer available front
    let rest := scan offer initial.remainder tail
    let together := scan offer available (front ++ tail)
    let parts := Changes.split front tail together.changes
    parts.1 = initial.changes ∧ parts.2 = rest.changes ∧ together.remainder = rest.remainder := by
  induction front generalizing available with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons row front prior =>
    let first := allot offer available row
    have later := prior first.remainder
    exact ⟨congrArg (Changes.cons first.change) later.1, later.2.1, later.2.2⟩

/-- The row at this original list position receives the exact remaining
amount after every earlier eligible row, truncated by its own balance. -/
theorem original_position_has_exact_FIFO_payment (offer : Offer seed) (available : Capacity offer)
    (front : List Row) (row : Row) (tail : List Row) :
    let together := scan offer available (front ++ row :: tail)
    let move := (Changes.split front (row :: tail) together.changes).2.head
    move.amount = min (max 0 ((available.balance row.1.key).remaining - demand offer row.1.key front))
      (eligible offer row) := by
  dsimp only
  rw [(scan_splits_at_the_original_prefix offer available front (row :: tail)).2.1]
  let initial := scan offer available front
  change (allot offer initial.remainder row).change.amount = _
  exact (allot offer initial.remainder row).amount_exact.trans
    (congrArg (fun quantity => min quantity (eligible offer row))
      (remainder_is_the_exact_unspent_delivery offer available front row.1.key))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
