import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Offer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

def Changes.uses (offer : Offer seed) : {rows : List Row} → Changes rows → Prop
  | _, .nil => True
  | _, .cons head tail => head.uses offer ∧ uses offer tail

structure Plan (offer : Offer seed) (rows : List Row) where
  changes : Changes rows
  remainder : Capacity offer
  original : changes.uses offer

/-- This is the original row order. Each head consumes its affordable share
and the tail receives only the unspent amount at that address. -/
def scan (offer : Offer seed) : Capacity offer → (rows : List Row) → Plan offer rows
  | available, [] => ⟨.nil, available, trivial⟩
  | available, row :: remaining =>
    let head := allot offer available row
    let tail := scan offer head.remainder remaining
    ⟨.cons head.change tail.changes, tail.remainder, ⟨head.fromOffer, tail.original⟩⟩

def allocate (offer : Offer seed) (rows : List Row) : Plan offer rows :=
  scan offer (Capacity.full offer) rows

def plan {key : Key Party Good} (receipt : SignedReceipt seed key) (rows : List Row) :
    Plan (Offer.singleton receipt) rows :=
  allocate (Offer.singleton receipt) rows

theorem conserved (offer : Offer seed) (available : Capacity offer) (rows : List Row)
    (key : Key Party Good) :
    ((scan offer available rows).remainder.balance key).remaining +
      (scan offer available rows).changes.assignedFor key = (available.balance key).remaining := by
  induction rows generalizing available with
  | nil => exact add_zero _
  | cons row remaining prior =>
    let first := allot offer available row
    let next := scan offer first.remainder remaining
    have tailExact := prior first.remainder
    have headExact := available.spend_exact row.1.key key first.change.amount
      first.change.amount_nonnegative first.available_bound
    change ((next.remainder.balance key).remaining + next.changes.assignedFor key) =
      (first.remainder.balance key).remaining at tailExact
    change (first.remainder.balance key).remaining =
      (available.balance key).remaining - (if row.1.key = key then first.change.amount else 0) at headExact
    change (next.remainder.balance key).remaining +
      ((if row.1.key = key then first.change.amount else 0) + next.changes.assignedFor key) =
        (available.balance key).remaining
    linarith only [tailExact, headExact]

theorem allocated_is_within_the_original_quantity (offer : Offer seed) (rows : List Row) (key : Key Party Good) :
    (allocate offer rows).changes.assignedFor key ≤ offer.quantity key := by
  have cap := conserved offer (Capacity.full offer) rows key
  change ((allocate offer rows).remainder.balance key).remaining +
    (allocate offer rows).changes.assignedFor key = offer.quantity key at cap
  exact (le_add_of_nonneg_left ((allocate offer rows).remainder.balance key).nonnegative).trans_eq cap

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
