import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Exact

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument
local notation "History" => Script Party Good Port Technology Instrument

abbrev Position (seed : C) (past : History) (input : Proposal) :=
  Fin (Boundary.Actual.items (endAt seed past) input).length

abbrev originalItem (seed : C) (past : History) (input : Proposal) (position : Position seed past input) :=
  (Boundary.Actual.items (endAt seed past) input)[position]

/-- The offer is generated at one original list position. Every usable
share of every good retains this same signed material occurrence. -/
def itemOffer (seed : C) (past : History) (input : Proposal) (position : Position seed past input) : Offer seed :=
  fun key =>
    if paid : 0 < receiptCredit seed.native.input.law (originalItem seed past input position) key then
      some ⟨past, input, position, paid⟩
    else none

theorem item_offer_is_the_actual_signed_credit (seed : C) (past : History) (input : Proposal)
    (position : Position seed past input) (key : Key Party Good) :
    (itemOffer seed past input position).quantity key =
      receiptCredit seed.native.input.law (originalItem seed past input position) key := by
  by_cases paid : 0 < receiptCredit seed.native.input.law (originalItem seed past input position) key
  · simp only [Offer.quantity, itemOffer, dif_pos paid]
  · have zero := le_antisymm (le_of_not_gt paid)
      (receipt_nonnegative seed.native.input.law (originalItem seed past input position) key)
    simp only [Offer.quantity, itemOffer, dif_neg paid]
    exact zero.symm

theorem item_offer_identifies_its_exact_receipt (seed : C) (past : History) (input : Proposal)
    (position : Position seed past input) (key : Key Party Good) (receipt : SignedReceipt seed key)
    (selected : itemOffer seed past input position key = some receipt) :
    receipt.past = past ∧ receipt.input = input ∧ receipt.position.val = position.val := by
  unfold itemOffer at selected
  split at selected
  · cases Option.some.inj selected
    exact ⟨rfl, rfl, rfl⟩
  · contradiction

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

def atItem (seed : C) (past : History) (input : Proposal) (position : Position seed past input)
    {community : Party → Community} (rows : List (Occurrence seed community × Balance)) :
    Plan (itemOffer seed past input position) rows :=
  allocate (itemOffer seed past input position) rows

theorem each_item_conserves_the_original_delivery (past : History) (input : Proposal)
    (position : Position seed past input) (rows : List Row) (key : Key Party Good) :
    (((atItem seed past input position rows).remainder.balance key).remaining) +
      (atItem seed past input position rows).changes.assignedFor key =
      receiptCredit seed.native.input.law (originalItem seed past input position) key :=
  (conserved _ _ rows key).trans (item_offer_is_the_actual_signed_credit seed past input position key)

theorem each_item_attains_the_original_joint_capacity (past : History) (input : Proposal)
    (position : Position seed past input) (rows : List Row) (key : Key Party Good) :
    (atItem seed past input position rows).changes.assignedFor key =
      min (receiptCredit seed.native.input.law (originalItem seed past input position) key)
        (demand (itemOffer seed past input position) key rows) :=
  (allocation_attains_the_joint_tight_bound _ _ rows key).trans
    (congrArg (fun amount => min amount (demand (itemOffer seed past input position) key rows))
      (item_offer_is_the_actual_signed_credit seed past input position key))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
