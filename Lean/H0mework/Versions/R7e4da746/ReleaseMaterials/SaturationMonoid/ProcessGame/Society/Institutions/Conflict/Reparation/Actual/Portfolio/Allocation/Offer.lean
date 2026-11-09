import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Spine

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

abbrev Offer (seed : Root.Cut Party Good Port Technology Instrument) :=
  (key : Key Party Good) → Option (SignedReceipt seed key)

namespace Offer

def quantity (offer : Offer seed) (key : Key Party Good) : ℚ :=
  match offer key with
  | none => 0
  | some receipt => receipt.quantity

theorem nonnegative (offer : Offer seed) (key : Key Party Good) : 0 ≤ offer.quantity key := by
  unfold quantity
  split
  · exact le_rfl
  · exact SignedReceipt.positive _ |>.le

def singleton {key : Key Party Good} (receipt : SignedReceipt seed key) : Offer seed :=
  fun selected =>
    if same : selected = key then some (same.symm ▸ receipt) else none

end Offer

/-- Local allocation fuel for a single material occurrence, separated by the
original victim, debtor and good. -/
structure Capacity (offer : Offer seed) where
  balance : Key Party Good → Balance
  within : ∀ key, (balance key).remaining ≤ offer.quantity key

namespace Capacity

variable {offer : Offer seed}

def full (offer : Offer seed) : Capacity offer :=
  ⟨fun key => ⟨offer.quantity key, offer.nonnegative key⟩, fun _ => le_rfl⟩

def spend (available : Capacity offer) (key : Key Party Good) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (within : amount ≤ (available.balance key).remaining) : Capacity offer where
  balance := fun read =>
    if read = key then (available.balance key).subtract amount within else available.balance read
  within := by
    intro read
    split
    · rename_i same
      subst read
      exact (sub_le_self _ nonnegative).trans (available.within key)
    · exact available.within read

theorem spend_exact (available : Capacity offer) (key read : Key Party Good) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (within : amount ≤ (available.balance key).remaining) :
    ((available.spend key amount nonnegative within).balance read).remaining =
      (available.balance read).remaining - (if key = read then amount else 0) := by
  by_cases same : read = key
  · subst read
    simp [spend, Balance.subtract]
  · simp [spend, same, Ne.symm same]

end Capacity

local notation "Row" => Occurrence seed community × Balance

/-- A row can consume the offered physical receipt only at its original key
and strictly after its own loss. -/
def eligible (offer : Offer seed) (row : Row) : ℚ := by
  classical
  exact match offer row.1.key with
    | none => 0
    | some receipt => if later row.1 receipt then row.2.remaining else 0

theorem eligible_nonnegative (offer : Offer seed) (row : Row) : 0 ≤ eligible offer row := by
  classical
  unfold eligible
  split
  · exact le_rfl
  · split
    · exact row.2.nonnegative
    · exact le_rfl

def demand (offer : Offer seed) (key : Key Party Good) (rows : List Row) : ℚ :=
  (rows.map (fun row => if row.1.key = key then eligible offer row else 0)).sum

theorem demand_nonnegative (offer : Offer seed) (key : Key Party Good) (rows : List Row) :
    0 ≤ demand offer key rows := by
  unfold demand
  apply List.sum_nonneg
  intro amount member
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  split
  · exact eligible_nonnegative offer row
  · exact le_rfl

def Change.uses (offer : Offer seed) {origin : Occurrence seed community} {balance : Balance} :
    Change origin balance → Prop
  | .keep => True
  | .pay share _ => offer origin.key = some share.receipt

structure Allotment (offer : Offer seed) (available : Capacity offer) (row : Row) where
  change : Change row.1 row.2
  amount_exact : change.amount = min (available.balance row.1.key).remaining (eligible offer row)
  fromOffer : change.uses offer

namespace Allotment

variable {offer : Offer seed} {available : Capacity offer} {row : Occurrence seed community × Balance}

theorem available_bound (allotment : Allotment offer available row) :
    allotment.change.amount ≤ (available.balance row.1.key).remaining :=
  allotment.amount_exact.trans_le (min_le_left _ _)

def remainder (allotment : Allotment offer available row) : Capacity offer :=
  available.spend row.1.key allotment.change.amount allotment.change.amount_nonnegative
    allotment.available_bound

end Allotment

def allot (offer : Offer seed) (available : Capacity offer) (row : Row) : Allotment offer available row := by
  classical
  let cap := available.balance row.1.key
  cases supplied : offer row.1.key with
  | none =>
    refine ⟨.keep, ?_, trivial⟩
    have zero : eligible offer row = 0 := by simp [eligible, supplied]
    rw [zero, min_eq_right cap.nonnegative]
    rfl
  | some receipt =>
    by_cases accepted : later row.1 receipt
    · have eligibleDue : eligible offer row = row.2.remaining := by simp [eligible, supplied, accepted]
      let payment := min cap.remaining row.2.remaining
      by_cases positive : 0 < payment
      · have capInReceipt : cap.remaining ≤ receipt.quantity := by
          have total := available.within row.1.key
          rw [Offer.quantity, supplied] at total
          exact total
        let share : Share row.1 := ⟨receipt, payment, positive, (min_le_left _ _).trans capInReceipt, accepted⟩
        exact ⟨.pay share (min_le_right _ _), by rw [eligibleDue]; rfl, supplied⟩
      · have zero : payment = 0 :=
          le_antisymm (le_of_not_gt positive) (le_min cap.nonnegative row.2.nonnegative)
        exact ⟨.keep, by rw [eligibleDue]; exact zero.symm, trivial⟩
    · have zero : eligible offer row = 0 := by simp [eligible, supplied, accepted]
      refine ⟨.keep, ?_, trivial⟩
      rw [zero, min_eq_right cap.nonnegative]
      rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
