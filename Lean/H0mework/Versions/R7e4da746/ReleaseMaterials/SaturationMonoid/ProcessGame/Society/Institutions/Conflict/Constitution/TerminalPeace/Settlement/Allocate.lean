import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Row
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Exact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Move

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Reparation Reparation.Actual
open private min_successive from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Exact

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {N : WorldRelationNetwork}

local notation "Row" => Occurrence seed community × Balance

/-- Remaining allocable units of this one material position. This is
temporary capacity used in the existing stack's oldest-first order. -/
structure Available (limit : Good → ℚ) where
  balance : Good → Balance
  within : ∀ good, (balance good).remaining ≤ limit good

namespace Available

variable {limit : Good → ℚ}

def full (nonnegative : ∀ good, 0 ≤ limit good) : Available limit :=
  ⟨fun good => ⟨limit good, nonnegative good⟩, fun _ => le_rfl⟩

def spend (prior : Available limit) (good : Good) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (within : amount ≤ (prior.balance good).remaining) : Available limit where
  balance := fun read => if same : read = good then (prior.balance read).subtract amount (same.symm ▸ within)
    else prior.balance read
  within := by
    intro read
    split
    · exact (sub_le_self _ nonnegative).trans (prior.within read)
    · exact prior.within read

theorem spend_exact (prior : Available limit) (good read : Good) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (within : amount ≤ (prior.balance good).remaining) :
    ((prior.spend good amount nonnegative within).balance read).remaining =
      (prior.balance read).remaining - if good = read then amount else 0 := by
  by_cases same : read = good
  · subst read
    simp [spend, Balance.subtract]
  · simp [spend, same, Ne.symm same]

end Available

omit [DecidableEq Community] in
def outstanding (good : Good) (rows : List Row) : ℚ :=
  (rows.map fun row => if row.1.key.2.2 = good then row.2.remaining else 0).sum

omit [DecidableEq Community] in
def demand (offer : JointOffer seed) (good : Good) (rows : List Row) : ℚ :=
  (rows.map fun row => if row.1.key.2.2 = good then rowDemand offer row.1 row.2 else 0).sum

private theorem demand_nonnegative (offer : JointOffer seed) (good : Good) (rows : List Row) :
    0 ≤ demand offer good rows := by
  unfold demand
  apply List.sum_nonneg
  rintro amount listed
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp listed
  split
  · exact rowDemand_nonnegative _ _ _
  · exact le_rfl

structure AppliedPosition (offer : JointOffer seed) {limit : Good → ℚ}
    {J : WorldRelationNetwork} (before : Stack seed community N J) (available : Available limit) where
  after : Stack seed community N J
  move : Stack.Move before after
  left : Available limit
  conservation : ∀ good, outstanding good after.balances +
    ((available.balance good).remaining - (left.balance good).remaining) = outstanding good before.balances
  tight : ∀ good, (available.balance good).remaining - (left.balance good).remaining =
    min (available.balance good).remaining (demand offer good before.balances)

namespace AppliedPosition

variable {offer : JointOffer seed} {limit : Good → ℚ} {J : WorldRelationNetwork}
  {before : Stack seed community N J} {available : Available limit}

def used (written : AppliedPosition offer before available) (good : Good) : ℚ :=
  (available.balance good).remaining - (written.left.balance good).remaining

theorem used_le_available (written : AppliedPosition offer before available) (good : Good) :
    written.used good ≤ (available.balance good).remaining :=
  sub_le_self _ (written.left.balance good).nonnegative

end AppliedPosition

variable (offer : JointOffer seed) (limit : Good → ℚ)
  (backed : ∀ (key : Key Party Good) (receipt : JointReceipt seed key),
    offer key = some receipt → limit key.2.2 ≤ receipt.quantity)

private theorem used_at_cons (available remaining charged earlier newDue : ℚ)
    (previous : available - remaining = min available earlier)
    (now : charged = min remaining newDue) (nonnegative : 0 ≤ newDue) :
    available - (remaining - charged) = min available (earlier + newDue) := by
  have exactRemaining : remaining = available - min available earlier := by linarith only [previous]
  have balance := min_successive available earlier newDue nonnegative
  rw [now, exactRemaining]
  linarith only [balance]

/-- Allocate once across the original stack, keeping its installed layer
and source law for every old row. -/
def allocate : {J : WorldRelationNetwork} → (before : Stack seed community N J) →
    (available : Available limit) → AppliedPosition offer before available
  | _, .base _, available =>
    ⟨.base _, .base, available, by intro good; simp [outstanding, Stack.balances],
      by intro good; simp [demand, Stack.balances, min_eq_right (available.balance good).nonnegative]⟩
  | _, .add prior origin balance view, available => by
    let earlier := allocate prior available
    let good := origin.key.2.2
    let supply := earlier.left.balance good
    let head := allocateRow offer origin balance supply.remaining supply.nonnegative
      (fun receipt selected => (earlier.left.within good).trans (backed origin.key receipt selected))
    let left := earlier.left.spend good head.amount (head.amount_nonnegative supply.nonnegative) head.amount_le_available
    let after := Stack.add earlier.after origin head.after view
    refine ⟨after, .add earlier.move origin view head.motion, left, ?_, ?_⟩
    · intro read
      have conserved := earlier.conservation read
      have spent := earlier.left.spend_exact good read head.amount
        (head.amount_nonnegative supply.nonnegative) head.amount_le_available
      change outstanding read (earlier.after.balances ++ [(origin, head.after)]) +
        ((available.balance read).remaining - (left.balance read).remaining) =
          outstanding read (prior.balances ++ [(origin, balance)])
      simp only [outstanding, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
        add_zero]
      change (left.balance read).remaining = _ at spent
      change _ + ((available.balance read).remaining - (earlier.left.balance read).remaining) = _ at conserved
      unfold outstanding at conserved
      by_cases same : good = read
      · rw [if_pos same] at spent
        rw [if_pos same, if_pos same, spent, head.afterExact]
        linarith only [conserved]
      · rw [if_neg same] at spent
        rw [if_neg same, if_neg same, spent, sub_zero, add_zero, add_zero]
        exact conserved
    · intro read
      have spent := earlier.left.spend_exact good read head.amount
        (head.amount_nonnegative supply.nonnegative) head.amount_le_available
      change (left.balance read).remaining = _ at spent
      change _ - (left.balance read).remaining = min _ (demand offer read (prior.balances ++ [(origin, balance)]))
      have splitDemand : demand offer read (prior.balances ++ [(origin, balance)]) =
          demand offer read prior.balances + if good = read then rowDemand offer origin balance else 0 := by
        simp [demand, good, List.sum_append]
      rw [splitDemand, spent]
      by_cases same : good = read
      · rw [if_pos same, if_pos same]
        have paid : head.amount = min (earlier.left.balance read).remaining (rowDemand offer origin balance) := by
          rw [← same]
          exact head.exactAmount
        exact used_at_cons _ _ _ _ _ (earlier.tight read) paid (rowDemand_nonnegative _ _ _)
      · rw [if_neg same, if_neg same, sub_zero, add_zero]
        exact earlier.tight read

#print axioms allocate

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
