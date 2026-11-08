import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Consume

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Allocation

open ResponsibilityLifecycle Source.Program Abolition.Root Abolition.Root.Epoch.Finance
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private allocateAt allocateLive allocateFrom from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

local notation "V" => vocabulary input depth count
local notation "Book" => NativeResponsibilityProcess.GeneratedState (process input depth count)
local notation "Item" => ActualItem input depth count

def balanceAt (state : Book) (index : Nat) (holder : Party) : ℚ :=
  (state.current.slots[index]?.map (fun slot => slotBalance input depth count slot holder)).getD 0

theorem one_allocation_changes_only_its_original_position (item : Item) (state : Book)
    (index other : Nat) (available : ℚ) (nonnegative : 0 ≤ available) (distinct : index ≠ other) :
    (allocateAt input depth count item state index available nonnegative).after.current.slots[other]? =
      state.current.slots[other]? := by
  unfold allocateAt
  split
  · split
    · rfl
    · split
      · rfl
      · change (state.current.slots.set index _)[other]? = _
        exact List.getElem?_set_ne distinct
  · rfl

theorem later_allocations_keep_the_already_reviewed_position (item : Item) (state : Book)
    (start fuel prior : Nat) (available : ℚ) (nonnegative : 0 ≤ available) (before : prior < start) :
    (allocateFrom input depth count item start fuel state available nonnegative).after.current.slots[prior]? =
      state.current.slots[prior]? := by
  induction fuel generalizing start state available with
  | zero => rfl
  | succ fuel ih =>
      let first := allocateAt input depth count item state start available nonnegative
      change (allocateFrom input depth count item (start + 1) fuel first.after first.remaining
        first.remaining_nonnegative).after.current.slots[prior]? = _
      rw [ih _ _ _ _ (by omega)]
      exact one_allocation_changes_only_its_original_position input depth count item state
        start prior available nonnegative (by omega)

theorem the_target_position_receives_the_remaining_quota
    (item : Item) (state : Book) (index : Nat)
    (obligation : AdmittedObligation V) (present : state.current.slots[index]? = some (.live obligation))
    (receipt : Review input depth count obligation.content) (selected : readReview input depth count obligation.content item = some receipt)
    (holder : Party) (payment : receipt.kind = .payment holder)
    (available : ℚ) (nonnegative : 0 ≤ available) (bounded : available ≤ receipt.quantity) :
    balanceAt input depth count (allocateAt input depth count item state index available nonnegative).after index holder =
      obligation.residual holder - min (obligation.residual holder) available := by
  obtain ⟨inRange, live⟩ := List.getElem?_eq_some_iff.mp present
  unfold allocateAt
  rw [dif_pos inRange]
  split
  · rename_i archive found
    rw [List.get_eq_getElem, live] at found
    cases found
  · rename_i actual found
    have same : actual = obligation := by
      rw [List.get_eq_getElem, live] at found
      exact ObligationSlot.live.inj found.symm
    subst actual
    rw [selected]
    let sound := live_sound input depth count state ⟨index, inRange⟩ obligation found
    let boundary := reviewBoundary input depth count obligation sound.1 receipt (min available receipt.quantity)
      sound.2 (le_min nonnegative (receipt.quantity_nonnegative input depth count)) (min_le_right _ _)
    change ((state.current.slots.set index
      (boundaryDisposition input depth count boundary).targetSlot)[index]?.map
      (fun slot => slotBalance input depth count slot holder)).getD 0 = _
    rw [List.getElem?_set_self inRange]
    change slotBalance input depth count (boundaryDisposition input depth count boundary).targetSlot holder = _
    rw [boundary_balance]
    change receipt.after input depth count obligation.residual (min available receipt.quantity) holder = _
    simp only [Review.after, Review.allocated, Review.fromHolder, payment,
      Financial.pay_apply, ↓reduceIte, min_eq_left bounded]
    rw [min_comm available]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Allocation
