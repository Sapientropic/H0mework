import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Allocation.Local

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Allocation

open ResponsibilityLifecycle Source.Program Abolition.Root Abolition.Root.Epoch.Finance
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private allocateAt allocateFrom from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

local notation "V" => vocabulary input depth count
local notation "Book" => NativeResponsibilityProcess.GeneratedState (process input depth count)
local notation "Item" => ActualItem input depth count

def prefixCapacity (state : Book) (start prior : Nat) (instrument : Instrument) (debtor holder : Party) : ℚ :=
  (((state.current.slots.drop start).take prior).map
    (fun slot => slotClaims input depth count slot instrument debtor holder)).sum

theorem prefixCapacity_nonnegative (state : Book) (start prior : Nat)
    (instrument : Instrument) (debtor holder : Party) :
    0 ≤ prefixCapacity input depth count state start prior instrument debtor holder := by
  unfold prefixCapacity
  apply List.sum_nonneg
  intro quantity member
  obtain ⟨slot, inside, rfl⟩ := List.mem_map.mp member
  exact slotClaims_nonnegative input depth count state slot (List.mem_of_mem_drop (List.mem_of_mem_take inside))
    instrument debtor holder

private theorem prefixCapacity_succ (state : Book) (start prior : Nat)
    (instrument : Instrument) (debtor holder : Party) (inRange : start < state.current.slots.length) :
    prefixCapacity input depth count state start (prior + 1) instrument debtor holder =
      slotClaims input depth count state.current.slots[start] instrument debtor holder +
        prefixCapacity input depth count state (start + 1) prior instrument debtor holder := by
  unfold prefixCapacity
  rw [List.drop_eq_getElem_cons inRange]
  rfl

theorem the_original_allocation_pays_exactly_the_post_priority_quota
    (item : Item) (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (obligation : AdmittedObligation V)
    (address : obligation.content.instrument input depth count = instrument ∧
      obligation.content.debtor input depth count = debtor)
    (state : Book) (start prior fuel : Nat) (available : ℚ) (nonnegative : 0 ≤ available)
    (bounded : available ≤ quantity) (covers : prior < fuel)
    (present : state.current.slots[start + prior]? = some (.live obligation)) :
    balanceAt input depth count
      (allocateFrom input depth count item start fuel state available nonnegative).after (start + prior) holder =
      obligation.residual holder - min (obligation.residual holder)
        (max 0 (available - prefixCapacity input depth count state start prior instrument debtor holder)) := by
  induction prior generalizing start fuel state available with
  | zero =>
    rcases fuel with _ | rest
    · omega
    let first := allocateAt input depth count item state start available nonnegative
    have later := later_allocations_keep_the_already_reviewed_position input depth count item first.after
      (start + 1) rest start first.remaining first.remaining_nonnegative (by omega)
    obtain ⟨receipt, selected, _, payment, cap⟩ := an_actual_matching_payment_generates_its_original_review
      input depth count obligation.content item holder quantity
      (by rw [address.1, address.2]; exact operation) accepted
    have settles := the_target_position_receives_the_remaining_quota input depth count item state start obligation
      (by simpa only [Nat.add_zero] using present) receipt selected holder payment available nonnegative
      (by simpa only [cap] using bounded)
    change ((allocateFrom input depth count item (start + 1) rest first.after first.remaining
        first.remaining_nonnegative).after.current.slots[start]?.map
          (fun slot => slotBalance input depth count slot holder)).getD 0 = _
    rw [later]
    change balanceAt input depth count first.after start holder = _
    simpa only [prefixCapacity, List.take_zero, List.map_nil, List.sum_nil, sub_zero, max_eq_right nonnegative]
      using settles
  | succ prior ih =>
    rcases fuel with _ | rest
    · omega
    let first := allocateAt input depth count item state start available nonnegative
    have inRange : start < state.current.slots.length := by
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp present
      omega
    have target : start + (prior + 1) = (start + 1) + prior := by omega
    have sameSlot : first.after.current.slots[(start + 1) + prior]? = some (.live obligation) := by
      rw [one_allocation_changes_only_its_original_position input depth count item state start _ available
        nonnegative (by omega), ← target]
      exact present
    have restPaid := ih first.after (start + 1) rest first.remaining first.remaining_nonnegative
      (first.remaining_le.trans bounded) (by omega) sameSlot
    have samePrefix : prefixCapacity input depth count first.after (start + 1) prior instrument debtor holder =
        prefixCapacity input depth count state (start + 1) prior instrument debtor holder := by
      unfold prefixCapacity
      rw [allocateAt_suffix input depth count item state start available nonnegative]
    have remaining : first.remaining =
        max (available - slotClaims input depth count state.current.slots[start] instrument debtor holder) 0 := by
      change (allocateAt input depth count item state start available nonnegative).remaining = _
      rw [allocateAt_remaining input depth count item state start available quantity nonnegative inRange
        (payment_source_quantity input depth count item instrument debtor holder quantity operation) bounded,
        payment_capacity input depth count item instrument debtor holder quantity operation accepted]
    have tailPositive := prefixCapacity_nonnegative input depth count state (start + 1) prior instrument debtor holder
    change balanceAt input depth count
        (allocateFrom input depth count item (start + 1) rest first.after first.remaining
          first.remaining_nonnegative).after (start + (prior + 1)) holder = _
    rw [target, restPaid, samePrefix, remaining, prefixCapacity_succ input depth count state start prior
      instrument debtor holder inRange]
    have quota (debit : ℚ) :
        max 0 (max (available - debit) 0 - prefixCapacity input depth count state (start + 1) prior instrument debtor holder) =
          max 0 (available - (debit + prefixCapacity input depth count state (start + 1) prior instrument debtor holder)) := by
      simp only [max_def]
      split_ifs <;> linarith
    rw [quota]

theorem the_literal_native_payment_reduces_the_named_old_slot_by_its_exact_share
    (item : Item) (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (state : Book) (index : Nat) (obligation : AdmittedObligation V)
    (present : state.current.slots[index]? = some (.live obligation))
    (address : obligation.content.instrument input depth count = instrument ∧
      obligation.content.debtor input depth count = debtor) :
    balanceAt input depth count ((consume input depth count item state).next input depth count) index holder =
      balanceAt input depth count state index holder - min (balanceAt input depth count state index holder)
        (max 0 (quantity - prefixCapacity input depth count state 0 index instrument debtor holder)) := by
  obtain ⟨movement, parsed, _, amount⟩ := an_actual_payment_generates_its_original_movement
    input depth count item instrument debtor holder quantity operation accepted
  rw [the_actual_settlement_next_is_the_same_original_allocator input depth count item instrument debtor holder
    quantity operation accepted state movement parsed]
  have inRange := (List.getElem?_eq_some_iff.mp present).1
  have effect := the_original_allocation_pays_exactly_the_post_priority_quota input depth count
    item instrument debtor holder quantity operation accepted obligation address state 0 index state.current.slots.length
    movement.quantity (movement.quantity_nonnegative input depth count) amount.le inRange
    (by simpa only [Nat.zero_add] using present)
  have original : balanceAt input depth count state index holder = obligation.residual holder := by
    unfold balanceAt
    rw [present]
    rfl
  rw [original]
  simpa only [allocate, Nat.zero_add, amount] using effect

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Allocation
