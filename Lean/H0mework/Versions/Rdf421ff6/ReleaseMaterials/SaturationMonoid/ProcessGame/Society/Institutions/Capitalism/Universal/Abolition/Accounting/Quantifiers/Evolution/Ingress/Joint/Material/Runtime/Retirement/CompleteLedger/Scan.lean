import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Readout


set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private allocateAt allocateLive allocateFrom Allocation.idle Allocation.append from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

def reviewCapacity (origin : ActualItem input depth count)
    (slot : ObligationSlot (vocabulary input depth count)) : ℚ :=
  match slot with
  | .terminal _ => 0
  | .live obligation =>
      match readReview input depth count obligation.content origin with
      | none => 0
      | some review => obligation.residual (review.fromHolder input depth count)

def suffixCapacity (origin : ActualItem input depth count)
    (state : ResponsibilityState (vocabulary input depth count)) (position : Nat) : ℚ :=
  ((state.slots.drop position).map (reviewCapacity input depth count origin)).sum

def ReviewQuantityAt (origin : ActualItem input depth count) (quantity : ℚ) : Prop :=
  ∀ (claim : Claim input depth count) (review : Review input depth count claim),
    readReview input depth count claim origin = some review → review.quantity = quantity

theorem reviewCapacity_nonnegative (origin : ActualItem input depth count)
    (state : (process input depth count).GeneratedState) (slot : ObligationSlot (vocabulary input depth count))
    (member : slot ∈ state.current.slots) : 0 ≤ reviewCapacity input depth count origin slot := by
  cases slot with
  | terminal archive => exact le_refl 0
  | live obligation =>
      have sound : Financial.Nonnegative input obligation.residual :=
        (generated_sound input depth count state (.live obligation) member).2
      change 0 ≤ match readReview input depth count obligation.content origin with
        | none => 0
        | some review => obligation.residual (review.fromHolder input depth count)
      cases selected : readReview input depth count obligation.content origin with
      | none => exact le_refl 0
      | some review => exact sound (review.fromHolder input depth count)

theorem suffixCapacity_nonnegative (origin : ActualItem input depth count)
    (state : (process input depth count).GeneratedState) (position : Nat) :
    0 ≤ suffixCapacity input depth count origin state.current position := by
  unfold suffixCapacity
  apply List.sum_nonneg
  intro quantity member
  obtain ⟨slot, inside, rfl⟩ := List.mem_map.mp member
  exact reviewCapacity_nonnegative input depth count origin state slot (List.mem_of_mem_drop inside)

private theorem drop_after_set {α : Type} (slots : List α) (position : Nat) (value : α) :
    (slots.set position value).drop (position + 1) = slots.drop (position + 1) := by
  induction slots generalizing position with
  | nil => simp
  | cons head tail ih => cases position <;> simp [ih]

theorem allocateAt_suffix (origin : ActualItem input depth count)
    (state : (process input depth count).GeneratedState) (position : Nat)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocateAt input depth count origin state position available nonnegative).after.current.slots.drop
        (position + 1) = state.current.slots.drop (position + 1) := by
  by_cases inRange : position < state.current.slots.length
  · rw [allocateAt, dif_pos inRange]
    split
    · rfl
    · split
      · rfl
      · change (state.current.slots.set position _).drop (position + 1) = _
        exact drop_after_set _ _ _
  · rw [allocateAt, dif_neg inRange]
    rfl

theorem allocateLive_remaining (state : (process input depth count).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input depth count))
    (present : state.current.slots.get index = .live obligation)
    (review : Review input depth count obligation.content) (available : ℚ) (nonnegative : 0 ≤ available)
    (bounded : available ≤ review.quantity) :
    (allocateLive input depth count state index obligation present review available nonnegative).remaining =
      max (available - obligation.residual (review.fromHolder input depth count)) 0 := by
  change available - min (min available review.quantity)
    (obligation.residual (review.fromHolder input depth count)) = _
  rw [min_eq_left bounded]
  by_cases enough : available ≤ obligation.residual (review.fromHolder input depth count)
  · rw [min_eq_left enough, max_eq_right (sub_nonpos.mpr enough), sub_self]
  · have enough' := le_of_not_ge enough
    rw [min_eq_right enough', max_eq_left (sub_nonneg.mpr enough')]

theorem allocateAt_remaining (origin : ActualItem input depth count)
    (state : (process input depth count).GeneratedState) (position : Nat)
    (available quantity : ℚ) (nonnegative : 0 ≤ available)
    (inRange : position < state.current.slots.length)
    (sourceQuantity : ReviewQuantityAt input depth count origin quantity) (bounded : available ≤ quantity) :
    (allocateAt input depth count origin state position available nonnegative).remaining =
      max (available - reviewCapacity input depth count origin state.current.slots[position]) 0 := by
  rw [allocateAt, dif_pos inRange]
  split
  next archive present =>
    have atIndex : state.current.slots[position] = .terminal archive := present
    simp only [Allocation.idle, atIndex, reviewCapacity, sub_zero, max_eq_left nonnegative]
  next obligation present =>
    have atIndex : state.current.slots[position] = .live obligation := present
    split
    next absent =>
      simp only [Allocation.idle, atIndex, reviewCapacity, absent, sub_zero, max_eq_left nonnegative]
    next review selected =>
      simp only [atIndex, reviewCapacity, selected]
      apply allocateLive_remaining
      rw [sourceQuantity obligation.content review selected]
      exact bounded

theorem suffixCapacity_cons (origin : ActualItem input depth count)
    (state : ResponsibilityState (vocabulary input depth count)) (position : Nat)
    (inRange : position < state.slots.length) :
    suffixCapacity input depth count origin state position =
      reviewCapacity input depth count origin state.slots[position] +
        suffixCapacity input depth count origin state (position + 1) := by
  unfold suffixCapacity
  rw [List.drop_eq_getElem_cons inRange]
  rfl

theorem allocateFrom_remaining (origin : ActualItem input depth count) (quantity : ℚ)
    (sourceQuantity : ReviewQuantityAt input depth count origin quantity) (fuel position : Nat)
    (state : (process input depth count).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available)
    (bounded : available ≤ quantity) (wholeSuffix : position + fuel = state.current.slots.length) :
    (allocateFrom input depth count origin position fuel state available nonnegative).remaining =
      max (available - suffixCapacity input depth count origin state.current position) 0 := by
  induction fuel generalizing state position available with
  | zero =>
      have exhausted : state.current.slots.length ≤ position := by omega
      simp only [allocateFrom, Allocation.idle, suffixCapacity, List.drop_eq_nil_iff.mpr exhausted,
        List.map_nil, List.sum_nil, sub_zero, max_eq_left nonnegative]
  | succ fuel ih =>
      have inRange : position < state.current.slots.length := by omega
      let first := allocateAt input depth count origin state position available nonnegative
      have unchanged : suffixCapacity input depth count origin first.after.current (position + 1) =
          suffixCapacity input depth count origin state.current (position + 1) := by
        unfold suffixCapacity
        rw [allocateAt_suffix]
      have remaining := allocateAt_remaining input depth count origin state position available quantity
        nonnegative inRange sourceQuantity bounded
      have smaller := ih (position + 1) first.after first.remaining first.remaining_nonnegative
        (first.remaining_le.trans bounded) (by rw [first.original_slots_length input depth count]; omega)
      change (allocateFrom input depth count origin (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative).remaining = _
      rw [smaller, unchanged, suffixCapacity_cons input depth count origin state.current position inRange]
      rw [show first.remaining = max (available - reviewCapacity input depth count origin state.current.slots[position]) 0
        from remaining]
      have restNonnegative := suffixCapacity_nonnegative input depth count origin state (position + 1)
      simp only [max_def]
      split_ifs <;> linarith

theorem allocate_remaining (origin : ActualItem input depth count)
    (movement : Movement input depth count origin)
    (sourceQuantity : ReviewQuantityAt input depth count origin movement.quantity)
    (state : (process input depth count).GeneratedState) :
    (allocate input depth count origin movement state).remaining =
      max (movement.quantity - suffixCapacity input depth count origin state.current 0) 0 := by
  exact allocateFrom_remaining input depth count origin movement.quantity sourceQuantity _ 0 state movement.quantity
    (movement.quantity_nonnegative input depth count) (le_refl _) (Nat.zero_add _)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
