import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Readout

/-! The capacity of the unvisited original slots.  Assignment to the same
holder does not consume principal, but it still consumes its source quota;
the scan therefore counts a slot only before visiting it. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def reviewCapacity (origin : Origin sources)
    (slot : ObligationSlot (vocabulary sources)) : ℚ :=
  match slot with
  | .terminal _ => 0
  | .live obligation =>
      match readReview sources obligation.content origin with
      | none => 0
      | some review => obligation.residual review.sender

def suffixCapacity (origin : Origin sources)
    (state : ResponsibilityState (vocabulary sources)) (position : Nat) : ℚ :=
  ((state.slots.drop position).map (reviewCapacity sources origin)).sum

def ReviewQuantityAt (origin : Origin sources) (quantity : ℚ) : Prop :=
  ∀ (claim : Claim sources) (review : Review sources claim),
    readReview sources claim origin = some review → review.quantity = quantity

theorem reviewCapacity_nonnegative (origin : Origin sources)
    (state : (process sources).GeneratedState) (slot : ObligationSlot (vocabulary sources))
    (member : slot ∈ state.current.slots) : 0 ≤ reviewCapacity sources origin slot := by
  cases slot with
  | terminal archive => exact le_refl 0
  | live obligation =>
      have sound : ∀ holder, 0 ≤ obligation.residual holder :=
        (generated_sound sources state (.live obligation) member).2
      change 0 ≤ match readReview sources obligation.content origin with
        | none => 0
        | some review => obligation.residual review.sender
      cases selected : readReview sources obligation.content origin with
      | none => exact le_refl 0
      | some review => exact sound review.sender

theorem suffixCapacity_nonnegative (origin : Origin sources)
    (state : (process sources).GeneratedState) (position : Nat) :
    0 ≤ suffixCapacity sources origin state.current position := by
  unfold suffixCapacity
  apply List.sum_nonneg
  intro quantity member
  obtain ⟨slot, inside, rfl⟩ := List.mem_map.mp member
  exact reviewCapacity_nonnegative sources origin state slot (List.mem_of_mem_drop inside)

private theorem drop_after_set {α : Type} (slots : List α) (position : Nat) (value : α) :
    (slots.set position value).drop (position + 1) = slots.drop (position + 1) := by
  induction slots generalizing position with
  | nil => simp
  | cons head tail ih => cases position <;> simp [ih]

theorem allocateAt_suffix (origin : Origin sources)
    (state : (process sources).GeneratedState) (position : Nat)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocateAt sources origin state position available nonnegative).after.current.slots.drop
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

theorem allocateLive_remaining (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (review : Review sources obligation.content) (available : ℚ) (nonnegative : 0 ≤ available)
    (bounded : available ≤ review.quantity) :
    (allocateLive sources state index obligation present review available nonnegative).remaining =
      max (available - obligation.residual review.sender) 0 := by
  change available - min (min available review.quantity)
    (obligation.residual review.sender) = _
  rw [min_eq_left bounded]
  by_cases enough : available ≤ obligation.residual review.sender
  · rw [min_eq_left enough, max_eq_right (sub_nonpos.mpr enough), sub_self]
  · have enough' := le_of_not_ge enough
    rw [min_eq_right enough', max_eq_left (sub_nonneg.mpr enough')]

theorem allocateAt_remaining (origin : Origin sources)
    (state : (process sources).GeneratedState) (position : Nat)
    (available quantity : ℚ) (nonnegative : 0 ≤ available)
    (inRange : position < state.current.slots.length)
    (sourceQuantity : ReviewQuantityAt sources origin quantity) (bounded : available ≤ quantity) :
    (allocateAt sources origin state position available nonnegative).remaining =
      max (available - reviewCapacity sources origin state.current.slots[position]) 0 := by
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

theorem suffixCapacity_cons (origin : Origin sources)
    (state : ResponsibilityState (vocabulary sources)) (position : Nat)
    (inRange : position < state.slots.length) :
    suffixCapacity sources origin state position =
      reviewCapacity sources origin state.slots[position] +
        suffixCapacity sources origin state (position + 1) := by
  unfold suffixCapacity
  rw [List.drop_eq_getElem_cons inRange]
  rfl

theorem allocateFrom_remaining (origin : Origin sources) (quantity : ℚ)
    (sourceQuantity : ReviewQuantityAt sources origin quantity) (fuel position : Nat)
    (state : (process sources).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available)
    (bounded : available ≤ quantity) (wholeSuffix : position + fuel = state.current.slots.length) :
    (allocateFrom sources origin position fuel state available nonnegative).remaining =
      max (available - suffixCapacity sources origin state.current position) 0 := by
  induction fuel generalizing state position available with
  | zero =>
      have exhausted : state.current.slots.length ≤ position := by omega
      simp only [allocateFrom, Allocation.idle, suffixCapacity, List.drop_eq_nil_iff.mpr exhausted,
        List.map_nil, List.sum_nil, sub_zero, max_eq_left nonnegative]
  | succ fuel ih =>
      have inRange : position < state.current.slots.length := by omega
      let first := allocateAt sources origin state position available nonnegative
      have unchanged : suffixCapacity sources origin first.after.current (position + 1) =
          suffixCapacity sources origin state.current (position + 1) := by
        unfold suffixCapacity
        rw [allocateAt_suffix]
      have remaining := allocateAt_remaining sources origin state position available quantity
        nonnegative inRange sourceQuantity bounded
      have smaller := ih (position + 1) first.after first.remaining first.remaining_nonnegative
        (first.remaining_le.trans bounded) (by rw [first.original_slots_length sources]; omega)
      change (allocateFrom sources origin (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative).remaining = _
      rw [smaller, unchanged, suffixCapacity_cons sources origin state.current position inRange]
      rw [show first.remaining = max (available - reviewCapacity sources origin state.current.slots[position]) 0
        from remaining]
      have restNonnegative := suffixCapacity_nonnegative sources origin state (position + 1)
      simp only [max_def]
      split_ifs <;> linarith

theorem allocate_remaining (origin : Origin sources) (quantity : ℚ)
    (sourceQuantity : ReviewQuantityAt sources origin quantity)
    (state : (process sources).GeneratedState) (nonnegative : 0 ≤ quantity) :
    (allocate sources origin state quantity nonnegative).remaining =
      max (quantity - suffixCapacity sources origin state.current 0) 0 := by
  exact allocateFrom_remaining sources origin quantity sourceQuantity _ 0 state quantity
    nonnegative (le_refl _) (Nat.zero_add _)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
