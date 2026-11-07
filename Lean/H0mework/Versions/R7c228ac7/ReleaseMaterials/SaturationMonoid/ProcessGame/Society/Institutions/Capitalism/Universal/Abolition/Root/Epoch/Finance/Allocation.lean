import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Movement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

/-- The existing native account is crossed in its original slot order. The
balance operations are the original `Financial.pay` and `Financial.assign`. -/
structure Allocation (before : (process input depth count).GeneratedState) (available : ℚ) where
  private mk ::
  after : (process input depth count).GeneratedState
  transition : (process input depth count).Run before.current after.current
  remaining : ℚ
  remaining_nonnegative : 0 ≤ remaining
  remaining_le : remaining ≤ available
  original_claims : after.current.slots.map (slotClaim input depth count) =
    before.current.slots.map (slotClaim input depth count)

namespace Allocation

private def idle (state : (process input depth count).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) : Allocation input depth count state available :=
  ⟨state, .nil, available, nonnegative, le_refl _, rfl⟩

def used {state : (process input depth count).GeneratedState} {available : ℚ}
    (result : Allocation input depth count state available) : ℚ := available - result.remaining

theorem whole_quota {state : (process input depth count).GeneratedState} {available : ℚ}
    (result : Allocation input depth count state available) :
    result.used input depth count + result.remaining = available := sub_add_cancel _ _

theorem used_nonnegative {state : (process input depth count).GeneratedState} {available : ℚ}
    (result : Allocation input depth count state available) :
    0 ≤ result.used input depth count := sub_nonneg.mpr result.remaining_le

theorem original_slots_length {state : (process input depth count).GeneratedState} {available : ℚ}
    (result : Allocation input depth count state available) :
    result.after.current.slots.length = state.current.slots.length := by
  simpa only [List.length_map] using congrArg List.length result.original_claims

theorem history_retained {state : (process input depth count).GeneratedState} {available : ℚ}
    (result : Allocation input depth count state available) :
    state.current.history <+: result.after.current.history := by
  rw [result.transition.history_eq]
  exact List.prefix_append _ _

private def append {state : (process input depth count).GeneratedState} {available : ℚ}
    (first : Allocation input depth count state available)
    (second : Allocation input depth count first.after first.remaining) :
    Allocation input depth count state available where
  after := second.after
  transition := first.transition.concatRuns (process input depth count) second.transition
  remaining := second.remaining
  remaining_nonnegative := second.remaining_nonnegative
  remaining_le := second.remaining_le.trans first.remaining_le
  original_claims := second.original_claims.trans first.original_claims

end Allocation

private def allocateLive (state : (process input depth count).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input depth count))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Review input depth count obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation input depth count state available := by
  let cap := min available receipt.quantity
  have cap_nonnegative : 0 ≤ cap := le_min nonnegative (receipt.quantity_nonnegative input depth count)
  let used := receipt.allocated input depth count obligation.residual cap
  have sound := live_sound input depth count state index obligation present
  have used_nonnegative : 0 ≤ used := le_min cap_nonnegative (sound.2 _)
  have used_le : used ≤ available := (min_le_left _ _).trans (min_le_left _ _)
  let boundary := reviewBoundary input depth count obligation sound.1 receipt cap sound.2
    cap_nonnegative (min_le_right _ _)
  let edge : (process input depth count).Edge state.current := .cross index obligation present boundary
  refine ⟨state.step (process input depth count) edge, .step .nil edge, available - used,
    sub_nonneg.mpr used_le, sub_le_self available used_nonnegative, ?_⟩
  exact cross_retains_all_claims input depth count state index obligation present boundary

private def allocateAt (origin : ActualItem input depth count)
    (state : (process input depth count).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation input depth count state available :=
  if inRange : position < state.current.slots.length then
    match present : state.current.slots.get ⟨position, inRange⟩ with
    | .terminal _ => Allocation.idle input depth count state available nonnegative
    | .live obligation =>
        match readReview input depth count obligation.content origin with
        | none => Allocation.idle input depth count state available nonnegative
        | some review => allocateLive input depth count state ⟨position, inRange⟩ obligation present review available nonnegative
  else Allocation.idle input depth count state available nonnegative

private def allocateFrom (origin : ActualItem input depth count) (position : Nat) :
    (fuel : Nat) → (state : (process input depth count).GeneratedState) →
      (available : ℚ) → 0 ≤ available → Allocation input depth count state available
  | 0, state, available, nonnegative => Allocation.idle input depth count state available nonnegative
  | fuel + 1, state, available, nonnegative =>
      let first := allocateAt input depth count origin state position available nonnegative
      let rest := allocateFrom origin (position + 1) fuel first.after first.remaining first.remaining_nonnegative
      first.append input depth count rest

/-- A source payment supplies the quota exactly once. The local scan only
passes its remainder to the next original slot. -/
def allocate (origin : ActualItem input depth count)
    (movement : Movement input depth count origin)
    (state : (process input depth count).GeneratedState) :
    Allocation input depth count state movement.quantity :=
  allocateFrom input depth count origin 0 state.current.slots.length state movement.quantity
    (movement.quantity_nonnegative input depth count)

theorem empty_has_visible_unallocated_payment (origin : ActualItem input depth count)
    (movement : Movement input depth count origin) :
    (allocate input depth count origin movement (.initial (process input depth count))).remaining =
      movement.quantity := rfl

theorem one_actual_movement_has_one_quota (origin : ActualItem input depth count)
    (movement : Movement input depth count origin)
    (state : (process input depth count).GeneratedState) :
    (allocate input depth count origin movement state).used input depth count +
        (allocate input depth count origin movement state).remaining = movement.quantity :=
  Allocation.whole_quota input depth count _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.one_actual_movement_has_one_quota
