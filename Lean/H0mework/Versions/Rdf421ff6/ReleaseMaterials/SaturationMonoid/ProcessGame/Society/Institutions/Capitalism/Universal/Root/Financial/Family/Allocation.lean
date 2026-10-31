import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Invariants

/-! A single accepted source payment or assignment is consumed once, in
stable original-slot order.  The remainder is explicit when the source
matrix has no corresponding admitted origin. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

structure Allocation (before : (process sources).GeneratedState) (available : ℚ) where
  private mk ::
  after : (process sources).GeneratedState
  transition : (process sources).Run before.current after.current
  remaining : ℚ
  remaining_nonnegative : 0 ≤ remaining
  remaining_le : remaining ≤ available
  original_claims : after.current.slots.map (slotClaim sources) =
    before.current.slots.map (slotClaim sources)

namespace Allocation

def idle (state : (process sources).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation sources state available :=
  ⟨state, .nil, available, nonnegative, le_refl _, rfl⟩

def used {state : (process sources).GeneratedState} {available : ℚ}
    (result : Allocation sources state available) : ℚ := available - result.remaining

theorem used_nonnegative {state : (process sources).GeneratedState} {available : ℚ}
    (result : Allocation sources state available) : 0 ≤ result.used sources :=
  sub_nonneg.mpr result.remaining_le

theorem whole_quota {state : (process sources).GeneratedState} {available : ℚ}
    (result : Allocation sources state available) :
    result.used sources + result.remaining = available := by
  exact sub_add_cancel _ _

theorem original_slots_length {state : (process sources).GeneratedState} {available : ℚ}
    (result : Allocation sources state available) :
    result.after.current.slots.length = state.current.slots.length := by
  simpa only [List.length_map] using congrArg List.length result.original_claims

theorem history_retained {state : (process sources).GeneratedState} {available : ℚ}
    (result : Allocation sources state available) :
    state.current.history <+: result.after.current.history := by
  rw [result.transition.history_eq]
  exact List.prefix_append _ _

def append {state : (process sources).GeneratedState} {available : ℚ}
    (first : Allocation sources state available)
    (second : Allocation sources first.after first.remaining) : Allocation sources state available where
  after := second.after
  transition := first.transition.concatRuns (process sources) second.transition
  remaining := second.remaining
  remaining_nonnegative := second.remaining_nonnegative
  remaining_le := second.remaining_le.trans first.remaining_le
  original_claims := second.original_claims.trans first.original_claims

theorem used_append {state : (process sources).GeneratedState} {available : ℚ}
    (first : Allocation sources state available)
    (second : Allocation sources first.after first.remaining) :
    (first.append sources second).used sources = first.used sources + second.used sources := by
  simp only [used, append]
  ring

end Allocation

def allocateLive (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Review sources obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation sources state available := by
  let cap := min available receipt.quantity
  have cap_nonnegative : 0 ≤ cap := le_min nonnegative (receipt.quantity_nonnegative sources)
  let used := min cap (obligation.residual receipt.sender)
  have sound := live_sound sources state index obligation present
  have used_nonnegative : 0 ≤ used :=
    le_min cap_nonnegative (sound.2 receipt.sender)
  have used_le : used ≤ available :=
    (min_le_left _ _).trans (min_le_left _ _)
  let boundary := reviewBoundary sources obligation receipt cap sound.2
    cap_nonnegative (min_le_right _ _) sound.1
  let edge : (process sources).Edge state.current := .cross index obligation present boundary
  refine ⟨state.step (process sources) edge, .step .nil edge, available - used,
    sub_nonneg.mpr used_le, sub_le_self available used_nonnegative, ?_⟩
  exact cross_retains_all_claims sources state index obligation present boundary

def allocateAt (origin : Origin sources) (state : (process sources).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) : Allocation sources state available :=
  if inRange : position < state.current.slots.length then
    match present : state.current.slots.get ⟨position, inRange⟩ with
    | .terminal _ => Allocation.idle sources state available nonnegative
    | .live obligation =>
        match readReview sources obligation.content origin with
        | none => Allocation.idle sources state available nonnegative
        | some review => allocateLive sources state ⟨position, inRange⟩ obligation present review available nonnegative
  else Allocation.idle sources state available nonnegative

def allocateFrom (origin : Origin sources) (position : Nat) :
    (fuel : Nat) → (state : (process sources).GeneratedState) →
      (available : ℚ) → 0 ≤ available → Allocation sources state available
  | 0, state, available, nonnegative => Allocation.idle sources state available nonnegative
  | fuel + 1, state, available, nonnegative =>
      let first := allocateAt sources origin state position available nonnegative
      let rest := allocateFrom origin (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative
      first.append sources rest

def allocate (origin : Origin sources) (state : (process sources).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) : Allocation sources state available :=
  allocateFrom sources origin 0 state.current.slots.length state available nonnegative

theorem empty_has_visible_unallocated_payment (origin : Origin sources)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocate sources origin (.initial (process sources)) available nonnegative).remaining = available := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family
