import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Invariants

/-! A single accepted source payment or assignment is consumed once, in
stable original-slot order.  The remainder is explicit when the source
matrix has no corresponding admitted origin. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

structure Allocation (before : (process input).GeneratedState) (available : ℚ) where
  private mk ::
  after : (process input).GeneratedState
  transition : (process input).Run before.current after.current
  remaining : ℚ
  remaining_nonnegative : 0 ≤ remaining
  remaining_le : remaining ≤ available
  original_claims : after.current.slots.map (slotClaim input) =
    before.current.slots.map (slotClaim input)

namespace Allocation

def idle (state : (process input).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation input state available :=
  ⟨state, .nil, available, nonnegative, le_refl _, rfl⟩

def used {state : (process input).GeneratedState} {available : ℚ}
    (result : Allocation input state available) : ℚ := available - result.remaining

theorem used_nonnegative {state : (process input).GeneratedState} {available : ℚ}
    (result : Allocation input state available) : 0 ≤ result.used input :=
  sub_nonneg.mpr result.remaining_le

theorem whole_quota {state : (process input).GeneratedState} {available : ℚ}
    (result : Allocation input state available) :
    result.used input + result.remaining = available := by
  exact sub_add_cancel _ _

theorem original_slots_length {state : (process input).GeneratedState} {available : ℚ}
    (result : Allocation input state available) :
    result.after.current.slots.length = state.current.slots.length := by
  simpa only [List.length_map] using congrArg List.length result.original_claims

theorem history_retained {state : (process input).GeneratedState} {available : ℚ}
    (result : Allocation input state available) :
    state.current.history <+: result.after.current.history := by
  rw [result.transition.history_eq]
  exact List.prefix_append _ _

def append {state : (process input).GeneratedState} {available : ℚ}
    (first : Allocation input state available)
    (second : Allocation input first.after first.remaining) : Allocation input state available where
  after := second.after
  transition := first.transition.concatRuns (process input) second.transition
  remaining := second.remaining
  remaining_nonnegative := second.remaining_nonnegative
  remaining_le := second.remaining_le.trans first.remaining_le
  original_claims := second.original_claims.trans first.original_claims

theorem used_append {state : (process input).GeneratedState} {available : ℚ}
    (first : Allocation input state available)
    (second : Allocation input first.after first.remaining) :
    (first.append input second).used input = first.used input + second.used input := by
  simp only [used, append]
  ring

end Allocation

def allocateLive (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Review input obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    Allocation input state available := by
  let cap := min available receipt.quantity
  have cap_nonnegative : 0 ≤ cap := le_min nonnegative (receipt.quantity_nonnegative input)
  let used := receipt.allocated input obligation.residual cap
  have sound := live_sound input state index obligation present
  have used_nonnegative : 0 ≤ used :=
    receipt.allocated_nonnegative input obligation.residual cap sound.2 cap_nonnegative
  have used_le : used ≤ available :=
    (receipt.allocated_le_available input obligation.residual cap).trans (min_le_left _ _)
  let boundary := reviewBoundary input obligation sound.1 receipt cap sound.2
    cap_nonnegative (min_le_right _ _)
  let edge : (process input).Edge state.current := .cross index obligation present boundary
  refine ⟨state.step (process input) edge, .step .nil edge, available - used,
    sub_nonneg.mpr used_le, sub_le_self available used_nonnegative, ?_⟩
  exact cross_retains_all_claims input state index obligation present boundary

def allocateAt (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) : Allocation input state available :=
  if inRange : position < state.current.slots.length then
    match present : state.current.slots.get ⟨position, inRange⟩ with
    | .terminal _ => Allocation.idle input state available nonnegative
    | .live obligation =>
        match readReview input obligation.content origin with
        | none => Allocation.idle input state available nonnegative
        | some review => allocateLive input state ⟨position, inRange⟩ obligation present review available nonnegative
  else Allocation.idle input state available nonnegative

def allocateFrom (origin : InstructionOrigin input) (position : Nat) :
    (fuel : Nat) → (state : (process input).GeneratedState) →
      (available : ℚ) → 0 ≤ available → Allocation input state available
  | 0, state, available, nonnegative => Allocation.idle input state available nonnegative
  | fuel + 1, state, available, nonnegative =>
      let first := allocateAt input origin state position available nonnegative
      let rest := allocateFrom origin (position + 1) fuel first.after
        first.remaining first.remaining_nonnegative
      first.append input rest

def allocate (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) : Allocation input state available :=
  allocateFrom input origin 0 state.current.slots.length state available nonnegative

theorem empty_has_visible_unallocated_payment (origin : InstructionOrigin input)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocate input origin (.initial (process input)) available nonnegative).remaining = available := rfl

namespace AllocationSource
open ComplementObservation

/-- Slot matching, review construction and the actual generated boundary crossing.
    The called source, validity, share-map and lifecycle primitive internals remain explicit costs. -/
inductive Event where
  | range (position slots : Nat) (inside : Bool)
  | slot (position : Nat) (live : Bool)
  | reviewRead (event : ReviewSource.Event)
  | review (position : Nat) (found : Bool)
  | idle (available : ℚ)
  | cap (available requested limit : ℚ)
  | allocated (used remaining : ℚ)
  | boundary
  | cross
  | live (position : Nat) (available requested limit used remaining : ℚ)
  deriving DecidableEq
private structure Part (α : Type) where
  value : α
  work : List Event

private def live (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Review input obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    Part (Allocation input state available) := by
  let cap := min available receipt.quantity
  have cap_nonnegative : 0 ≤ cap := le_min nonnegative (receipt.quantity_nonnegative input)
  let used := receipt.allocated input obligation.residual cap
  have sound := live_sound input state index obligation present
  have used_nonnegative : 0 ≤ used :=
    receipt.allocated_nonnegative input obligation.residual cap sound.2 cap_nonnegative
  have used_le : used ≤ available :=
    (receipt.allocated_le_available input obligation.residual cap).trans (min_le_left _ _)
  let boundary : Boundary input obligation := {
    event := .review obligation.content receipt obligation.residual cap
    lawful := ⟨sound.2,cap_nonnegative,min_le_right _ _⟩
    content_eq := rfl
    before_eq := rfl
    owns := {
      anchor_eq := by
        change MinimalRegistrableSourceAnchor.canonical obligation.content.origin obligation.content.origin =
          MinimalRegistrableSourceAnchor.canonical
            (obligation.admission.sourceEvent.claim input).origin
            (obligation.admission.sourceEvent.claim input).origin
        rw [sound.1.1]
      incidence_eq := by
        change obligation.content.origin = (obligation.admission.sourceEvent.claim input).origin
        rw [sound.1.1]
    }
    scope_eq := sound.1.2.1
  }
  let edge : (process input).Edge state.current := .cross index obligation present boundary
  let result : Allocation input state available := ⟨state.step (process input) edge,.step .nil edge,
    available-used,sub_nonneg.mpr used_le,sub_le_self available used_nonnegative,
    cross_retains_all_claims input state index obligation present boundary⟩
  exact ⟨result,[.cap available receipt.quantity cap,.allocated used (available-used),.boundary,.cross,
    .live index.val available receipt.quantity cap used (available-used)]⟩

private theorem live_exact (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Review input obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    (live input state index obligation present receipt available nonnegative).value =
      allocateLive input state index obligation present receipt available nonnegative := by rfl

private def produce (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) : Part (Allocation input state available) :=
  if inRange : position < state.current.slots.length then
    match present : state.current.slots.get ⟨position,inRange⟩ with
    | .terminal _ => ⟨Allocation.idle input state available nonnegative,
        [.range position state.current.slots.length true,.slot position false,.idle available]⟩
    | .live obligation =>
      let reading := ReviewSource.compile input obligation.content origin
      match reading.receipt with
      | none => ⟨Allocation.idle input state available nonnegative,
          [.range position state.current.slots.length true,.slot position true] ++
          reading.work.map Event.reviewRead ++ [.review position false,.idle available]⟩
      | some receipt =>
        let made := live input state ⟨position,inRange⟩ obligation present receipt available nonnegative
        ⟨made.value,[.range position state.current.slots.length true,.slot position true] ++
          reading.work.map Event.reviewRead ++ [.review position true] ++ made.work⟩
  else ⟨Allocation.idle input state available nonnegative,
    [.range position state.current.slots.length false,.idle available]⟩
private theorem produce_exact (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (produce input origin state position available nonnegative).value =
      allocateAt input origin state position available nonnegative := by
  unfold produce allocateAt
  split
  · split
    · rfl
    · rename_i obligation present
      dsimp only
      rw [← (ReviewSource.compile input obligation.content origin).exact]
      cases reading : (ReviewSource.compile input obligation.content origin).receipt with
      | none => rfl
      | some receipt => exact live_exact input state _ obligation present receipt available nonnegative
  · rfl
private theorem produce_work (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (produce input origin state position available nonnegative).work.length ≤ 14 := by
  unfold produce
  split
  · split
    · simp
    · rename_i obligation present
      have reading := ReviewSource.work_bound input obligation.content origin
      dsimp only
      split <;> simp only [live,List.length_append,List.length_cons,List.length_nil,List.length_map] <;> omega
  · simp

structure Compilation (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) where
  private mk ::
  result : Allocation input state available
  work : List Event
  exact : result = allocateAt input origin state position available nonnegative
  private generated : result = (produce input origin state position available nonnegative).value ∧
    work = (produce input origin state position available nonnegative).work

def compile (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    Compilation input origin state position available nonnegative :=
  let made := produce input origin state position available nonnegative
  ⟨made.value,made.work,produce_exact input origin state position available nonnegative,⟨rfl,rfl⟩⟩
theorem work_bound (origin : InstructionOrigin input) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (compile input origin state position available nonnegative).work.length ≤ 14 :=
  produce_work input origin state position available nonnegative
private def produceFrom {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) : Part (Allocation input state available) :=
  if inRange : position < state.current.slots.length then
    match present : state.current.slots.get ⟨position,inRange⟩ with
    | .terminal _ => ⟨Allocation.idle input state available nonnegative,
        [.range position state.current.slots.length true,.slot position false,.idle available]⟩
    | .live obligation =>
      let reading := ReviewSource.compileFrom input obligation.content source
      match reading.receipt with
      | none => ⟨Allocation.idle input state available nonnegative,
          [.range position state.current.slots.length true,.slot position true] ++
          reading.work.map Event.reviewRead ++ [.review position false,.idle available]⟩
      | some receipt =>
        let made := live input state ⟨position,inRange⟩ obligation present receipt available nonnegative
        ⟨made.value,[.range position state.current.slots.length true,.slot position true] ++
          reading.work.map Event.reviewRead ++ [.review position true] ++ made.work⟩
  else ⟨Allocation.idle input state available nonnegative,
    [.range position state.current.slots.length false,.idle available]⟩
private theorem from_exact {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (produceFrom input source state position available nonnegative).value =
      allocateAt input origin state position available nonnegative := by
  unfold produceFrom allocateAt
  split
  · split
    · rfl
    · rename_i obligation present
      dsimp only
      rw [← (ReviewSource.compileFrom input obligation.content source).exact]
      cases reading : (ReviewSource.compileFrom input obligation.content source).receipt with
      | none => rfl
      | some receipt => exact live_exact input state _ obligation present receipt available nonnegative
  · rfl
private theorem from_work {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (produceFrom input source state position available nonnegative).work.length ≤ 13 := by
  unfold produceFrom
  split
  · split
    · simp
    · rename_i obligation present
      have reading := ReviewSource.from_work_bound input obligation.content source
      dsimp only
      split <;> simp only [live,List.length_append,List.length_cons,List.length_nil,List.length_map] <;> omega
  · simp

structure FromCompilation {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) where
  private mk ::
  result : Allocation input state available
  work : List Event
  exact : result = allocateAt input origin state position available nonnegative
  private generated : result = (produceFrom input source state position available nonnegative).value ∧
    work = (produceFrom input source state position available nonnegative).work

def compileFrom {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    FromCompilation input source state position available nonnegative :=
  let made := produceFrom input source state position available nonnegative
  ⟨made.value,made.work,from_exact input source state position available nonnegative,⟨rfl,rfl⟩⟩
theorem from_work_bound {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) (state : (process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (compileFrom input source state position available nonnegative).work.length ≤ 13 :=
  from_work input source state position available nonnegative
end AllocationSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
