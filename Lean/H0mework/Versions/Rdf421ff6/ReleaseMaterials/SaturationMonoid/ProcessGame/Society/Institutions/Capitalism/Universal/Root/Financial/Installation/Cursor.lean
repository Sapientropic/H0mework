import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Action

/-! A raw body takes effect once, at cursor zero.  Later positions consume
that body's already generated original inventory; they do not execute a
second material transfer.  All unprocessed items remain explicit. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive Phase
  | entering | accounting
  deriving DecidableEq

structure State where
  cycle : Nat
  position : Nat
  ahead : Nat
  phase : Phase
  account : (process input).GeneratedState

def initial : State input := ⟨0, 0, 0, .accounting, .initial (process input)⟩

def enteringAt (physical : Nat) : State input :=
  ⟨0, 0, physical, .entering, .initial (process input)⟩

def originalVisit (state : State input) := ProgrammeHistory.visitAt input state.cycle

def capacity (state : State input) : Nat :=
  (inventoryAt input (originalVisit input state)).length

theorem fixed_capacity (state : State input) (fixed : input.emission? = none) :
    capacity input state = input.instructions.length + 2 := by
  simp only [capacity, inventoryAt, fixed, administrativeInventoryAt, List.length_ofFn,
    ProgrammeSource.registrationSize_fixed input fixed]

theorem generated_capacity (state : State input)
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) :
    capacity input state = ProgrammeSource.registrationSize input + 2 +
      (Source.ProgrammeFace.Registered.traceItems input (originalVisit input state).current).length := by
  simp only [capacity, inventoryAt, generated, List.length_append,
    administrativeInventoryAt, traceInventoryAt, List.length_ofFn]

theorem capacity_positive (state : State input) : 0 < capacity input state := by
  unfold capacity inventoryAt
  cases input.emission? <;>
    simp [administrativeInventoryAt, traceInventoryAt]

def physicalVisitIndex (state : State input) : Nat :=
  state.ahead + state.cycle + if state.position = 0 then 0 else 1

def physicalVisit (state : State input) :=
  ProgrammeHistory.visitAt input (physicalVisitIndex input state)

def originalItem? (state : State input) : Option (InstructionOrigin input) :=
  (inventoryAt input (originalVisit input state))[state.position]?

/-- Every dynamically emitted trace position is read after the inherited
administrative rows, even beyond the seed instruction count. -/
theorem generated_item_at_trace_position (state : State input)
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input (originalVisit input state).current).length)
    (position : state.position = ProgrammeSource.registrationSize input + 2 + index.val) :
    originalItem? input state = some (traceOriginAt input (originalVisit input state) index) := by
  simp only [originalItem?, inventoryAt, generated, position]
  rw [List.getElem?_append_right (by
    simp only [administrativeInventoryAt, List.length_ofFn]
    omega)]
  simp only [administrativeInventoryAt, List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by simpa only [traceInventoryAt, List.length_ofFn] using index.isLt)]
  simp only [traceInventoryAt, List.getElem_ofFn]

theorem generated_position_decodes_original_instruction (state : State input)
    (emit : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit)
    (index : Fin (Source.ProgrammeFace.Registered.traceItems input (originalVisit input state).current).length)
    (position : state.position = ProgrammeSource.registrationSize input + 2 + index.val) :
    ∃ origin, originalItem? input state = some origin ∧
      origin.instruction? input =
        some ((Source.ProgrammeFace.Registered.traceItems input (originalVisit input state).current).get index) :=
  ⟨traceOriginAt input (originalVisit input state) index,
    generated_item_at_trace_position input state emit generated index position,
    traceOriginAt_instruction input (originalVisit input state) index⟩

def action (state : State input) : Action input :=
  match state.phase with
  | .entering => .retain
  | .accounting =>
      match originalItem? input state with
      | some original => sourceAction input original
      | none => .retain

def next (state : State input) : State input where
  cycle := match state.phase with
    | .entering => state.cycle
    | .accounting => if state.position < capacity input state then state.cycle else state.cycle + 1
  position := match state.phase with
    | .entering => state.position
    | .accounting => if state.position < capacity input state then state.position + 1 else 0
  ahead := match state.phase with
    | .entering => state.ahead + 1
    | .accounting => if state.position = 0 then state.ahead - 1 else state.ahead
  phase := .accounting
  account := (action input state).next input state.account

def native (state : State input) :
    (process input).Run state.account.current (next input state).account.current :=
  (action input state).native input state.account

theorem next_position_bounded (state : State input) (bounded : state.position ≤ capacity input state) :
    (next input state).position ≤ capacity input (next input state) := by
  cases phase : state.phase with
  | entering => simpa only [next, phase, capacity, originalVisit] using bounded
  | accounting =>
      by_cases available : state.position < capacity input state
      · have position : (next input state).position = state.position + 1 := by
          simp only [next, phase, if_pos available]
        have cycle : (next input state).cycle = state.cycle := by
          simp only [next, phase, if_pos available]
        have sameCapacity : capacity input (next input state) = capacity input state := by
          unfold capacity originalVisit
          rw [cycle]
        rw [position, sameCapacity]
        exact Nat.succ_le_of_lt available
      · simp only [next, phase, if_neg available]
        exact Nat.zero_le _

theorem entry_has_one_actual_body (state : State input) (entry : state.phase = .entering) :
    physicalVisitIndex input (next input state) = physicalVisitIndex input state + 1 := by
  unfold physicalVisitIndex
  simp only [next, entry]
  omega

theorem physical_index_advances_once (state : State input) (first : state.position = 0) (fresh : state.ahead = 0) :
    physicalVisitIndex input (next input state) = physicalVisitIndex input state + 1 := by
  cases phase : state.phase with
  | entering =>
      simp [next, physicalVisitIndex, first, fresh, phase]
      omega
  | accounting =>
      have positive := capacity_positive input state
      simp [next, physicalVisitIndex, first, fresh, phase, positive]

theorem pending_body_is_not_executed_again (state : State input) (first : state.position = 0)
    (already : 0 < state.ahead) (accounting : state.phase = .accounting) :
    physicalVisitIndex input (next input state) = physicalVisitIndex input state := by
  have positive := capacity_positive input state
  simp [physicalVisitIndex, next, accounting, first, positive]
  omega

theorem bookkeeping_keeps_physical_visit (state : State input) (later : state.position ≠ 0)
    (accounting : state.phase = .accounting) :
    physicalVisitIndex input (next input state) = physicalVisitIndex input state := by
  by_cases available : state.position < capacity input state
  · simp [next, physicalVisitIndex, later, available, accounting]
  · simp [next, physicalVisitIndex, later, available, accounting]
    omega

theorem exhausted_cursor_keeps_account (state : State input) (done : capacity input state ≤ state.position) :
    (next input state).account = state.account := by
  have absent : originalItem? input state = none := List.getElem?_eq_none done
  cases phase : state.phase <;>
    simp only [next, action, phase, absent, Action.next]

theorem completed_word_reads_next_original_visit (state : State input) (done : capacity input state ≤ state.position)
    (accounting : state.phase = .accounting) :
    (next input state).cycle = state.cycle + 1 ∧ (next input state).position = 0 := by
  simp only [next, accounting, if_neg (Nat.not_lt.mpr done), and_self]

def currentPending (state : State input) : List (InstructionOrigin input) :=
  (inventoryAt input (originalVisit input state)).drop state.position

def queuedCount (state : State input) : Nat := state.ahead - if state.position = 0 then 1 else 0

def pending (state : State input) : List (InstructionOrigin input) :=
  currentPending input state ++ (List.range (queuedCount input state)).flatMap (fun offset =>
    inventoryAt input (ProgrammeHistory.visitAt input (state.cycle + offset + 1)))

structure Rejection (origin : InstructionOrigin input) where
  private mk ::
  instruction : ExecutionItem Party Good Port Technology Instrument
  original : origin.instruction? input = some instruction
  refused : ¬ input.law.Valid instruction.before instruction.request

def rejection? (origin : InstructionOrigin input) : Option (Rejection input origin) := by
  cases original : origin.instruction? input with
  | none => exact none
  | some instruction =>
      by_cases accepted : input.law.Valid instruction.before instruction.request
      · exact none
      · exact some ⟨instruction, original, accepted⟩

structure PendingAt (origin : InstructionOrigin input) where
  issue : IssueReadout input origin
  movement : Option (Movement input origin)
  rejection : Option (Rejection input origin)

def pendingAt (origin : InstructionOrigin input) : PendingAt input origin :=
  ⟨readIssue input origin, readMovement input origin, rejection? input origin⟩

/-- This is a dependent source read of the original pending rows, not an
additional account or a receipt registry. -/
def PendingInventory (state : State input) :=
  (origin : { item : InstructionOrigin input // item ∈ pending input state }) →
    PendingAt input origin.val

def pendingInventory (state : State input) : PendingInventory input state :=
  fun original => pendingAt input original.val

def pendingBaseRow (state : State input) (origin : InstructionOrigin input) :
    OpenResponsibilityAt (ProgrammeSource.N input)
      (ProgrammeSource.supportAt input (physicalVisit input state).current) :=
  ProgrammeSource.sourceEntry input (physicalVisit input state).current origin.item.1

theorem current_item_has_original_source (state : State input) (original : InstructionOrigin input)
    (present : originalItem? input state = some original) :
    original.visit = originalVisit input state := by
  have member := List.mem_of_getElem? present
  change original ∈ inventoryAt input (originalVisit input state) at member
  cases emission : input.emission? with
  | none =>
      simp only [inventoryAt, emission, administrativeInventoryAt] at member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      rfl
  | some emit =>
      simp only [inventoryAt, emission, List.mem_append] at member
      rcases member with administrative | traced
      · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp administrative
        rfl
      · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp traced
        rfl

theorem cursor_zero_exposes_all_original_items (state : State input) (first : state.position = 0) :
    inventoryAt input (originalVisit input state) <+: pending input state := by
  simp only [pending, currentPending, first, List.drop_zero]
  exact List.prefix_append _ _

theorem queued_body_already_occurred (state : State input) (offset : Nat)
    (present : offset < queuedCount input state) :
    state.cycle + offset + 1 < physicalVisitIndex input state := by
  unfold queuedCount at present
  unfold physicalVisitIndex
  split_ifs at * <;> omega

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor
