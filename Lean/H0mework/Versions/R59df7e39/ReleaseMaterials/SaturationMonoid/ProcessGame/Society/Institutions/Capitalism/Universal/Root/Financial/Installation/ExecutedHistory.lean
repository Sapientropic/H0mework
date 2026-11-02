import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Base

/-! The source phase distinguishes a newly executed word from bookkeeping.
The latter may read the last completed occurrence and its pending rows,
but never treats the next physical word as already executed. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem fresh_physical_index (state : State input) (fresh : FreshBody input state) :
    physicalVisitIndex input (next input state) = physicalVisitIndex input state + 1 := by
  rcases fresh with entering | ready
  · exact entry_has_one_actual_body input state entering
  · exact physical_index_advances_once input state ready.1 ready.2

theorem bookkeeping_physical_index (state : State input) (old : ¬ FreshBody input state) :
    physicalVisitIndex input (next input state) = physicalVisitIndex input state := by
  have accounting : state.phase = .accounting := by
    cases phase : state.phase with
    | entering => exact (old (Or.inl phase)).elim
    | accounting => rfl
  by_cases first : state.position = 0
  · exact pending_body_is_not_executed_again input state first
      (Nat.pos_of_ne_zero (fun zero => old (Or.inr ⟨first, zero⟩))) accounting
  · exact bookkeeping_keeps_physical_visit input state first accounting

theorem original_cycle_has_occurred_after_tick (state : State input) :
    state.cycle < physicalVisitIndex input (next input state) := by
  have positive := capacity_positive input state
  cases phase : state.phase with
  | entering => simp only [physicalVisitIndex, next, phase]; omega
  | accounting =>
      by_cases first : state.position = 0
      · simp [physicalVisitIndex, next, phase, first, positive]
        omega
      · by_cases available : state.position < capacity input state
        · simp only [physicalVisitIndex, next, phase, if_pos available, if_neg first]
          simp
          omega
        · simp only [physicalVisitIndex, next, phase, if_neg available, if_neg first, if_true]
          omega

def currentExecutedBody? (state : State input) :
    Option (RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot) :=
  if FreshBody input state then some (physicalVisit input state) else none

def lastExecutedIndex (state : State input) : Nat :=
  physicalVisitIndex input (next input state) - 1

def lastExecutedVisit (state : State input) :=
  ProgrammeHistory.visitAt input (lastExecutedIndex input state)

theorem fresh_reads_this_actual_body (state : State input) (fresh : FreshBody input state) :
    currentExecutedBody? input state = some (physicalVisit input state) ∧
      lastExecutedVisit input state = physicalVisit input state := by
  refine ⟨if_pos fresh, ?_⟩
  simp only [lastExecutedVisit, lastExecutedIndex, fresh_physical_index input state fresh,
    Nat.add_sub_cancel, physicalVisit]

theorem bookkeeping_reads_only_completed_body (state : State input) (old : ¬ FreshBody input state) :
    currentExecutedBody? input state = none ∧
      lastExecutedVisit input state =
        ProgrammeHistory.visitAt input (physicalVisitIndex input state - 1) := by
  exact ⟨if_neg old, congrArg (ProgrammeHistory.visitAt input)
    (congrArg (fun n => n - 1) (bookkeeping_physical_index input state old))⟩

theorem last_body_is_strictly_completed (state : State input) :
    lastExecutedIndex input state < physicalVisitIndex input (next input state) := by
  have positive := original_cycle_has_occurred_after_tick input state
  unfold lastExecutedIndex
  omega

/-- This reads the complete raw target of the original last execution,
including on ticks that merely account for already executed instructions. -/
theorem last_execution_returns_actual_physical_current (state : State input) :
    input.law.next
      (ProgrammeSource.rawCurrent input (lastExecutedVisit input state).current)
      (ProgrammeSource.rawEvent input (lastExecutedVisit input state).current) =
      ProgrammeSource.rawCurrent input (physicalVisit input (next input state)).current := by
  have positive := original_cycle_has_occurred_after_tick input state
  have successor : lastExecutedIndex input state + 1 = physicalVisitIndex input (next input state) := by
    unfold lastExecutedIndex
    omega
  rw [physicalVisit, ← successor]
  exact (ProgrammeSource.actual_raw_next input (lastExecutedVisit input state).current).symm

omit [DecidableEq Port] in
private theorem inventory_member_original_visit
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (origin : InstructionOrigin input) (member : origin ∈ inventoryAt input visit) : origin.visit = visit := by
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

theorem pending_origin_has_actually_occurred (state : State input) (origin : InstructionOrigin input)
    (member : origin ∈ pending input state) :
    ∃ index < physicalVisitIndex input (next input state),
      origin.visit = ProgrammeHistory.visitAt input index := by
  rcases List.mem_append.mp member with current | queued
  · exact ⟨state.cycle, original_cycle_has_occurred_after_tick input state,
      inventory_member_original_visit input (originalVisit input state) origin
        (List.mem_of_mem_drop current)⟩
  · obtain ⟨offset, included, original⟩ := List.mem_flatMap.mp queued
    refine ⟨state.cycle + offset + 1,
      (queued_body_already_occurred input state offset (List.mem_range.mp included)).trans_le
        (physical_index_monotone input state), ?_⟩
    exact inventory_member_original_visit input _ origin original

theorem bookkeeping_pending_was_already_occurred (state : State input)
    (old : ¬ FreshBody input state) (origin : InstructionOrigin input)
    (member : origin ∈ pending input state) :
    ∃ index < physicalVisitIndex input state,
      origin.visit = ProgrammeHistory.visitAt input index := by
  simpa only [bookkeeping_physical_index input state old] using
    pending_origin_has_actually_occurred input state origin member

#print axioms last_execution_returns_actual_physical_current
#print axioms bookkeeping_pending_was_already_occurred

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor
