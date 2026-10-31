import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Generated
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Prefix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- A cursor is the original native fold at its exact processed prefix.
The physical visit may already be ahead; pending rows retain that difference. -/
def PrefixAligned (state : State input) : Prop :=
  state.position ≤ capacity input state ∧
    state.account = consumeOrigins input
      ((inventoryAt input (originalVisit input state)).take state.position)
      (accountAt input state.cycle)

private theorem consumeOrigins_append (left right : List (InstructionOrigin input))
    (state : (process input).GeneratedState) :
    consumeOrigins input (left ++ right) state =
      consumeOrigins input right (consumeOrigins input left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons head tail ih => exact ih _

private theorem inventory_length (state : State input) :
    (inventoryAt input (originalVisit input state)).length = capacity input state := rfl

theorem initial_prefix_aligned : PrefixAligned input (initial input) := by
  exact ⟨Nat.zero_le _, rfl⟩

theorem entering_prefix_aligned (physical : Nat) : PrefixAligned input (enteringAt input physical) := by
  exact ⟨Nat.zero_le _, rfl⟩

theorem next_prefix_aligned (state : State input) (aligned : PrefixAligned input state) :
    PrefixAligned input (next input state) := by
  refine ⟨next_position_bounded input state aligned.1, ?_⟩
  cases phase : state.phase with
  | entering =>
      simpa only [next, action, phase, Action.next, originalVisit] using aligned.2
  | accounting =>
      by_cases available : state.position < capacity input state
      · let original := (inventoryAt input (originalVisit input state))[state.position]'available
        have present : originalItem? input state = some original :=
          List.getElem?_eq_getElem available
        have step := sourceAction_is_actual_consumer input original state.account
        simp only [next, action, phase, present, if_pos available]
        rw [step, aligned.2]
        change (consume input original
          (consumeOrigins input ((inventoryAt input (originalVisit input state)).take state.position)
            (accountAt input state.cycle))).next input =
          consumeOrigins input ((inventoryAt input (originalVisit input state)).take (state.position + 1))
            (accountAt input state.cycle)
        rw [List.take_succ_eq_append_getElem available,
          consumeOrigins_append, consumeOrigins, consumeOrigins]
      · have done : state.position = capacity input state := Nat.le_antisymm aligned.1 (Nat.le_of_not_gt available)
        simp only [next, phase, if_neg available, List.take_zero, consumeOrigins]
        change (next input state).account = accountAt input (state.cycle + 1)
        rw [exhausted_cursor_keeps_account input state (Nat.le_of_not_gt available),
          aligned.2, done]
        rw [← inventory_length input state, List.take_length, accountAt_successor]
        rfl

theorem current_instruction_claims_match
    (initialZero : input.initial.claims = fun _ _ _ => 0)
    (state : State input) (aligned : PrefixAligned input state)
    (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (present : originalItem? input state = some origin)
    (original : origin.instruction? input = some instruction) :
    BalanceConservation.ledgerClaims input state.account.current = instruction.before.claims := by
  have position : (inventoryAt input (originalVisit input state))[state.position]? = some origin := present
  rw [aligned.2]
  exact BalanceConservation.prefix_claims_before_original input
    (inventoryAt input (originalVisit input state)) (accountAt input state.cycle)
    (ProgrammeSource.rawCurrent input (originalVisit input state).current) 0
    (ProgrammeSource.rawEvent input (originalVisit input state).current)
    (inventoryAt_instructions_exact input (originalVisit input state))
    (BalanceConservation.generated_prefix_claims input initialZero state.cycle)
    state.position origin instruction position original

theorem current_movement_quota_exhausted
    (initialZero : input.initial.claims = fun _ _ _ => 0)
    (state : State input) (aligned : PrefixAligned input state)
    (origin : InstructionOrigin input) (movement : Movement input origin)
    (present : originalItem? input state = some origin) :
    (allocate input origin state.account movement.quantity
      (movement.quantity_nonnegative input)).remaining = 0 :=
  BalanceConservation.matched_movement_quota_exhausted input movement state.account
    (current_instruction_claims_match input initialZero state aligned origin movement.instruction
      present movement.original)

#print axioms next_prefix_aligned
#print axioms current_instruction_claims_match
#print axioms current_movement_quota_exhausted

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Cursor
