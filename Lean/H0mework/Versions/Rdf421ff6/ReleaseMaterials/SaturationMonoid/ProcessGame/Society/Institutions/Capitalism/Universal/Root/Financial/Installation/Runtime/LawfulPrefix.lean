import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.CursorRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.PrefixInvariant

/-! A registered historical prefix is not the complete physical balance.
The source recursion keeps its exact original prefix and its remaining
instructions; actual payments never allocate an unsupported claim. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem cursorAt_prefix_aligned (depth count : Nat) : Cursor.PrefixAligned input (cursorAt input depth count) := by
  induction count with
  | zero =>
      exact Cursor.next_prefix_aligned input (Ingress.start input depth)
        (Cursor.entering_prefix_aligned input (depth + 1))
  | succ count prior => exact Cursor.next_prefix_aligned input _ prior

theorem frames_prefix_aligned (depth count : Nat) :
    Cursor.PrefixAligned input ((frames input depth count).cursor input) := by
  rw [frames_cursor]
  exact cursorAt_prefix_aligned input depth count

theorem every_current_instruction_has_its_original_balance
    (initialZero : input.initial.claims = fun _ _ _ => 0) (depth count : Nat)
    (origin : InstructionOrigin input)
    (instruction : Source.Program.ExecutionItem Party Good Port Technology Instrument)
    (present : Cursor.originalItem? input ((frames input depth count).cursor input) = some origin)
    (original : origin.instruction? input = some instruction) :
    BalanceConservation.ledgerClaims input ((frames input depth count).cursor input).account.current =
      instruction.before.claims :=
  Cursor.current_instruction_claims_match input initialZero _ (frames_prefix_aligned input depth count)
    origin instruction present original

theorem every_actual_movement_exhausts_only_its_source_quota
    (initialZero : input.initial.claims = fun _ _ _ => 0) (depth count : Nat)
    (origin : InstructionOrigin input) (movement : Movement input origin)
    (present : Cursor.originalItem? input ((frames input depth count).cursor input) = some origin) :
    (allocate input origin ((frames input depth count).cursor input).account movement.quantity
      (movement.quantity_nonnegative input)).remaining = 0 :=
  Cursor.current_movement_quota_exhausted input initialZero _ (frames_prefix_aligned input depth count)
    origin movement present

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
