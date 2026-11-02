import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Movement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem supported_movement_quota_exhausted {origin : InstructionOrigin input}
    (movement : Movement input origin) (state : (process input).GeneratedState)
    (within : movement.quantity ≤ ledgerClaims input state.current
      movement.instrument movement.debtor movement.sender) :
    (allocate input origin state movement.quantity (movement.quantity_nonnegative input)).remaining = 0 := by
  rw [allocate_remaining input origin movement.quantity (movement_source_quantity input movement),
    movement_full_capacity input movement]
  exact max_eq_right (sub_nonpos.mpr within)

theorem supported_movement_preserves_uncovered_claims {origin : InstructionOrigin input}
    (movement : Movement input origin) (state : (process input).GeneratedState)
    (within : movement.quantity ≤ ledgerClaims input state.current
      movement.instrument movement.debtor movement.sender) (instrument : Instrument) (debtor creditor : Party) :
    (input.law.step movement.instruction.before movement.instruction.request).claims instrument debtor creditor -
      ledgerClaims input (allocate input origin state movement.quantity
        (movement.quantity_nonnegative input)).after.current instrument debtor creditor =
    movement.instruction.before.claims instrument debtor creditor -
      ledgerClaims input state.current instrument debtor creditor := by
  have effects := allocateFrom_ledgerClaims input movement state.current.slots.length 0 state
    movement.quantity (movement.quantity_nonnegative input) instrument debtor creditor
  have consumed : (allocate input origin state movement.quantity
      (movement.quantity_nonnegative input)).used input = movement.quantity := by
    rw [Allocation.used, supported_movement_quota_exhausted input movement state within, sub_zero]
  change ledgerClaims input (allocate input origin state movement.quantity
    (movement.quantity_nonnegative input)).after.current instrument debtor creditor = _ at effects
  dsimp only [allocate] at consumed
  rw [effects, consumed, input.law.step_financial_balance,
    input.law.accepted_delta _ _ movement.accepted, movementDelta_actual]
  ring

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
