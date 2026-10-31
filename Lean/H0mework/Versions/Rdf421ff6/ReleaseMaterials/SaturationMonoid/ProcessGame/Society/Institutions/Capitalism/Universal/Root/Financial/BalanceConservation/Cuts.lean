import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Generated

/-! Continuation starts at the actual generated ledger of the selected
historical cut, including every outstanding original claim. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def fromActualCut (start depth : Nat) : (process input).Run
    (accountAt input start).current (accountAt input (start + depth)).current := by
  induction depth with
  | zero => exact .nil
  | succ depth ih =>
      exact ih.concatRuns (process input)
        (consumeOrigins_run input (inventoryAt input (ProgrammeHistory.visitAt input (start + depth)))
          (accountAt input (start + depth)))

theorem cut_preserves_all_original_claims (start depth : Nat) :
    (accountAt input start).current.slots.map (slotClaim input) <+:
      (accountAt input (start + depth)).current.slots.map (slotClaim input) := by
  induction depth with
  | zero => exact List.prefix_rfl
  | succ depth ih => exact ih.trans (every_original_debt_is_retained input (start + depth))

theorem cut_keeps_history (start depth : Nat) :
    (accountAt input start).current.history <+: (accountAt input (start + depth)).current.history := by
  rw [(fromActualCut input start depth).history_eq]
  exact List.prefix_append _ _

theorem continuation_at_every_actual_cut
    (initialZero : input.initial.claims = fun _ _ _ => 0) (start depth : Nat) :
    ledgerClaims input (accountAt input (start + depth)).current =
        (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (start + depth)).current).claims ∧
      (accountAt input start).current.slots.map (slotClaim input) <+:
        (accountAt input (start + depth)).current.slots.map (slotClaim input) ∧
      (accountAt input start).current.history <+: (accountAt input (start + depth)).current.history :=
  ⟨generated_prefix_claims input initialZero _, cut_preserves_all_original_claims input start depth,
    cut_keeps_history input start depth⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
