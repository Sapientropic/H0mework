import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveryInventory

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InventoryBirthBudget
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)

def relieved (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => relieved start count + CompletedInventory.closedOld bound inputs (start + count)
def arrivals (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => arrivals start count + CompletedInventory.openBorn bound inputs (start + count)
def productive (start : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => productive start count + if 0 < CompletedInventory.closedOld bound inputs (start + count) then 1 else 0

theorem the_complete_source_window_has_exact_birth_disposition_and_residual_balance (start count : Nat) :
    CompletedInventory.pending bound inputs (start + count) + relieved bound inputs start count =
      CompletedInventory.pending bound inputs start + arrivals bound inputs start count := by
  induction count with
  | zero => simp only [Nat.add_zero, relieved, arrivals]
  | succ count ih =>
    have step := CompletedInventory.every_completed_cut_has_exact_source_birth_and_disposition_balance bound inputs (start + count)
    simp only [Nat.add_succ, Nat.add_zero] at step
    simp only [Nat.add_succ, relieved, arrivals]
    omega

theorem productive_actual_visits_are_paid_from_actual_old_dispositions (start count : Nat) :
    productive bound inputs start count ≤ relieved bound inputs start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [productive, relieved]
    split <;> omega

theorem every_actual_window_has_a_source_generated_productive_visit_budget (start count : Nat) :
    productive bound inputs start count ≤
      CompletedInventory.pending bound inputs start + arrivals bound inputs start count := by
  have paid := productive_actual_visits_are_paid_from_actual_old_dispositions bound inputs start count
  have balance := the_complete_source_window_has_exact_birth_disposition_and_residual_balance bound inputs start count
  omega

theorem already_terminal_newborns_cannot_refill_the_actual_visit_budget (start count : Nat)
    (noneOpen : arrivals bound inputs start count = 0) :
    productive bound inputs start count ≤ CompletedInventory.pending bound inputs start := by
  have budget := every_actual_window_has_a_source_generated_productive_visit_budget bound inputs start count
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InventoryBirthBudget
