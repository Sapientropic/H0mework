import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Addresses

/-!
An arbitrary material loss is opened by its original dispatcher. The posted
row and the publication after allocation are read from the original states.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community

/-- The literal history ending at this damage's first material write. -/
def history (loss : Loss) : Script Party Good Port Technology Instrument :=
  loss.past ++ [loss.input]

/-- The dispatcher has written the physical input and filed all its damage
addresses, before the receipt positions are allocated. -/
def filed (loss : Loss) : StateAt seed community (Quantities.Execution.next
    (Quantities.Execution.endAt seed loss.past) loss.input) :=
  posted (run seed community loss.past) loss.input

def publication (loss : Loss) : Published seed community (history loss) :=
  publish seed community (history loss)

/-- Start a continuation at the fully published state of the original tick. -/
def originState (loss : Loss) : State seed community (history loss) := (publication loss).next

theorem the_original_address_is_filed (loss : Loss) :
    loss ∈ openings seed community loss.past loss.input := by
  unfold openings
  refine List.mem_map.mpr ⟨loss.damage, Boundary.Actual.every_actual_debit_is_assessed loss.damage, ?_⟩
  cases loss
  rfl

theorem the_original_row_starts_at_the_actual_loss_quantity (loss : Loss) :
    (loss, opening loss) ∈ (filed loss).stack.balances := by
  unfold filed
  rw [posted_balances]
  exact List.mem_append_right _ (List.mem_map_of_mem (the_original_address_is_filed loss))

theorem the_opening_quantity_is_written_in_the_original_ledger (loss : Loss) :
    ∃ row, (filed loss).read row = .inr (loss, opening loss) :=
  (filed loss).every_balance_is_a_row_of_the_current _ (the_original_row_starts_at_the_actual_loss_quantity loss)

theorem origin_in_material_history (loss : Loss) :
    loss ∈ originalLosses seed community (history loss) := by
  rw [history, losses_snoc]
  exact List.mem_append_right _ (the_original_address_is_filed loss)

theorem originState_origins (loss : Loss) :
    (originState loss).stack.balances.map Prod.fst = originalLosses seed community (history loss) :=
  the_live_ledger_contains_exactly_the_original_losses seed community (history loss)

theorem originState_records_the_whole_history (loss : Loss) : Quantities.Recorded seed (history loss) :=
  (publication loss).recorded

#print axioms the_opening_quantity_is_written_in_the_original_ledger

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
