import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.NativeBirth
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.NativeSame
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Receipts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next query endAt_append)
open Allocation
open Transport (native_step_has_no_material_items)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {past : Script Party Good Port Technology Instrument}
  (state : State seed community past) (input : Input Party Good Port Technology Instrument)

local notation "oldCut" => endAt seed past
local notation "newCut" => next (endAt seed past) input

/-- Only the actual dispatcher chooses between the original material,
accounting, and registration writes. -/
def posted : StateAt seed community newCut :=
  match Transport.inspect (query (oldCut) input) with
  | .material ready => sameNext state input (.inl ready)
  | .accounting _ absent => sameNext state input (.inr absent)
  | .registration work registered selected => financeNext state input work registered selected

theorem posted_balances :
    (posted state input).stack.balances = state.stack.balances ++
      (openings seed community past input).map (fun origin => (origin, opening origin)) := by
  unfold posted
  split
  · exact same_next_keeps_the_original_balances_and_opens_every_loss _ _ _
  · exact same_next_keeps_the_original_balances_and_opens_every_loss _ _ _
  · rename_i work registered selected _
    rw [financeNext_balances _ _ work selected]
    have empty := Boundary.Actual.no_material_write_has_no_damage (oldCut) input community
      (native_step_has_no_material_items input work)
    simp only [openings, empty, List.map_nil, List.append_nil]

def advance : State seed community (past ++ [input]) :=
  ((writtenReceipts past input (posted state input)).val).rebase
    (endAt_append seed past [input]).symm

theorem written_balances :
    (advance state input).stack.balances =
      (atInput past input (state.stack.balances ++
        (openings seed community past input).map (fun origin => (origin, opening origin)))).result := by
  calc
    _ = (writtenReceipts past input (posted state input)).val.stack.balances :=
      StateAt.rebase_balances (cut := newCut) _ _
    _ = _ := by rw [(writtenReceipts past input (posted state input)).property, posted_balances]

theorem each_input_keeps_its_old_claims_and_files_exactly_its_new_damage :
    (advance state input).stack.balances.map Prod.fst =
      state.stack.balances.map Prod.fst ++ openings seed community past input := by
  rw [written_balances, ItemWrites.same_original_rows]
  rw [List.map_append, List.map_map]
  change _ ++ (openings seed community past input).map id = _
  rw [List.map_id]

theorem the_same_input_carries_its_whole_write_and_cannot_reuse_a_receipt (good : Good) :
    let trace := atInput past input (posted state input).stack.balances
    Quantities.Recorded (oldCut) [input] ∧
    (advance state input).stack.balances = trace.result ∧
    trace.assignedForGood good ≤ inputQuantity (seed := seed) past input good ∧
    (itemPositions (seed := seed) past input).Nodup := by
  refine ⟨Quantities.record (oldCut) [input], ?_⟩
  obtain ⟨written, bounded, distinct⟩ :=
    the_generated_receipts_do_not_overdraw_any_original_good past input (posted state input) good
  exact ⟨(StateAt.rebase_balances (cut := newCut) _ _).trans written, bounded, distinct⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
