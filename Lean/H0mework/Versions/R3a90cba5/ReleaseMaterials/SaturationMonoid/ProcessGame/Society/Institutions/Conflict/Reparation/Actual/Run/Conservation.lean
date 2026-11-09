import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.History
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "History" => Script Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)

def paidAt (good : Good) (past : History) (input : Proposal) : ℚ :=
  let prior := run seed community past
  (atInput past input (posted prior input).stack.balances).assignedForGood good

def paidThrough (good : Good) (history : History) : ℚ :=
  List.reverseRecOn (motive := fun _ => ℚ) history 0
    (fun past input paid => paid + paidAt seed community good past input)

def signedThrough (good : Good) (history : History) : ℚ :=
  List.reverseRecOn (motive := fun _ => ℚ) history 0
    (fun past input signed => signed + inputQuantity (seed := seed) past input good)

def damageThrough (good : Good) (history : History) : ℚ :=
  ((originalLosses seed community history).map fun origin =>
    if origin.key.2.2 = good then origin.quantity else 0).sum

theorem no_actual_history_overdraws_the_signed_material (good : Good) (history : History) :
    paidThrough seed community good history ≤ signedThrough seed good history := by
  induction history using List.reverseRecOn with
  | nil => rw [paidThrough, signedThrough, List.reverseRecOn_nil, List.reverseRecOn_nil]
  | append_singleton past input prior =>
    have localBound := an_input_cannot_overdraw_any_good past input
      (posted (run seed community past) input).stack.balances good
    simp only [paidThrough, signedThrough, List.reverseRecOn_concat]
    exact add_le_add prior localBound

theorem the_original_whole_ledger_conserves_each_material_good (good : Good) (history : History) :
    outstandingForGood good (run seed community history).stack.balances +
      paidThrough seed community good history = damageThrough seed community good history := by
  induction history using List.reverseRecOn with
  | nil =>
    rw [run_nil, paidThrough, List.reverseRecOn_nil, damageThrough, originalLosses, List.reverseRecOn_nil]
    change (0 : ℚ) + 0 = 0
    exact zero_add 0
  | append_singleton past input prior =>
    let earlier := run seed community past
    let receipt := atInput past input (posted earlier input).stack.balances
    have written : (advance earlier input).stack.balances = receipt.result :=
      (the_same_input_carries_its_whole_write_and_cannot_reuse_a_receipt earlier input good).2.1
    have exactMass := receipt.outstanding_and_assigned_eq_before good
    have postedMass : outstandingForGood good (posted earlier input).stack.balances =
        outstandingForGood good earlier.stack.balances +
        ((openings seed community past input).map fun origin =>
          if origin.key.2.2 = good then origin.quantity else 0).sum := by
      rw [posted_balances]
      simp only [outstandingWhere, List.map_append, List.sum_append, List.map_map, Function.comp_def, opening]
    rw [run_snoc, written, paidThrough, List.reverseRecOn_concat, damageThrough, losses_snoc,
      List.map_append, List.sum_append]
    change outstandingForGood good receipt.result +
        (paidThrough seed community good past + receipt.assignedForGood good) =
      damageThrough seed community good past +
        ((openings seed community past input).map fun origin =>
          if origin.key.2.2 = good then origin.quantity else 0).sum
    linarith only [prior, exactMass, postedMass]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
