import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Consumers.Joint.Opening
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Consumers.Split
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Protection

set_option autoImplicit false
set_option maxRecDepth 8192

open private original_body_is_single item_exact from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Consumers.Source

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (primitiveScript endAt)
open Reparation.Consumers (warCut receipt)
open Conflict.Consumers.Evolving (R W compact sourceInput)
open Allocation
open Allocation.Consumers

noncomputable section

private theorem body_signer (earlier : W) (request : R)
    (whole : Conflict.Root.Paid warCut (earlier ++ [request])) :
    (originalItem warCut (primitiveScript earlier) (bodyInput request) (bodyPosition earlier request whole)).request.signer =
      request.signer := by
  have item := List.getElem_of_eq (original_body_is_single earlier request whole) (bodyPosition earlier request whole).isLt
  exact congrArg (fun item : Item => item.request.signer) item

private theorem the_levy_pays_no_row_of_the_original_victim (earlier : W) (request : R)
    (whole : Conflict.Root.Paid warCut (earlier ++ [request])) (signed : request.signer = true)
    (rows : List Row) (oldVictims : ∀ row ∈ rows, row.1.key.1 = false) :
    (atItem warCut (primitiveScript earlier) (bodyInput request) (bodyPosition earlier request whole) rows).changes.result =
      rows := by
  let plan := atItem warCut (primitiveScript earlier) (bodyInput request) (bodyPosition earlier request whole) rows
  have keep := Changes.kept_without_the_original_victim_signatures _ _ _ plan.changes plan.original (by
    intro row listed
    rw [body_signer earlier request whole, signed, oldVictims row listed]
    decide)
  exact (congrArg Changes.result keep).trans (Changes.unchanged_result _)

private theorem first_opening :
    openings warCut id (primitiveScript beforeFirst) (bodyInput (levyOf 2)) = [firstOrigin] :=
  a_single_transfer_files_exactly_its_one_damage beforeFirst (levyOf 2) firstPaid
    false true false 2 rfl firstOrigin.damage rfl

private theorem second_opening :
    openings warCut id (primitiveScript beforeSecond) (bodyInput (levyOf 4)) = [secondOrigin] :=
  a_single_transfer_files_exactly_its_one_damage beforeSecond (levyOf 4) secondPaid
    false true false 4 rfl secondOrigin.damage rfl

theorem the_first_levy_files_its_original_two :
    (run warCut id (primitiveScript beforeSecond)).stack.balances = [older] := by
  change (run warCut id (primitiveScript (beforeFirst ++ [levyOf 2]))).stack.balances = _
  rw [the_two_original_ticks_write_the_generated_balances beforeFirst (levyOf 2) firstPaid,
    the_front_installs_no_aggression_row, first_opening]
  exact the_levy_pays_no_row_of_the_original_victim beforeFirst (levyOf 2) firstPaid rfl [older]
    (by intro row present; rw [List.mem_singleton.mp present]; rfl)

theorem the_second_levy_keeps_two_and_files_four :
    (run warCut id (primitiveScript beforeReceipt)).stack.balances = oldRows := by
  change (run warCut id (primitiveScript (beforeSecond ++ [levyOf 4]))).stack.balances = _
  rw [the_two_original_ticks_write_the_generated_balances beforeSecond (levyOf 4) secondPaid,
    the_first_levy_files_its_original_two, second_opening]
  exact the_levy_pays_no_row_of_the_original_victim beforeSecond (levyOf 4) secondPaid rfl oldRows (by
    intro row present
    simp only [oldRows, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with first | second
    · rw [first]; rfl
    · rw [second]; rfl)

abbrev reverseKey : Key Bool Bool := (true, false, false)

private theorem reverse_loss :
    loss (Boundary.Actual.materialLaw (endAt warCut (primitiveScript beforeReceipt))) id
      (originalItem warCut (primitiveScript beforeReceipt) (bodyInput (receipt 3)) receiptPosition) reverseKey = 3 := by
  rw [item_exact beforeReceipt (receipt 3) secondPaid paid]
  change loss (Physical.Public.interpreter (Conflict.Root.terminal warCut beforeReceipt).native.input) id _ _ = _
  rw [secondPaid.whole.sameInput, sourceInput]
  decide +kernel

def reverseOrigin : Occurrence warCut id :=
  ⟨primitiveScript beforeReceipt, bodyInput (receipt 3), ⟨(receiptPosition, reverseKey),
    by
      change 0 < loss (Boundary.Actual.materialLaw (endAt warCut (primitiveScript beforeReceipt))) id
        (originalItem warCut (primitiveScript beforeReceipt) (bodyInput (receipt 3)) receiptPosition) reverseKey
      rw [reverse_loss]
      decide⟩⟩

theorem the_receipt_also_opens_its_actual_reverse_three : reverseOrigin.quantity = 3 := reverse_loss

abbrev reverseRow := (reverseOrigin, opening reverseOrigin)

private theorem receipt_opening :
    openings warCut id (primitiveScript beforeReceipt) (bodyInput (receipt 3)) = [reverseOrigin] :=
  a_single_transfer_files_exactly_its_one_damage beforeReceipt (receipt 3) paid
    true false false 3 rfl reverseOrigin.damage rfl

private theorem joint_receipt_result :
    (atItem warCut (primitiveScript beforeReceipt) (bodyInput (receipt 3)) receiptPosition
      (oldRows ++ [reverseRow])).changes.result = splitPlan.changes.result ++ [reverseRow] := by
  let larger := atItem warCut (primitiveScript beforeReceipt) (bodyInput (receipt 3)) receiptPosition (oldRows ++ [reverseRow])
  let parts := Changes.split oldRows [reverseRow] larger.changes
  let rest := scan offer splitPlan.remainder [reverseRow]
  have decomposed : parts.1 = splitPlan.changes ∧ parts.2 = rest.changes :=
    let exact := scan_splits_at_the_original_prefix offer (Capacity.full offer) oldRows [reverseRow]
    ⟨exact.1, exact.2.1⟩
  have noPay := Changes.kept_without_the_original_victim_signatures _ _ _ rest.changes rest.original (by
    intro row present
    rw [List.mem_singleton.mp present, body_signer beforeReceipt (receipt 3) paid]
    decide)
  calc
    larger.changes.result = (parts.1.append parts.2).result :=
      congrArg Changes.result (Changes.append_split oldRows [reverseRow] larger.changes).symm
    _ = splitPlan.changes.result ++ [reverseRow] := by
      rw [Changes.result_append, decomposed.1, decomposed.2, noPay, Changes.unchanged_result]

/-- This is the original canonical run after the receipt and its native write.
The new reverse debit has its own row and keeps its own amount. -/
theorem canonical_receipt_writes_both_old_rows_and_the_reverse_row :
    (run warCut id script).stack.balances = splitPlan.changes.result ++ [reverseRow] := by
  change (run warCut id (primitiveScript (beforeReceipt ++ [receipt 3]))).stack.balances = _
  rw [the_two_original_ticks_write_the_generated_balances beforeReceipt (receipt 3) paid,
    the_second_levy_keeps_two_and_files_four, receipt_opening]
  exact joint_receipt_result

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint
