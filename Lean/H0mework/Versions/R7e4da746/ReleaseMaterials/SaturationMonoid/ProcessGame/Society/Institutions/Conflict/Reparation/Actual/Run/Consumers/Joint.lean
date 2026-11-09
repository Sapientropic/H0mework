import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Consumers.Joint.Balances
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Conservation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Disposition

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (primitiveScript)
open Reparation.Consumers (warCut)
open Allocation
open Allocation.Consumers
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

def reached : State warCut (id : Bool → Bool) script := (publish warCut id script).next

def reachedBalances : List Row := reached.stack.balances
def paidOlder : Row := (firstOrigin, olderMove.after)
def paidYounger : Row := (secondOrigin, youngerMove.after)
def reachedRows : List Row := [paidOlder, paidYounger, reverseRow]

def ReachedRow := OpenResponsibilityAt reached.world reached.resident.support
def readsReparation (row : ReachedRow) (balance : Row) : Prop := reached.read row = .inr balance

private theorem original_split_rows :
    splitPlan.changes.result = [(firstOrigin, olderMove.after), (secondOrigin, youngerMove.after)] := by
  change splitPlan.changes.result =
    [(firstOrigin, splitPlan.changes.head.after),
      (secondOrigin, (Changes.split [older] [younger] splitPlan.changes).2.head.after)]
  generalize computed : splitPlan.changes = changes
  cases changes with
  | cons first remaining =>
    cases remaining with
    | cons second tail => cases tail; rfl

theorem the_published_successor_has_the_three_literal_rows :
    reachedBalances = reachedRows := by
  change (run warCut id script).stack.balances = _
  rw [canonical_receipt_writes_both_old_rows_and_the_reverse_row, original_split_rows]
  rfl

theorem the_published_successor_reads_both_old_balances_and_the_reverse_balance :
    ∃ first second reverse : ReachedRow,
      readsReparation first paidOlder ∧ paidOlder.2.remaining = 0 ∧
      readsReparation second paidYounger ∧ paidYounger.2.remaining = 3 ∧
      readsReparation reverse reverseRow ∧ reverseRow.2.remaining = 3 := by
  obtain ⟨first, readFirst⟩ := reached.every_balance_is_a_row_of_the_current paidOlder (by
    change paidOlder ∈ reachedBalances
    rw [the_published_successor_has_the_three_literal_rows]
    exact List.mem_cons_self)
  obtain ⟨second, readSecond⟩ := reached.every_balance_is_a_row_of_the_current paidYounger (by
    change paidYounger ∈ reachedBalances
    rw [the_published_successor_has_the_three_literal_rows]
    exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨reverse, readReverse⟩ := reached.every_balance_is_a_row_of_the_current reverseRow (by
    change reverseRow ∈ reachedBalances
    rw [the_published_successor_has_the_three_literal_rows]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact ⟨first, second, reverse, readFirst, the_original_two_rows_end_at_zero_and_three.1, readSecond,
    the_original_two_rows_end_at_zero_and_three.2, readReverse, the_receipt_also_opens_its_actual_reverse_three⟩

private theorem the_fixture_preserves_original_authority : SourceAuthority warCut script := by
  intro item member
  change item ∈ Quantities.Execution.inventory warCut (primitiveScript word) at member
  rw [Quantities.Execution.primitive_inventory paid.trace 0] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact paid.authorized original present

def PublishedSettled : Prop := ∃ checked proof, (publish warCut id script).result = .settled checked proof

theorem the_original_program_is_published_in_the_settled_branch : PublishedSettled := by
  change ∃ checked proof, approval warCut script = .settled checked proof
  unfold approval
  cases inspected : Capitalism.Universal.Abolition.Material.inspectList
      (fun item => warCut.native.input.law.Valid item.before item.request)
      (Quantities.Execution.inventory warCut script) with
  | failure item original unlicensed =>
    exact (unlicensed (the_fixture_preserves_original_authority item original)).elim
  | clear checked =>
    cases decided : Quantities.decideAt warCut script with
    | blocked obstruction => exact (obstruction.refutes paid.whole.toFeasible).elim
    | feasible proof => exact ⟨checked, Quantities.settle warCut script proof, rfl⟩

def reachedPaid (good : Bool) : ℚ := paidThrough warCut id good script
def reachedSigned (good : Bool) : ℚ := signedThrough warCut good script

theorem the_canonical_run_spends_three_with_every_good_bounded :
    reachedPaid false = 3 ∧ ∀ good, reachedPaid good ≤ reachedSigned good := by
  have whole := the_original_whole_ledger_conserves_each_material_good warCut id false script
  have named : originalLosses warCut id script = [firstOrigin, secondOrigin, reverseOrigin] := by
    rw [← the_live_ledger_contains_exactly_the_original_losses]
    change reachedBalances.map Prod.fst = _
    rw [the_published_successor_has_the_three_literal_rows]
    rfl
  have amounts := the_original_two_rows_end_at_zero_and_three
  have remaining : outstandingForGood false (run warCut id script).stack.balances = 6 := by
    change outstandingForGood false reachedBalances = 6
    rw [the_published_successor_has_the_three_literal_rows]
    have first : firstOrigin.key.2.2 = false := rfl
    have second : secondOrigin.key.2.2 = false := rfl
    have reverse : reverseOrigin.key.2.2 = false := rfl
    simp only [reachedRows, paidOlder, paidYounger, outstandingWhere, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_pos first,
      if_pos second, if_pos reverse, add_zero, reverseRow, opening,
      the_receipt_also_opens_its_actual_reverse_three]
    exact (congrArg₂ (fun first second : ℚ => first + (second + 3)) amounts.1 amounts.2).trans
      (by decide +kernel)
  have losses : damageThrough warCut id false script = 9 := by
    unfold damageThrough
    rw [named]
    have first : firstOrigin.key.2.2 = false := rfl
    have second : secondOrigin.key.2.2 = false := rfl
    have reverse : reverseOrigin.key.2.2 = false := rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_pos first, if_pos second,
      if_pos reverse, first_original_quantity, second_original_quantity, the_receipt_also_opens_its_actual_reverse_three,
      add_zero]
    decide +kernel
  rw [remaining, losses] at whole
  exact ⟨by change paidThrough warCut id false script = 3; linarith, fun good =>
    no_actual_history_overdraws_the_signed_material warCut id good script⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.RunConsumers.Joint
