import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Validation

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit

def originalMethod : PaidMethod := ((frameAt 5).method).get (by decide +kernel)

theorem original_method_is_kept (later : Nat) :
    (frameAt (5 + later)).method = some originalMethod := by
  induction later with
  | zero => exact (Option.some_get _).symm
  | succ later ih => exact method_is_kept (5 + later) originalMethod ih

private theorem cache_at_four_is_empty : (frameAt 4).method = none := by
  apply Option.isNone_iff_eq_none.mp
  decide +kernel

private theorem original_method_generated : compile (frameAt 4).raw = some originalMethod := by
  have paid := original_method_is_kept 0
  change (frameAt 4).method.orElse (fun _ => compile (frameAt 4).raw) = some originalMethod at paid
  rw [cache_at_four_is_empty] at paid
  exact paid

private theorem first_ready : Cell.Ready (frameAt 4).raw := by decide +kernel

private theorem word_at_four : wordAt 4 (frameAt 4) = seedChild 1 := by
  have round := machine_round 4
  simp only [wordAt, show ¬(4 : Nat) = 0 by decide, show ¬(4 : Nat) = 1 by decide, ↓reduceIte,
    respond, round, show ¬(4 : Nat) = 7 by decide, Response.word, Feedback.respond,
    show (4 : Nat) ≤ 10 by decide, Feedback.Outcome.word, Cell.respond, dif_pos first_ready, Cell.Response.word]
  simp [Cell.candidate, round]

theorem actual_paid_method_origin :
    originalMethod.before = source.currentAt 4 ∧
      originalMethod.word = (source.actualExecution 3).submitted ∧
      originalMethod.item ∈ (source.actualExecution 3).interpreted.items ∧
      flowAt (law.actualDebit originalMethod.item.before originalMethod.item.request) 0 .labor = 1 := by
  have origin := compile_origin _ originalMethod original_method_generated
  refine ⟨?_, ?_, ?_, originalMethod.actual_labor_payment⟩
  · rw [current_is_generated_machine]; exact origin.1
  · rw [actual_execution_word, word_at_four]; exact originalMethod.schema
  · change originalMethod.item ∈ law.rawItems (source.currentAt 4) (source.actualExecution 3).submitted
    rw [current_is_generated_machine, actual_execution_word, word_at_four, origin.2]
    exact List.mem_cons_self

private theorem second_ready : Ready (frameAt 7).raw originalMethod := by
  unfold Ready
  rw [originalMethod.plan_is_parameterized_original]
  decide +kernel

private theorem word_at_seven : wordAt 7 (frameAt 7) = originalMethod.plan 2 := by
  simp only [wordAt, show ¬(7 : Nat) = 0 by decide, show ¬(7 : Nat) = 1 by decide, ↓reduceIte,
    respond, machine_round, original_method_is_kept 2, dif_pos second_ready, Response.word]

theorem actual_reuse_consumes_the_original_paid_programme :
    (source.actualExecution 6).submitted = originalMethod.plan 2 ∧
      (source.actualExecution 6).submitted = seedWord 2 ∧
      ∀ item ∈ (source.actualExecution 6).interpreted.items, law.Valid item.before item.request := by
  have word : (source.actualExecution 6).submitted = originalMethod.plan 2 := by
    rw [actual_execution_word, word_at_seven]
  refine ⟨word, word.trans (originalMethod.plan_is_parameterized_original 2), ?_⟩
  change ∀ item ∈ law.rawItems (source.currentAt 7) (source.actualExecution 6).submitted, _
  rw [current_is_generated_machine, word]
  exact second_ready

theorem finite_inventory_difference : ∀ actor : Fin 6, ∀ good : Good,
    (frameAt 11).raw.stock actor good = (Cell.source.frameAt 11).raw.stock actor good +
      if actor.val = 0 ∧ good = .labor then 1 else 0 := by
  decide +kernel

/-- The comparison covers every address and every physical unit. -/
theorem complete_inventory_difference (actor : Party) (good : Good) :
    (source.currentAt 11).stock actor good = (Cell.source.currentAt 11).stock actor good +
      if actor = 0 ∧ good = .labor then 1 else 0 := by
  by_cases inside : actor < 6
  · rw [current_is_generated_machine, Cell.raw_current_frame]
    exact finite_inventory_difference ⟨actor, inside⟩ good
  · have outside : 6 ≤ actor := Nat.le_of_not_gt inside
    rw [raw_current_frame, Cell.raw_current_frame]
    have left := outside_inventory_zero true actor outside good
    have right := outside_inventory_zero false actor outside good
    change (source.frameAt 11).raw.stock actor good = 0 at left
    change (Cell.source.frameAt 11).raw.stock actor good = 0 at right
    rw [left, right, if_neg (by rintro ⟨zero, _⟩; subst actor; norm_num at outside)]
    norm_num

theorem all_physical_goods_except_saved_labor_are_identical (actor : Party) (good : Good)
    (different : actor ≠ 0 ∨ good ≠ .labor) :
    (source.currentAt 11).stock actor good = (Cell.source.currentAt 11).stock actor good := by
  rw [complete_inventory_difference, if_neg (by tauto), add_zero]

theorem complete_credits_equal (actor : Party) (good : Good) :
    law.totalCredit (receipts source 11) actor good = law.totalCredit (receipts Cell.source 11) actor good := by
  by_cases inside : actor < 6
  · have finite : ∀ address : Fin 6, ∀ unit : Good,
        law.totalCredit (receipts source 11) address unit = law.totalCredit (receipts Cell.source 11) address unit := by
      rw [receipts_are_the_generated_machine]
      decide +kernel
    exact finite ⟨actor, inside⟩ good
  · have outside : 6 ≤ actor := Nat.le_of_not_gt inside
    exact (outside_totals_zero true actor outside good).2.trans
      (outside_totals_zero false actor outside good).2.symm

/-- Every cost is included, including the loan, research and all audits.
Only one already-paid audit is reused; no output credit changes. -/
theorem complete_debit_difference (actor : Party) (good : Good) :
    law.totalDebit (receipts source 11) actor good + (if actor = 0 ∧ good = .labor then 1 else 0) =
      law.totalDebit (receipts Cell.source 11) actor good := by
  have left := receipt_balance source 11 actor good
  have right := receipt_balance Cell.source 11 actor good
  change (source.frameAt 11).raw.stock actor good + law.totalDebit (receipts source 11) actor good =
    initial.stock actor good + law.totalCredit (receipts source 11) actor good at left
  change (Cell.source.frameAt 11).raw.stock actor good + law.totalDebit (receipts Cell.source 11) actor good =
    initial.stock actor good + law.totalCredit (receipts Cell.source 11) actor good at right
  rw [← raw_current_frame, complete_inventory_difference, complete_credits_equal] at left
  rw [← Cell.raw_current_frame] at right
  linarith

def laborDividend : ℚ := law.totalDebit (receipts Cell.source 11) 0 .labor -
  law.totalDebit (receipts source 11) 0 .labor

theorem exact_strict_labor_dividend : laborDividend = 1 ∧ 0 < laborDividend := by
  have balance := complete_debit_difference 0 .labor
  simp only [true_and, ↓reduceIte] at balance
  dsimp only [laborDividend]
  constructor <;> linarith

theorem same_all_financial_positions :
    (source.currentAt 11).claims = (Cell.source.currentAt 11).claims := by
  funext instrument debtor holder
  exact (Finance.all_claims_are_zero true instrument debtor holder).trans
    (Finance.all_claims_are_zero false instrument debtor holder).symm

theorem same_technology_and_window :
    (source.currentAt 11).technology = (Cell.source.currentAt 11).technology ∧
      (source.currentAt 11).clock = (Cell.source.currentAt 11).clock ∧
      (source.currentAt 11).round = (Cell.source.currentAt 11).round := by
  rw [current_is_generated_machine, Cell.raw_current_frame]
  decide +kernel

theorem same_actual_research_and_loan_settlement :
    (source.currentAt 3).technology = (true, false) ∧
      (source.currentAt 5).technology = (true, false) ∧
      (source.currentAt 6).technology = (true, true) ∧
      (source.currentAt 2).claims () 0 2 = 1 ∧ (source.currentAt 4).claims () 0 2 = 0 ∧
      (source.currentAt 5).stock 1 .feed - (source.currentAt 6).stock 1 .feed = 1 ∧
      (source.currentAt 5).stock 1 .energy - (source.currentAt 6).stock 1 .energy = 1 ∧
      (source.currentAt 5).stock 1 .labor - (source.currentAt 6).stock 1 .labor = 1 := by
  simp only [current_is_generated_machine]
  decide +kernel

theorem both_children_and_grandchildren_have_actual_first_production :
    (source.currentAt 7).stock 1 .seed = 3 ∧ (source.currentAt 9).stock 2 .seed = 3 ∧
      (source.currentAt 10).stock 4 .seed = 3 ∧ (source.currentAt 11).stock 5 .seed = 3 ∧
      (∀ child ∈ ([1, 2, 4, 5] : List Party),
        1 ≤ (source.currentAt 11).stock child .life ∧ 1 ≤ (source.currentAt 11).stock child .spare) := by
  simp only [current_is_generated_machine]
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
