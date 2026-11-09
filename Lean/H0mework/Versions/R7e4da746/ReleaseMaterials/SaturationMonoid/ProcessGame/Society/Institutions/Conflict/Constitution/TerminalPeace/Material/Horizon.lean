import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Conservation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Period

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (C compact)
open Quantities.Execution
open Quantities.Recovery.PersonTime.Cohort.Conservation (stock)

noncomputable section

/-- Each window is consumed at the successor of the earlier original
windows. An earlier delivery cannot pay a later one. -/
def PaidFoodWindows : C → List Original.Word → Prop
  | _, [] => True
  | cut, window :: later =>
      (∀ bearer : Bool, 1 ≤ Quantities.Demand.delivered cut window bearer .necessity true) ∧
      PaidFoodWindows (endAt cut window) later

/-- Amount actually delivered across disjoint windows of the original
inventory. The two original beneficiaries both remain in the charge. -/
def spentInFoodWindows : C → List Original.Word → ℚ
  | _, [] => 0
  | cut, window :: later =>
      Quantities.Demand.delivered cut window false .necessity true +
        Quantities.Demand.delivered cut window true .necessity true +
        spentInFoodWindows (endAt cut window) later

theorem food_spent_in_any_original_schedule_has_the_inventory_bound (cut : C)
    (same : cut.native.input = compact) (windows : List Original.Word) :
    stock (endAt cut windows.flatten).raw true + spentInFoodWindows cut windows ≤ stock cut.raw true := by
  induction windows generalizing cut with
  | nil => simp [endAt, spentInFoodWindows]
  | cons window later ih =>
    have laterCut : (endAt cut window).native.input = compact := (endAt_input cut window).trans same
    have first := food_is_consumed_in_the_original_ledger cut same window
    have rest := ih _ laterCut
    simp only [List.flatten_cons, endAt_append, spentInFoodWindows]
    linarith only [first, rest]

theorem actual_living_windows_require_two_food_each (cut : C) (windows : List Original.Word)
    (paid : PaidFoodWindows cut windows) :
    2 * (windows.length : ℚ) ≤ spentInFoodWindows cut windows := by
  induction windows generalizing cut with
  | nil => simp [spentInFoodWindows]
  | cons window later ih =>
    have rest := ih _ paid.2
    have left := paid.1 false
    have right := paid.1 true
    simp only [List.length_cons, Nat.cast_succ, spentInFoodWindows]
    linarith only [rest, left, right]

theorem every_original_continuation_pays_at_most_one_living_window (windows : List Original.Word)
    (paid : PaidFoodWindows Original.cut windows) :
    windows.length ≤ 1 := by
  have lower := actual_living_windows_require_two_food_each Original.cut windows paid
  have upper := food_spent_in_any_original_schedule_has_the_inventory_bound Original.cut Original.same_source windows
  have available := food_stock_nonnegative Original.cut windows.flatten the_original_stocks_are_nonnegative
  rw [original_food_opening] at upper
  have lengths : (windows.length : ℚ) ≤ 1 := by linarith only [lower, upper, available]
  exact_mod_cast lengths

theorem the_bound_of_one_is_actually_attained :
    PaidFoodWindows Original.cut [livingPeriod] ∧
      Quantities.Settled Original.cut livingPeriod ∧
      (endAt Original.cut livingPeriod).raw.clock = Original.cut.raw.clock + 1 :=
  ⟨⟨fun bearer => (the_living_period_pays_one_unit_to_each_original_bearer bearer).ge, trivial⟩,
    the_original_cut_pays_one_real_living_period.1, the_living_period_moves_the_original_clock_one⟩

theorem every_original_schedule_has_the_required_food_shortfall (windows : List Original.Word) :
    max 0 (2 * (windows.length : ℚ) - 2) ≤
      max 0 (2 * (windows.length : ℚ) - spentInFoodWindows Original.cut windows) := by
  have source := food_spent_in_any_original_schedule_has_the_inventory_bound Original.cut Original.same_source windows
  have available := food_stock_nonnegative Original.cut windows.flatten the_original_stocks_are_nonnegative
  rw [original_food_opening] at source
  have availableToSpend : spentInFoodWindows Original.cut windows ≤ 2 := by linarith only [source, available]
  exact max_le_max le_rfl (sub_le_sub_left availableToSpend _)

/-- Returns the first underfunded window at its real cut and its original
bearer. All earlier windows have actually paid their two food requirements. -/
theorem an_underfunded_schedule_has_an_original_first_shortage
    (cut : C) (windows : List Original.Word) (failed : ¬ PaidFoodWindows cut windows) :
    ∃ (front : List Original.Word) (window : Original.Word) (later : List Original.Word) (bearer : Bool), windows = front ++ window :: later ∧
      PaidFoodWindows cut front ∧
      Quantities.Demand.delivered (endAt cut front.flatten) window bearer .necessity true < 1 := by
  induction windows generalizing cut with
  | nil => exact (failed trivial).elim
  | cons window later ih =>
    by_cases first : ∀ bearer : Bool, 1 ≤ Quantities.Demand.delivered cut window bearer .necessity true
    · have rejected : ¬ PaidFoodWindows (endAt cut window) later := fun paid => failed ⟨first, paid⟩
      obtain ⟨front, now, tail, bearer, same, funded, shortage⟩ := ih _ rejected
      refine ⟨window :: front, now, tail, bearer, by simp [same], ⟨first, funded⟩, ?_⟩
      simpa only [List.flatten_cons, endAt_append] using shortage
    · obtain ⟨bearer, under⟩ := not_forall.mp first
      exact ⟨[], window, later, bearer, rfl, trivial, lt_of_not_ge under⟩

theorem a_second_living_window_has_a_named_original_shortage (windows : List Original.Word)
    (many : 1 < windows.length) :
    ∃ (front : List Original.Word) (window : Original.Word) (later : List Original.Word) (bearer : Bool), windows = front ++ window :: later ∧
      PaidFoodWindows Original.cut front ∧
      Quantities.Demand.delivered (endAt Original.cut front.flatten) window bearer .necessity true < 1 :=
  an_underfunded_schedule_has_an_original_first_shortage Original.cut windows
    (fun paid => (not_le_of_gt many) (every_original_continuation_pays_at_most_one_living_window windows paid))

theorem no_food_is_delivered_from_an_original_zero_stock_cut (cut : C)
    (same : cut.native.input = compact) (nonnegative : ∀ person good, 0 ≤ cut.raw.stock person good)
    (empty : stock cut.raw true = 0) (suffix : Original.Word) (bearer : Bool) :
    Quantities.Demand.delivered cut suffix bearer .necessity true = 0 := by
  have bound := food_is_consumed_in_the_original_ledger cut same suffix
  have remaining := food_stock_nonnegative cut suffix nonnegative
  have left := original_food_delivery_nonnegative cut suffix false
  have right := original_food_delivery_nonnegative cut suffix true
  rw [empty] at bound
  cases bearer
  · linarith only [bound, remaining, left, right]
  · linarith only [bound, remaining, left, right]

theorem no_original_continuation_after_the_paid_period_can_deliver_either_food
    (suffix : Original.Word) (bearer : Bool) :
    Quantities.Demand.delivered (endAt Original.cut livingPeriod) suffix bearer .necessity true = 0 :=
  no_food_is_delivered_from_an_original_zero_stock_cut (endAt Original.cut livingPeriod)
    ((endAt_input Original.cut livingPeriod).trans Original.same_source)
    (original_stock_stays_nonnegative Original.cut livingPeriod the_original_stocks_are_nonnegative)
    food_is_exhausted_after_the_living_period suffix bearer

#print axioms the_bound_of_one_is_actually_attained
#print axioms a_second_living_window_has_a_named_original_shortage
#print axioms no_original_continuation_after_the_paid_period_can_deliver_either_food

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
