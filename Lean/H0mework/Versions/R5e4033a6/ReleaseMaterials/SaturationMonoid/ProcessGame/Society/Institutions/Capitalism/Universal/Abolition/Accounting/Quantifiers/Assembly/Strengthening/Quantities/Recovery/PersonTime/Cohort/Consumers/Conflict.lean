import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Budget
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Consumers.ConflictSource

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Consumers

open Abolition.Root Abolition.Root.Registered
open Quantities.Consumers (lifeSource)
open Innovation.Contribution.Pricing.Consumers.Actual (the_repair_really_funds_both_original_lives)
open ConflictSource
open scoped BigOperators

noncomputable section

local notation "Script" => List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

def foodShortage (repair : Script) (person : Bool) : ℚ :=
  max 0 (shortage lifeSource exposure repair person true)

theorem each_original_persons_food_shortage_can_separately_be_zero (person : Bool) :
    ∃ repair, Recorded lifeSource (exposure ++ repair) ∧ foodShortage repair person = 0 := by
  cases person
  · refine ⟨move 1, record lifeSource _, ?_⟩
    unfold foodShortage shortage
    rw [the_repair_really_funds_both_original_lives.1, (a_paid_move_changes_the_original_food_addresses 1
      (by decide) le_rfl).1, sub_self, max_self]
  · refine ⟨[], record lifeSource _, ?_⟩
    unfold foodShortage shortage
    rw [List.append_nil, the_repair_really_funds_both_original_lives.2.1,
      exposure_has_one_actual_food_unit true]
    norm_num

private theorem original_food_sum_bound (repair : Script) :
    (Execution.endAt lifeSource (exposure ++ repair)).raw.stock false true +
      (Execution.endAt lifeSource (exposure ++ repair)).raw.stock true true ≤ 1 := by
  have conserved := Conservation.unproduced_original_stock_never_increases_in_any_continuation
    (Execution.endAt lifeSource exposure) true no_installed_technique_outputs_food repair
  rw [← Execution.endAt_append] at conserved
  have all : (Finset.univ : Finset Bool) = {false, true} := by decide
  simpa [Conservation.stock, all, exposure_has_one_actual_food_unit] using conserved

theorem every_same_root_repair_leaves_at_least_half_a_unit_at_a_named_original_address
    (repair : Script) :
    ∃ (person : Bool) (loss : Loss lifeSource exposure repair), loss.address = (person, true) ∧
      1 / 2 ≤ foodShortage repair person ∧ Recorded lifeSource (exposure ++ repair) := by
  have total : 1 ≤ shortage lifeSource exposure repair false true + shortage lifeSource exposure repair true true := by
    unfold shortage
    rw [the_repair_really_funds_both_original_lives.1, the_repair_really_funds_both_original_lives.2.1]
    linarith only [original_food_sum_bound repair]
  have named : ∃ person, 1 / 2 ≤ shortage lifeSource exposure repair person true := by
    by_cases first : 1 / 2 ≤ shortage lifeSource exposure repair false true
    · exact ⟨false, first⟩
    · exact ⟨true, by linarith only [total, lt_of_not_ge first]⟩
  obtain ⟨person, lower⟩ := named
  have positive : 0 < shortage lifeSource exposure repair person true :=
    (by norm_num : (0 : ℚ) < 1 / 2).trans_le lower
  obtain ⟨loss, exactAddress, original⟩ := a_positive_shortage_preserves_the_original_named_residual
    lifeSource exposure repair person true positive
  exact ⟨person, loss, exactAddress, lower.trans (le_max_right _ _), original⟩

theorem the_original_shared_food_loss_attains_its_exact_simultaneous_half_unit_floor :
    ∃ repair, Recorded lifeSource (exposure ++ repair) ∧
      foodShortage repair false = 1 / 2 ∧ foodShortage repair true = 1 / 2 := by
  obtain ⟨left, right⟩ := a_paid_move_changes_the_original_food_addresses (1 / 2) (by norm_num) (by norm_num)
  refine ⟨move (1 / 2), record lifeSource _, ?_, ?_⟩
  · unfold foodShortage shortage
    rw [left, the_repair_really_funds_both_original_lives.1]
    norm_num
  · unfold foodShortage shortage
    rw [right, the_repair_really_funds_both_original_lives.2.1]
    norm_num

/-- The two individually achievable zero shortfalls cannot be combined.
Every candidate remains visible to the same joint recovery consumer. -/
theorem the_original_shared_food_conflict_blocks_every_cohort_budget
    (meter : Meter.{0} lifeSource) (limit : Address lifeSource meter exposure → EReal) :
    ∀ repair, Recorded lifeSource (exposure ++ repair) ∧
      Nonempty (BudgetIssue lifeSource meter exposure limit repair) := by
  cases decideBudget lifeSource meter exposure limit with
  | blocked failures => exact failures
  | paid repair paid _ =>
    obtain ⟨_, loss, _, _, _⟩ := every_same_root_repair_leaves_at_least_half_a_unit_at_a_named_original_address repair
    exact (not_lt_of_ge (paid.restored loss.address.1 loss.address.2) loss.unpaid).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Cohort.Consumers
