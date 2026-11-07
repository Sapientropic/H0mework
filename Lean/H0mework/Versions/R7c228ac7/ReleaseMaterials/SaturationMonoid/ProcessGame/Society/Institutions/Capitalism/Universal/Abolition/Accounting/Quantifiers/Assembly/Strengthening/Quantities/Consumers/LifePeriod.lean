import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeSettlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Innovation.Contribution.Pricing.Consumers.Actual (lifeWord source_ready source_review
  source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair
  each_original_test_word_really_passes_the_complete_period_checks
  every_original_person_keeps_actual_standing)

noncomputable section

def lifePeriod := [some (Compile.RawInput.execute lifeWord)]

theorem checked_living_period : Execution.PeriodChecks lifeSource lifeWord := by
  let n := lifeSource.native
  let input := Public.Scope.checkInput n.input
  let members := Public.Scope.scope n.input n.depth n.count n.prefixLimit n.renewalLimit
    n.oldPast n.actual.snapshot lifeWord
  change Review.Guarded.Checks input (Actual.origin n.input n.depth n.count) lifeSource.raw members lifeWord
  have floor := (Demand.primitive_covers_iff_original_floor lifeTrace).mp
    the_two_actual_life_payments_write_the_original_ledger.paid
  have paid : Material.PeriodChecks input lifeSource.raw lifeSource.members lifeWord :=
    each_original_test_word_really_passes_the_complete_period_checks lifeWord List.mem_cons_self
  refine ⟨by decide +kernel, ?_, paid.1, ?_, paid.2.2.1, ?_, paid.2.2.2.2⟩
  · intro cell listed
    obtain ⟨bearer, _, actual⟩ := List.mem_flatMap.mp listed
    exact floor cell (List.mem_flatMap.mpr ⟨bearer, every_original_person_keeps_actual_standing bearer, actual⟩)
  · intro bearer _
    exact paid.2.1 bearer (every_original_person_keeps_actual_standing bearer)
  · intro bearer _
    exact paid.2.2.2.1 bearer (every_original_person_keeps_actual_standing bearer)

theorem the_original_life_period_pays_its_actual_material_body :
    (Execution.endAt lifeSource lifePeriod).raw =
      (Physical.Public.interpreter lifeSource.native.input).next lifeSource.raw lifeWord :=
  Execution.a_checked_period_has_the_original_real_effect lifeSource lifeWord source_ready source_review checked_living_period

theorem the_original_period_advances_one_actual_hour : elapsed lifeSource lifePeriod = 1 := by
  unfold elapsed
  rw [the_original_life_period_pays_its_actual_material_body]
  change lifeSource.raw.clock + max 0 ((Physical.Public.interpreter lifeSource.native.input).duration lifeSource.raw) -
    lifeSource.raw.clock = 1
  have duration : (Physical.Public.interpreter lifeSource.native.input).duration lifeSource.raw = 1 := by
    rw [source_input_is_the_original_registered_input]
    rfl
  rw [duration, max_eq_right (show (0 : ℚ) ≤ 1 by decide)]
  ring

theorem the_original_period_uses_the_actual_food_stock :
    (Execution.endAt lifeSource lifePeriod).raw.stock false true = 0 := by
  rw [the_original_life_period_pays_its_actual_material_body, source_input_is_the_original_registered_input,
    the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
