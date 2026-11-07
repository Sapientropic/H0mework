import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.WorkHours
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifePeriod

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Consumers

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource lifePeriod the_original_period_advances_one_actual_hour
  the_original_period_uses_the_actual_food_stock)
open Innovation.Contribution.Pricing.Consumers.Actual (the_repair_really_funds_both_original_lives)

noncomputable section

theorem the_original_hour_leaves_a_real_food_shortage :
    elapsed lifeSource lifePeriod = 1 ∧ Recorded lifeSource lifePeriod ∧
      ∃ loss, inspect lifeSource lifePeriod [] = some loss := by
  refine ⟨the_original_period_advances_one_actual_hour, record lifeSource lifePeriod, ?_⟩
  cases found : inspect lifeSource lifePeriod [] with
  | some loss => exact ⟨loss, rfl⟩
  | none =>
      have funded := (cleared_exactly_when_no_original_actor_loses_stock lifeSource lifePeriod []).mp found false true
      rw [List.append_nil, the_original_period_uses_the_actual_food_stock,
        the_repair_really_funds_both_original_lives.1] at funded
      norm_num at funded

theorem arbitrary_waiting_without_real_debits_or_credits_cannot_restore_the_original_stock
    (repair : List (Option (Abolition.Root.Registered.Compile.RawInput Bool Bool Bool Unit Unit)))
    (silent : Execution.inventory (Execution.endAt lifeSource lifePeriod) repair = []) :
    Recorded lifeSource (lifePeriod ++ repair) ∧ ¬ Restored lifeSource lifePeriod repair := by
  refine ⟨record lifeSource _, ?_⟩
  intro restored
  have absent : (false, true) ∉ Execution.materialAddresses (Execution.endAt lifeSource lifePeriod) repair := by
    simp [Execution.materialAddresses, silent]
  have unchanged := Execution.stock_outside_original_effects_is_unchanged
    (Execution.endAt lifeSource lifePeriod) repair false true absent
  have food := restored false true
  rw [Execution.endAt_append, unchanged, the_original_period_uses_the_actual_food_stock,
    the_repair_really_funds_both_original_lives.1] at food
  norm_num at food

theorem the_original_exposure_consumes_the_full_work_time_contract :
    Bounds.Restriction.Minimum (Execution.endAt lifeSource lifePeriod)
      (inspect lifeSource lifePeriod) (hourRatio lifeSource lifePeriod) := by
  rcases the_original_work_cut_resolves_its_full_recovery_hour_conversion lifeSource lifePeriod with
    ⟨zero, _⟩ | ⟨_, exactCut⟩
  · rw [the_original_period_advances_one_actual_hour] at zero
    norm_num at zero
  · exact exactCut

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Consumers
