import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Family.Cost

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

abbrev Code := Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit)

def improve (code : Code) := programme (indexFor (Cost.value fullReading input before code - 1))

theorem every_completed_original_programme_has_a_source_generated_strict_improvement
    (code : Code) (cleared : RawCleared code) :
    RawCleared (improve code) ∧ Cost.value fullReading input before (improve code) < Cost.value fullReading input before code := by
  have lower := all_complete_programmes_exceed_the_floor_in_the_full_source_readout code cleared
  refine ⟨each_candidate_actually_clears_the_complete_original_debt _,?_⟩
  have approximate := generated_index_improves_any_positive_gap (Cost.value fullReading input before code - 1) (by linarith)
  unfold improve
  rw [(the_candidates_pay_the_same_actual_positive_maintenance_and_efficient_input _).2]
  linarith

theorem arbitrary_precision_is_realized_by_an_actual_complete_source_programme
    (tolerance : ℚ) (positive : 0 < tolerance) :
    RawCleared (programme (indexFor tolerance)) ∧
      1 < Cost.value fullReading input before (programme (indexFor tolerance)) ∧
      Cost.value fullReading input before (programme (indexFor tolerance)) < 1 + tolerance := by
  refine ⟨each_candidate_actually_clears_the_complete_original_debt _,?_,?_⟩
  · rw [(the_candidates_pay_the_same_actual_positive_maintenance_and_efficient_input _).2]
    linarith [epsilon_positive (indexFor tolerance)]
  · rw [(the_candidates_pay_the_same_actual_positive_maintenance_and_efficient_input _).2]
    linarith [generated_index_improves_any_positive_gap tolerance positive]

theorem no_complete_original_source_programme_minimizes_the_full_positive_readout :
    ¬ ∃ code : Code,RawCleared code ∧ ∀ rival : Code,RawCleared rival →
      Cost.value fullReading input before code ≤ Cost.value fullReading input before rival := by
  rintro ⟨code,cleared,least⟩
  have better := every_completed_original_programme_has_a_source_generated_strict_improvement code cleared
  exact (not_lt_of_ge (least (improve code) better.1)) better.2

theorem the_whole_actual_living_and_maintenance_prefix_has_its_original_full_cost :
    Cost.value fullReading input genesis initialHistory = 2 := by decide +kernel

theorem every_complete_suffix_keeps_the_same_actual_prefix_and_exceeds_its_full_floor
    (code : Code) (cleared : RawCleared code) :
    3 < Cost.value fullReading input genesis (initialHistory ++ code) := by
  rw [full_value_of_an_original_prefix_and_suffix,the_whole_actual_living_and_maintenance_prefix_has_its_original_full_cost]
  have lower := all_complete_programmes_exceed_the_floor_in_the_full_source_readout code cleared
  change 3 < 2 + Cost.value fullReading input before code
  linarith

theorem the_real_complete_history_has_cost_arbitrarily_close_to_its_unattained_floor (n : Nat) :
    Cost.value fullReading input genesis (initialHistory ++ programme n) = 3 + epsilon n := by
  rw [full_value_of_an_original_prefix_and_suffix,the_whole_actual_living_and_maintenance_prefix_has_its_original_full_cost]
  change 2 + Cost.value fullReading input before (programme n) = _
  rw [(the_candidates_pay_the_same_actual_positive_maintenance_and_efficient_input n).2]
  ring

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
