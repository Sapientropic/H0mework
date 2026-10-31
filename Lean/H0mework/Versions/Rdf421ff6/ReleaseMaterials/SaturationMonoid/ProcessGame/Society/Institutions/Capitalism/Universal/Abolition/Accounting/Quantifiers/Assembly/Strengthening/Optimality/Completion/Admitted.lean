import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion

open Countermodels.Nonattainment
noncomputable section

/-- A stricter completion test cannot acquire a minimum by accepting all
the actual full-clearing family. This is a diagnostic, not an admission producer. -/
theorem every_admitted_candidate_has_a_strictly_cheaper_admitted_source_alternative
    (admitted : Code → Prop)
    (clears : ∀ code, admitted code → RawCleared code)
    (family : ∀ n, admitted (programme n))
    (code : Code) (accepted : admitted code) :
    admitted (improve code) ∧
      Cost.value fullReading input before (improve code) < Cost.value fullReading input before code :=
  ⟨family _,(every_completed_original_programme_has_a_source_generated_strict_improvement code (clears code accepted)).2⟩

theorem no_stricter_admission_containing_the_actual_clearing_family_has_a_minimum
    (admitted : Code → Prop)
    (clears : ∀ code, admitted code → RawCleared code)
    (family : ∀ n, admitted (programme n)) :
    ¬ ∃ code : Code, admitted code ∧ ∀ rival : Code, admitted rival →
      Cost.value fullReading input before code ≤ Cost.value fullReading input before rival := by
  rintro ⟨code,accepted,least⟩
  have better := every_admitted_candidate_has_a_strictly_cheaper_admitted_source_alternative admitted clears family code accepted
  exact (not_lt_of_ge (least (improve code) better.1)) better.2

attribute [local irreducible] Cost.value

theorem the_strict_improvement_keeps_the_complete_original_historical_cost
    (admitted : Code → Prop)
    (clears : ∀ code, admitted code → RawCleared code)
    (family : ∀ n, admitted (programme n))
    (code : Code) (accepted : admitted code) :
    admitted (improve code) ∧
      Cost.value fullReading input genesis (initialHistory ++ improve code) <
        Cost.value fullReading input genesis (initialHistory ++ code) := by
  have better := every_admitted_candidate_has_a_strictly_cheaper_admitted_source_alternative admitted clears family code accepted
  refine ⟨better.1,?_⟩
  rw [full_value_of_an_original_prefix_and_suffix genesis initialHistory (improve code),
    full_value_of_an_original_prefix_and_suffix genesis initialHistory code,
    the_whole_actual_living_and_maintenance_prefix_has_its_original_full_cost]
  simpa only [before,add_comm] using (_root_.add_lt_add_left better.2 (2 : ℚ))

theorem no_admitted_full_history_attains_the_complete_social_cost_infimum
    (admitted : Code → Prop)
    (clears : ∀ code, admitted code → RawCleared code)
    (family : ∀ n, admitted (programme n)) :
    ¬ ∃ code : Code, admitted code ∧ ∀ rival : Code, admitted rival →
      Cost.value fullReading input genesis (initialHistory ++ code) ≤
        Cost.value fullReading input genesis (initialHistory ++ rival) := by
  rintro ⟨code,accepted,least⟩
  have better := the_strict_improvement_keeps_the_complete_original_historical_cost admitted clears family code accepted
  exact (not_lt_of_ge (least (improve code) better.1)) better.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion
